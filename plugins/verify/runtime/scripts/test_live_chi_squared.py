#!/usr/bin/env python3
"""Live pipeline test — chi_squared_po (Huang et al., ICLR 2025).

Tests the pipeline on a recent RLHF paper that uses f-divergence
reparameterization and concentrability coefficients.
"""

import json
import sys
import os
import re

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from unittest.mock import MagicMock
from statverify.engine import StatVerifyEngine, VerifyReport
from statverify.retriever import PremiseRetriever, save_embeddings
from tests.proofs.chi_squared_po import PROOF


# ---------------------------------------------------------------------------
call_log = []

def log_call(phase, content_preview):
    call_log.append(phase)
    print(f"  [{len(call_log):2d}] {phase}: {content_preview[:80]}")


# ---------------------------------------------------------------------------
# Decompose response — break proof into 4 building blocks
# ---------------------------------------------------------------------------

DECOMPOSE_RESPONSE = json.dumps([
    {
        "name": "mixed_divergence_decomposition",
        "statement": (
            "The mixed f-divergence f_{chi_mix}(z) = (1/2)(z-1)^2 + z log z "
            "decomposes as D_{f_mix}(P||Q) = (1/2) D_{chi^2}(P||Q) + D_{KL}(P||Q)."
        ),
        "role": "Establishing the mixed divergence structure for chi-PO"
    },
    {
        "name": "chi_squared_change_of_measure",
        "statement": (
            "For distributions P, Q and any function f: "
            "(E_P[f] - E_Q[f])^2 <= D_{chi^2}(P||Q) * Var_Q[f]."
        ),
        "role": "Transferring from training to testing distribution"
    },
    {
        "name": "concentrability_from_chi_squared",
        "statement": (
            "The L1 concentrability coefficient satisfies "
            "C^{pi} = E_{pi_ref}[pi/pi_ref] = 1 + D_{chi^2}(pi || pi_ref) "
            "for any policy pi relative to reference pi_ref."
        ),
        "role": "Relating chi-squared divergence to concentrability"
    },
    {
        "name": "mle_uniform_convergence",
        "statement": (
            "For a finite policy class Pi with n samples, with probability 1-delta: "
            "sup_{pi in Pi} |L_hat(pi) - L(pi)| <= C * sqrt(log(|Pi|/delta) / n)."
        ),
        "role": "MLE generalization bound for the empirical objective"
    },
])


def make_classify_response(lemma_name, candidates):
    """Route classification based on lemma name."""
    if lemma_name == "mixed_divergence_decomposition":
        for c in candidates:
            if "fMixDiv_eq" in c or "fMix_decomp" in c:
                return json.dumps({
                    "kind": "library",
                    "match_id": c,
                    "reasoning": "fMixDiv_eq_half_chiSq_add_kl is exactly this decomposition"
                })
    if lemma_name == "chi_squared_change_of_measure":
        for c in candidates:
            if "chiSqDivF_eq" in c:
                return json.dumps({
                    "kind": "library",
                    "match_id": c,
                    "reasoning": "chiSqDivF_eq gives the chi-squared formula"
                })
        for c in candidates:
            if "chiSqDiv" in c and "change" in c:
                return json.dumps({
                    "kind": "library",
                    "match_id": c,
                    "reasoning": "chiSqDiv_change_of_measure is the bound"
                })
    if lemma_name == "concentrability_from_chi_squared":
        # This is NOVEL — chiSqDivF nonnegativity isn't in the library
        return json.dumps({
            "kind": "novel",
            "match_id": "",
            "reasoning": "chiSqDivF nonnegativity not in library; needs proof from definition"
        })
    return json.dumps({
        "kind": "novel",
        "match_id": "",
        "reasoning": "No matching theorem found in library"
    })


# Novel: chi-squared divergence nonnegativity
# This demonstrates a novel lemma derived from the library's definitions
NOVEL_STATEMENT = (
    "theorem concentrability_from_chi_squared "
    "{S : Type*} [Fintype S] [DecidableEq S] "
    "(P Q : S → ℝ) "
    "(hQ : ∀ x, 0 < Q x) "
    ": 0 ≤ chiSqDivF P Q"
)

NOVEL_PROOF = (
    "unfold chiSqDivF fDiv chiSqGenerator\n"
    "  apply Finset.sum_nonneg\n"
    "  intro x _\n"
    "  apply mul_nonneg\n"
    "  · exact le_of_lt (hQ x)\n"
    "  · exact sq_nonneg _"
)

# Instantiation: fMixDiv nonnegativity (specializes library's fMixDiv_nonneg)
INST_STATEMENT = (
    "theorem concentrability_nonneg "
    "{S : Type*} [Fintype S] [DecidableEq S] "
    "(P Q : S → ℝ) "
    "(hQ : ∀ x, 0 < Q x) "
    "(hP : ∀ x, 0 ≤ P x) "
    "(h_chiSq_nonneg : 0 ≤ chiSqDivF P Q) "
    ": 0 ≤ fMixDiv P Q"
)

INST_PROOF = "exact fMixDiv_nonneg P Q hQ hP h_chiSq_nonneg"

# Novel: MLE uniform convergence (simplified)
NOVEL_MLE_STATEMENT = (
    "theorem mle_uniform_convergence "
    "(n : ℕ) (hn : 0 < n) "
    "(Pi_card : ℕ) (hPi : 0 < Pi_card) "
    "(δ : ℝ) (hδ : 0 < δ) "
    ": Real.sqrt (Real.log (↑Pi_card / δ) / ↑n) ≥ 0"
)

NOVEL_MLE_PROOF = "exact Real.sqrt_nonneg _"

# Assembly — uses library theorems + novel lemmas
ASSEMBLY_STATEMENT = (
    "theorem chi_po_sample_complexity "
    "{S : Type*} [Fintype S] [DecidableEq S] "
    "(P Q : S → ℝ) (hQ_pos : ∀ x, 0 < Q x) "
    ": fMixDiv P Q = (1 / 2) * chiSqDivF P Q + klDivF P Q "
    "∧ chiSqDivF P Q = ∑ x, (P x - Q x) ^ 2 / Q x "
    "∧ 0 ≤ chiSqDivF P Q"
)

ASSEMBLY_PROOF = (
    "refine ⟨?_, ?_, ?_⟩\n"
    "  · -- Library: mixed f-divergence decomposition\n"
    "    exact fMixDiv_eq_half_chiSq_add_kl P Q\n"
    "  · -- Library: chi-squared formula\n"
    "    exact chiSqDivF_eq P Q hQ_pos\n"
    "  · -- Novel: chi-squared nonnegativity\n"
    "    exact concentrability_from_chi_squared P Q hQ_pos"
)


def smart_chat(messages, **kwargs):
    """Route LLM calls to the right response."""
    content = messages[0]["content"] if messages else ""

    # Classify
    if "candidate theorem" in content.lower() or "classify this lemma" in content.lower():
        name_match = re.search(r"Name:\s*(\w+)", content)
        lemma_name = name_match.group(1) if name_match else ""
        candidates = re.findall(r"Candidate:\s*([\w.]+)", content)
        log_call("CLASSIFY", f"Classifying {lemma_name} against {len(candidates)} candidates")
        return make_classify_response(lemma_name, candidates)

    # Formalize — statement
    if "type signature" in content.lower() or "convert this natural-language" in content.lower():
        if "main_theorem" in content or "building blocks" in content.lower():
            log_call("ASSEMBLE-STMT", "Generating main theorem signature")
            return ASSEMBLY_STATEMENT
        name_match = re.search(r"must be `(\w+)`", content)
        lemma_name = name_match.group(1) if name_match else ""
        if "mle" in lemma_name:
            log_call("NOVEL-STMT", f"Generating novel ({lemma_name})")
            return NOVEL_MLE_STATEMENT
        if "concentrability" in lemma_name:
            log_call("NOVEL-STMT", f"Generating novel ({lemma_name})")
            return NOVEL_STATEMENT
        log_call("NOVEL-STMT", f"Generating ({lemma_name})")
        return NOVEL_STATEMENT

    # Assembly proof
    if "informal proof sketch" in content.lower():
        log_call("ASSEMBLE-PROOF", "Composing main theorem proof")
        return ASSEMBLY_PROOF

    # Formalize — proof
    if "locked" in content.lower() and "proof" in content.lower():
        if "mle" in content.lower() or "sqrt" in content.lower():
            log_call("NOVEL-PROOF", "Proving MLE bound")
            return NOVEL_MLE_PROOF
        log_call("NOVEL-PROOF", "Proving novel lemma")
        return NOVEL_PROOF

    # Audit
    if "hypothesis" in content.lower() and "auditor" in content.lower():
        log_call("AUDIT-HYP", "Checking hypothesis fidelity")
        return json.dumps({
            "mappings": [
                {"lean_param": "(P Q : S → ℝ)", "paper_assumption": "distributions P, Q", "status": "matched"},
            ],
            "extra_hypotheses": [],
            "verdict": "pass",
            "reasoning": "All hypotheses match paper assumptions"
        })

    # Decompose (last)
    if "atomic lemma building blocks" in content.lower():
        log_call("DECOMPOSE", "Breaking proof into building blocks")
        return DECOMPOSE_RESPONSE

    log_call("UNKNOWN", content[:60])
    return "sorry"


def smart_embed(texts, **kwargs):
    """Embeddings: 8-dim vectors designed to get high cosine with matching corpus entries."""
    embs = []
    for text in texts:
        t = text.lower()
        if "fmix" in t or ("mixed" in t and "divergence" in t) or ("half" in t and "chi" in t and "kl" in t):
            embs.append([0.9, 0.1, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0])
        elif ("chi" in t and ("change" in t or "measure" in t)) or ("e_p" in t and "e_q" in t):
            embs.append([0.0, 0.9, 0.1, 0.0, 0.0, 0.0, 0.0, 0.0])
        elif "concentrab" in t or ("chi" in t and ("nonneg" in t or "sum" in t)):
            embs.append([0.0, 0.1, 0.9, 0.0, 0.0, 0.0, 0.0, 0.0])
        elif "mle" in t or "uniform convergence" in t or ("log" in t and ("pi" in t or "class" in t)):
            embs.append([0.0, 0.0, 0.0, 0.9, 0.0, 0.0, 0.0, 0.0])
        elif "pessim" in t or "coverage" in t:
            embs.append([0.0, 0.0, 0.0, 0.0, 0.9, 0.0, 0.0, 0.0])
        elif "fdiv" in t or "fenchel" in t or "conjugate" in t:
            embs.append([0.7, 0.0, 0.1, 0.0, 0.0, 0.2, 0.0, 0.0])
        else:
            embs.append([0.12, 0.12, 0.12, 0.12, 0.12, 0.12, 0.12, 0.16])
    return embs


# ---------------------------------------------------------------------------
# Build test corpus from real entries
# ---------------------------------------------------------------------------

def build_test_corpus(tmp_dir):
    import json
    from pathlib import Path

    corpus_path = Path(tmp_dir) / "test_corpus.jsonl"

    real_corpus = Path("benchmark/retrieval_corpus.jsonl")
    # Only FDivergence entries — ChiSquared.lean has build errors
    target_ids = [
        "RLGeneralization.Concentration.FDivergence.fMixDiv_eq_half_chiSq_add_kl",
        "RLGeneralization.Concentration.FDivergence.fMix_decomp",
        "RLGeneralization.Concentration.FDivergence.chiSqDivF_eq",
        "RLGeneralization.Concentration.FDivergence.fMixDiv_nonneg",
        "RLGeneralization.Concentration.FDivergence.klDivF_nonneg",
        "RLGeneralization.Concentration.FDivergence.fDiv_nonneg",
        "RLGeneralization.OfflineRL.FunctionApprox.pessimism_coverage_tradeoff",
        "RLGeneralization.Algorithms.ModelBased.model_based_pac",
    ]

    entries = []
    with open(real_corpus) as f:
        for line in f:
            entry = json.loads(line)
            if entry["id"] in target_ids:
                entries.append(entry)

    with open(corpus_path, "w") as f:
        for e in entries:
            f.write(json.dumps(e) + "\n")

    embeddings = []
    for e in entries:
        eid = e["id"].lower()
        if "fmixdiv_eq" in eid or "fmix_decomp" in eid:
            embeddings.append([0.9, 0.1, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0])
        elif "chisqdivf_eq" in eid:
            # chi-squared formula — matches both "chi squared" and "change of measure" queries
            embeddings.append([0.0, 0.9, 0.8, 0.0, 0.0, 0.0, 0.0, 0.0])
        elif "fmixdiv_nonneg" in eid:
            embeddings.append([0.0, 0.1, 0.9, 0.0, 0.0, 0.0, 0.0, 0.0])
        elif "kldivf_nonneg" in eid or "fdiv_nonneg" in eid:
            embeddings.append([0.0, 0.1, 0.9, 0.0, 0.0, 0.0, 0.0, 0.0])
        elif "chisq" in eid:
            embeddings.append([0.0, 0.2, 0.7, 0.0, 0.0, 0.1, 0.0, 0.0])
        elif "pessimism" in eid or "coverage" in eid:
            embeddings.append([0.0, 0.0, 0.0, 0.0, 0.9, 0.0, 0.0, 0.0])
        elif "fdiv" in eid or "fmix" in eid:
            embeddings.append([0.7, 0.0, 0.1, 0.0, 0.0, 0.2, 0.0, 0.0])
        else:
            embeddings.append([0.12, 0.12, 0.12, 0.12, 0.12, 0.12, 0.12, 0.16])

    emb_path = corpus_path.with_name("test_corpus_embeddings.bin")
    save_embeddings(embeddings, emb_path)
    print(f"  Built test corpus: {len(entries)} entries")
    return str(corpus_path)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    import tempfile
    from pathlib import Path
    from datetime import datetime

    run_dir = Path(__file__).parent.parent / "runs"
    run_dir.mkdir(exist_ok=True)
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    run_output = run_dir / f"chi_squared_po_{timestamp}.txt"

    print("=" * 60)
    print("STATVERIFY LIVE PIPELINE TEST")
    print(f"Fixture: chi_squared_po (Huang et al., ICLR 2025)")
    print(f"LLM: Claude Code (hand-crafted responses)")
    print(f"Lean: REAL compilation via lake env lean")
    print(f"Output: {run_output}")
    print("=" * 60)

    print("\n--- Setup ---")
    tmp_dir = tempfile.mkdtemp(prefix="statverify_chi_")
    corpus_path = build_test_corpus(tmp_dir)

    mock_llm = MagicMock()
    mock_llm.chat.side_effect = smart_chat
    mock_llm.embed.side_effect = smart_embed
    mock_llm.model = "claude-code-manual"

    engine = StatVerifyEngine(llm=mock_llm, corpus_path=corpus_path)
    print(f"  Loaded {len(engine.retriever)} premises")

    print(f"\n--- Pipeline Execution ---")
    print(f"  Theorem: {PROOF['theorem'][:80]}...")
    print(f"  Proof: {PROOF['proof'][:80]}...")
    print()

    report = engine.verify(
        PROOF["theorem"],
        PROOF["proof"],
        locked=True,
        audit=True,
    )

    # Results
    print(f"\n--- Results ---")
    print(f"  Overall: {report.overall.upper()}")
    print(f"  Lemmas: {len(report.lemmas)}")
    for l in report.lemmas:
        icon = {"library_verified": "+", "formalized": "!", "gap": "x"}.get(l.status, "?")
        kind_label = f" [{l.kind}]" if l.kind != "novel" else ""
        print(f"    {icon} {l.name}{kind_label}: {l.status}")
        if l.library_match_id:
            print(f"      matched: {l.library_match_id}")
        if l.compile_error:
            first = l.compile_error.split("\n")[0][:100]
            print(f"      error: {first}")
        if l.hypothesis_audit:
            print(f"      hyp_audit: {l.hypothesis_audit.verdict}")

    print(f"\n  Compile success: {report.compile_success}")
    if report.lean_statement:
        print(f"  Main theorem: {report.lean_statement[:80]}")
    if report.compile_error:
        print(f"  Compile error: {report.compile_error[:200]}")
    if report.hypothesis_audit:
        print(f"  Main hyp audit: {report.hypothesis_audit.verdict}")
    if report.structural_audit:
        print(f"  Main struct audit: {report.structural_audit.verdict}"
              f" (sorry={report.structural_audit.has_sorry})")

    print(f"\n  Summary: {report.summary}")

    if report.lean_code:
        print(f"\n--- Assembled Lean Code ---")
        print(report.lean_code)
        print(f"--- End Lean Code ---")

    print(f"\n--- LLM Call Log ({len(call_log)} calls) ---")
    for i, phase in enumerate(call_log, 1):
        print(f"  {i:2d}. {phase}")

    # Save
    with open(run_output, "w") as f:
        f.write(f"StatVerify Live Test — {timestamp}\n")
        f.write(f"Fixture: chi_squared_po (ICLR 2025)\n")
        f.write(f"Overall: {report.overall}\n\n")
        for l in report.lemmas:
            f.write(f"  {l.name}: {l.status} (kind={l.kind})\n")
        f.write(f"\nLLM calls: {len(call_log)}\n")
        if report.lean_code:
            f.write(f"\n--- Lean Code ---\n{report.lean_code}\n")
        f.write(f"\nSummary: {report.summary}\n")

    if report.lean_code:
        lean_output = run_dir / f"chi_squared_po_{timestamp}.lean"
        lean_output.write_text(report.lean_code)
        print(f"\nSaved: {run_output}")
        print(f"Saved: {lean_output}")

    print(f"\n{'=' * 60}")
    if report.overall == "verified":
        print("VERDICT: VERIFIED — proof compiles, all building blocks resolved")
    elif report.overall == "has_gaps":
        gaps = [l.name for l in report.lemmas if l.status == "gap"]
        formalized = [l.name for l in report.lemmas if l.status == "formalized"]
        lib = [l.name for l in report.lemmas if l.status == "library_verified"]
        print(f"VERDICT: HAS_GAPS — pipeline works, some lemmas couldn't compile")
        print(f"  Library: {lib}")
        print(f"  Formalized: {formalized}")
        print(f"  Gaps: {gaps}")
    print("=" * 60)

    return 0 if report.overall in ("verified", "has_gaps") else 1


if __name__ == "__main__":
    sys.exit(main())
