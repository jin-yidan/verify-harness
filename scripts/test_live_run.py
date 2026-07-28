#!/usr/bin/env python3
"""Manual live pipeline test — Claude Code acts as the LLM.

Runs the full StatVerify pipeline on settling_online_rl_2024 with
hand-crafted LLM responses to test every phase end-to-end.
Lean compilation is REAL (not mocked).
"""

import json
import sys
import os
import re

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from unittest.mock import MagicMock
from statverify.engine import StatVerifyEngine, VerifyReport
from statverify.retriever import PremiseRetriever, save_embeddings
from tests.proofs.settling_online_rl import PROOF


# ---------------------------------------------------------------------------
# Step counter to track which LLM call we're on
# ---------------------------------------------------------------------------
call_log = []

def log_call(phase, content_preview):
    call_log.append(phase)
    print(f"  [{len(call_log):2d}] {phase}: {content_preview[:80]}")


# ---------------------------------------------------------------------------
# Hand-crafted LLM responses — Claude Code acting as the LLM
# ---------------------------------------------------------------------------

DECOMPOSE_RESPONSE = json.dumps([
    {
        "name": "freedman_concentration",
        "statement": (
            "For a martingale difference sequence with conditional variance V "
            "and bounded increments |d_i| <= b, "
            "P(|S_n| >= t) <= 2 exp(-t^2 / (2V + 2bt/3))."
        ),
        "role": "Concentration for Bellman recursion estimation errors"
    },
    {
        "name": "law_of_total_variance",
        "statement": (
            "For random variables X, Y: Var(X) = E[Var(X|Y)] + Var(E[X|Y])."
        ),
        "role": "Bounding cumulative variance sum_h Var[V_{h+1}] <= O(H^2)"
    },
    {
        "name": "optimistic_regret_decomposition",
        "statement": (
            "For an optimistic model-based algorithm with value function "
            "estimates V_hat >= V*, the regret decomposes as "
            "Regret(K) <= sum_{k=1}^K (V_hat_1^k(s_1) - V_1^*(s_1))."
        ),
        "role": "Decomposing regret into per-episode optimism gaps"
    },
    {
        "name": "variance_aware_value_bound",
        "statement": (
            "In a finite-horizon MDP with horizon H, the sum of value "
            "function variances satisfies sum_{h=1}^H Var_{s~d_h}[V_{h+1}(s)] <= H^2."
        ),
        "role": "Bounding total variance across stages via law of total variance"
    },
])


def make_classify_response(lemma_name, candidates):
    """Generate classification response based on lemma name and candidates."""
    if lemma_name == "freedman_concentration":
        for c in candidates:
            if "freedman" in c.lower() or "Freedman" in c:
                return json.dumps({
                    "kind": "library",
                    "match_id": c,
                    "reasoning": "Freedman's inequality is exactly this concentration bound"
                })
    if lemma_name == "law_of_total_variance":
        for c in candidates:
            if "total_variance" in c.lower() or "TotalVariance" in c:
                return json.dumps({
                    "kind": "library",
                    "match_id": c,
                    "reasoning": "Law of total variance is directly available"
                })
    if lemma_name == "variance_aware_value_bound":
        for c in candidates:
            if "total_variance_bound" in c.lower():
                return json.dumps({
                    "kind": "instantiation",
                    "match_id": c,
                    "reasoning": "General total_variance_bound can be instantiated for H-horizon MDP"
                })
        for c in candidates:
            if "variance" in c.lower():
                return json.dumps({
                    "kind": "instantiation",
                    "match_id": c,
                    "reasoning": "Variance bound can be instantiated for H-horizon MDP"
                })
    return json.dumps({
        "kind": "novel",
        "match_id": "",
        "reasoning": "No matching theorem found in library"
    })


# For novel lemma formalization (optimistic_regret_decomposition)
# Real mathematical fact: regret = sum of per-episode optimism gaps ≥ 0
STATEMENT_RESPONSE = (
    "theorem optimistic_regret_decomposition "
    "(K : ℕ) "
    "(V_hat V_star : Fin K → ℝ) "
    "(h_opt : ∀ k, V_hat k ≥ V_star k) "
    ": (∑ k : Fin K, (V_hat k - V_star k)) ≥ 0"
)

PROOF_RESPONSE_NOVEL = (
    "apply Finset.sum_nonneg\n"
    "  intro k _\n"
    "  linarith [h_opt k]"
)

# For instantiation formalization (variance_aware_value_bound)
# Instantiates library's total_variance_bound for H-horizon MDP setting
INST_STATEMENT_RESPONSE = (
    "theorem variance_aware_value_bound "
    "{ι : Type*} (s : Finset ι) "
    "(variance mean : ι → ℝ) "
    "(H : ℝ) (hH : 0 ≤ H) "
    "(h_var_le : ∀ i ∈ s, variance i ≤ H * mean i) "
    "(h_mean_sum : ∑ i ∈ s, mean i ≤ H) "
    ": ∑ i ∈ s, variance i ≤ H ^ 2"
)

INST_PROOF_RESPONSE = (
    "have h := FiniteHorizonMDP.total_variance_bound s variance mean hH h_var_le h_mean_sum\n"
    "  linarith"
)

# Assembly — main theorem references ALL building blocks:
#   - optimistic_regret_decomposition (novel lemma, defined above)
#   - freedman_tail_inversion (library, imported)
#   - law_of_total_variance (library, imported)
# NOTE: cannot use `let x := ...` in the type (engine regex strips `:=`)
ASSEMBLY_STATEMENT_RESPONSE = (
    "theorem main_theorem "
    "{Y : Type*} [Fintype Y] [DecidableEq Y] "
    "(K : ℕ) (hK : 0 < K) "
    "(V_hat V_star : Fin K → ℝ) "
    "(h_opt : ∀ k, V_hat k ≥ V_star k) "
    "(v b δ : ℝ) (hv : 0 ≤ v) (hb : 0 < b) (hδ : 0 < δ) (hδ1 : δ < 1) "
    "(w : Y → ℝ) (μ m₂ : Y → ℝ) "
    "(hw_nonneg : ∀ y, 0 ≤ w y) (hw_sum : ∑ y, w y = 1) "
    ": (∑ k : Fin K, (V_hat k - V_star k)) ≥ 0 "
    "∧ Real.exp (-(√(2 * v * Real.log (1/δ)) + 2*b/3 * Real.log (1/δ))^2 / "
    "(2 * v + 2 * b * (√(2 * v * Real.log (1/δ)) + 2*b/3 * Real.log (1/δ)) / 3)) ≤ δ "
    "∧ (∑ y, w y * m₂ y) - (∑ y, w y * μ y) ^ 2 = "
    "(∑ y, w y * (m₂ y - μ y ^ 2)) + "
    "((∑ y, w y * μ y ^ 2) - (∑ y, w y * μ y) ^ 2)"
)

ASSEMBLY_PROOF_RESPONSE = (
    "refine ⟨?_, ?_, ?_⟩\n"
    "  · -- Novel lemma: regret decomposition\n"
    "    exact optimistic_regret_decomposition K V_hat V_star h_opt\n"
    "  · -- Library: Freedman's concentration inequality\n"
    "    exact freedman_tail_inversion hv hb hδ hδ1\n"
    "  · -- Library: law of total variance\n"
    "    exact law_of_total_variance w μ m₂ hw_nonneg hw_sum"
)


def smart_chat(messages, **kwargs):
    """Route LLM calls to the right hand-crafted response."""
    content = messages[0]["content"] if messages else ""

    # Phase 2: Classify/Verify (check BEFORE decompose — classify prompts are specific)
    if "candidate theorem" in content.lower() or "classify this lemma" in content.lower():
        # Extract lemma name from prompt
        name_match = re.search(r"Name:\s*(\w+)", content)
        lemma_name = name_match.group(1) if name_match else ""

        # Extract candidate IDs
        candidates = re.findall(r"Candidate:\s*([\w.]+)", content)

        log_call("CLASSIFY", f"Classifying {lemma_name} against {len(candidates)} candidates")
        return make_classify_response(lemma_name, candidates)

    # Phase 3: Formalize — statement generation
    if "type signature" in content.lower() or "convert this natural-language" in content.lower():
        if "main_theorem" in content or "building blocks" in content.lower():
            log_call("ASSEMBLE-STMT", "Generating main theorem signature")
            return ASSEMBLY_STATEMENT_RESPONSE
        # Distinguish by lemma name, not by context keywords
        name_match = re.search(r"must be `(\w+)`", content)
        lemma_name = name_match.group(1) if name_match else ""
        if lemma_name == "variance_aware_value_bound":
            log_call("INST-STMT", f"Generating instantiation statement ({lemma_name})")
            return INST_STATEMENT_RESPONSE
        else:
            log_call("NOVEL-STMT", f"Generating novel statement ({lemma_name})")
            return STATEMENT_RESPONSE

    # Phase 4: Assembly proof (check BEFORE locked-proof — assembly also says "LOCKED")
    if "informal proof sketch" in content.lower():
        log_call("ASSEMBLE-PROOF", "Writing main theorem proof")
        return ASSEMBLY_PROOF_RESPONSE

    # Phase 3: Formalize — proof body
    if "locked" in content.lower() and "proof" in content.lower():
        if "variance_aware_value_bound" in content:
            log_call("INST-PROOF", "Filling instantiation proof body")
            return INST_PROOF_RESPONSE
        else:
            log_call("NOVEL-PROOF", "Filling novel lemma proof body")
            return PROOF_RESPONSE_NOVEL

    # Phase 5: Audit
    if "hypothesis" in content.lower() and "auditor" in content.lower():
        log_call("AUDIT-HYP", "Checking hypothesis fidelity")
        return json.dumps({
            "mappings": [
                {"lean_param": "(K H : ℕ)", "paper_assumption": "K >= 1, horizon H", "status": "matched"},
                {"lean_param": "(hK : 1 ≤ K)", "paper_assumption": "K >= 1", "status": "matched"},
            ],
            "extra_hypotheses": [],
            "verdict": "pass",
            "reasoning": "All hypotheses correspond to paper assumptions"
        })

    # Phase 1: Decompose (LAST — "decompose" appears in lemma statements too)
    if "atomic lemma building blocks" in content.lower():
        log_call("DECOMPOSE", "Breaking proof into building blocks")
        return DECOMPOSE_RESPONSE

    log_call("UNKNOWN", content[:60])
    return "sorry"


def smart_embed(texts, **kwargs):
    """Return embeddings that align with corpus embeddings for correct retrieval."""
    embs = []
    for text in texts:
        text_lower = text.lower()
        if "freedman" in text_lower or "martingale" in text_lower:
            embs.append([0.8, 0.1, 0.05, 0.05])
        elif ("total variance" in text_lower or "law of total" in text_lower
              or "var(x)" in text_lower or "var(x|y)" in text_lower
              or ("var" in text_lower and "e[" in text_lower)):
            embs.append([0.1, 0.8, 0.05, 0.05])
        elif "variance" in text_lower and ("bound" in text_lower or "value" in text_lower
                                           or "sum" in text_lower or "horizon" in text_lower):
            embs.append([0.12, 0.75, 0.1, 0.03])
        elif "regret" in text_lower or "optimistic" in text_lower:
            embs.append([0.05, 0.05, 0.8, 0.1])
        else:
            embs.append([0.25, 0.25, 0.25, 0.25])
    return embs


# ---------------------------------------------------------------------------
# Build a small test corpus with real entries + matching embeddings
# ---------------------------------------------------------------------------

def build_test_corpus(tmp_dir):
    """Build a small corpus from real library entries relevant to this proof."""
    import json
    from pathlib import Path

    corpus_path = Path(tmp_dir) / "test_corpus.jsonl"

    # Pull relevant entries from the real corpus
    real_corpus = Path("benchmark/retrieval_corpus.jsonl")
    target_ids = [
        "RLGeneralization.Concentration.Freedman.freedman_tail_inversion",
        "RLGeneralization.Concentration.Freedman.freedman_vs_azuma",
        "RLGeneralization.Concentration.TotalVariance.law_of_total_variance",
        "RLGeneralization.Concentration.TotalVariance.law_of_total_variance_bound",
        "RLGeneralization.Exploration.VarianceUCBVI.total_variance_bound",
        "RLGeneralization.Exploration.VarianceUCBVI.variance_pigeonhole",
        "RLGeneralization.MDP.ValueDecomposition.variance_bound_expression_nonneg",
        "RLGeneralization.Algorithms.ModelBased.model_based_pac",
    ]

    entries = []
    with open(real_corpus) as f:
        for line in f:
            entry = json.loads(line)
            if entry["id"] in target_ids:
                entries.append(entry)

    # Write corpus
    with open(corpus_path, "w") as f:
        for e in entries:
            f.write(json.dumps(e) + "\n")

    # Generate matching embeddings (simple 4D vectors for testing)
    embeddings = []
    for e in entries:
        text = e["id"].lower()
        if "freedman" in text:
            embeddings.append([0.85, 0.1, 0.03, 0.02])
        elif "total_variance" in text or "TotalVariance" in text.replace(".", ""):
            embeddings.append([0.1, 0.85, 0.03, 0.02])
        elif "variance" in text:
            embeddings.append([0.12, 0.75, 0.1, 0.03])
        elif "model_based" in text:
            embeddings.append([0.05, 0.05, 0.1, 0.8])
        else:
            embeddings.append([0.25, 0.25, 0.25, 0.25])

    emb_path = corpus_path.with_name("test_corpus_embeddings.bin")
    save_embeddings(embeddings, emb_path)

    print(f"  Built test corpus: {len(entries)} entries, {len(embeddings)} embeddings")
    return str(corpus_path)


# ---------------------------------------------------------------------------
# Main test run
# ---------------------------------------------------------------------------

def main():
    import tempfile
    from pathlib import Path
    from datetime import datetime

    run_dir = Path(__file__).parent.parent / "runs"
    run_dir.mkdir(exist_ok=True)
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    run_output = run_dir / f"live_test_{timestamp}.txt"

    print("=" * 60)
    print("STATVERIFY LIVE PIPELINE TEST")
    print(f"Fixture: settling_online_rl_2024 (Zhang et al., COLT 2024)")
    print(f"LLM: Claude Code (hand-crafted responses)")
    print(f"Lean: REAL compilation via lake env lean")
    print(f"Output: {run_output}")
    print("=" * 60)

    # Build test corpus
    print("\n--- Setup ---")
    tmp_dir = tempfile.mkdtemp(prefix="statverify_test_")
    corpus_path = build_test_corpus(tmp_dir)

    # Create mock LLM with our smart handlers
    mock_llm = MagicMock()
    mock_llm.chat.side_effect = smart_chat
    mock_llm.embed.side_effect = smart_embed
    mock_llm.model = "claude-code-manual"

    # Create engine
    engine = StatVerifyEngine(llm=mock_llm, corpus_path=corpus_path)
    print(f"  Loaded {len(engine.retriever)} premises")

    # Run the full pipeline
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

    # Print results
    print(f"\n--- Results ---")
    print(f"  Overall: {report.overall.upper()}")
    print(f"  Lemmas: {len(report.lemmas)}")

    for l in report.lemmas:
        icon = {"library_verified": "+", "formalized": "!", "gap": "x"}.get(l.status, "?")
        kind_label = f" [{l.kind}]" if l.kind != "novel" else ""
        print(f"    {icon} {l.name}{kind_label}: {l.status}")
        if l.library_match_id:
            print(f"      matched: {l.library_match_id}")
        if l.lean_statement:
            print(f"      stmt: {l.lean_statement[:80]}")
        if l.compile_error:
            first = l.compile_error.split("\n")[0][:100]
            print(f"      error: {first}")
        if l.hypothesis_audit:
            print(f"      hyp_audit: {l.hypothesis_audit.verdict}")
        if l.structural_audit:
            print(f"      struct_audit: {l.structural_audit.verdict}"
                  f" (sorry={l.structural_audit.has_sorry})")

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

    # Print the assembled Lean code
    if report.lean_code:
        print(f"\n--- Assembled Lean Code ---")
        print(report.lean_code)
        print(f"--- End Lean Code ---")

    # Print LLM call log
    print(f"\n--- LLM Call Log ({len(call_log)} calls) ---")
    for i, phase in enumerate(call_log, 1):
        print(f"  {i:2d}. {phase}")

    # Check corpus growth
    with open(corpus_path) as f:
        final_count = sum(1 for _ in f)
    print(f"\n  Corpus: 8 → {final_count} entries")

    # Verdict
    print(f"\n{'=' * 60}")
    if report.overall == "verified":
        print("VERDICT: PIPELINE WORKS — all phases completed, proof compiles")
    elif report.overall == "has_gaps":
        gaps = [l.name for l in report.lemmas if l.status == "gap"]
        formalized = [l.name for l in report.lemmas if l.status == "formalized"]
        lib = [l.name for l in report.lemmas if l.status == "library_verified"]
        print(f"VERDICT: PIPELINE WORKS — has gaps but all phases ran")
        print(f"  Library: {lib}")
        print(f"  Formalized: {formalized}")
        print(f"  Gaps: {gaps}")
    else:
        print(f"VERDICT: {report.overall}")
    print("=" * 60)

    # Save outputs to runs/
    with open(run_output, "w") as f:
        f.write(f"StatVerify Live Test — {timestamp}\n")
        f.write(f"Fixture: settling_online_rl_2024\n")
        f.write(f"Overall: {report.overall}\n\n")
        f.write(f"Lemmas ({len(report.lemmas)}):\n")
        for l in report.lemmas:
            f.write(f"  {l.name}: {l.status} (kind={l.kind})\n")
            if l.library_match_id:
                f.write(f"    match: {l.library_match_id}\n")
            if l.compile_error:
                f.write(f"    error: {l.compile_error[:200]}\n")
        f.write(f"\nLLM calls: {len(call_log)}\n")
        for i, phase in enumerate(call_log, 1):
            f.write(f"  {i}. {phase}\n")
        if report.lean_code:
            f.write(f"\n--- Assembled Lean Code ---\n{report.lean_code}\n")
        f.write(f"\nSummary: {report.summary}\n")

    # Save assembled Lean file
    if report.lean_code:
        lean_output = run_dir / f"live_test_{timestamp}.lean"
        with open(lean_output, "w") as f:
            f.write(report.lean_code)
        print(f"\nSaved: {run_output}")
        print(f"Saved: {lean_output}")
    else:
        print(f"\nSaved: {run_output}")

    return 0 if report.overall in ("verified", "has_gaps") else 1


if __name__ == "__main__":
    sys.exit(main())
