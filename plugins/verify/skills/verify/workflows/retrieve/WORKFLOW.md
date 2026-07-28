# Formal-library retrieval workflow

Use when the user asks whether a result is already formalized or wants reusable
lemmas for a statistics, probability, RL, or supporting-mathematics argument.

Search with the plugin-facing `verify_search_library` tool or:

```text
<verify-python> -m rlverify retrieve "<mathematical query>"
```

Return candidate identifiers, signatures, source modules, and why each may
match. Do not describe a search hit as applicable until its types and
hypotheses have been checked. Run the module from the runtime source directory
returned by the root preflight. Retrieval alone carries no proof authority.
