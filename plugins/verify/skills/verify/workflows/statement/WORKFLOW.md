# Statement-audit workflow

Use when the user asks whether a formal statement faithfully represents the
intended theorem.

Compare:

- quantifiers and their order;
- domains and types;
- equality versus inequality;
- strict versus non-strict relations;
- constants and normalization;
- conditions and side assumptions;
- probability, expectation, and asymptotic semantics.

Use sealed back-translation when available: translate the Lean statement into
precise English without seeing the claimed prose, then compare the two.

Return `MISMATCH` only with a concrete difference. A match is audit evidence,
not proof of the theorem.
