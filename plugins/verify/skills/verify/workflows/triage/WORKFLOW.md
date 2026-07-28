# Triage workflow

Use for vague requests such as "look at this proof", "check this argument", or
"what do you think of this derivation" when complete verification was not
explicitly requested.

Run cheap sealed triage with `verify_run(scope="triage", ...)`, passing pasted
statement and proof text directly when available. The user's request to check
or review the proof authorizes this triage scope.

If the product tool is unavailable, use:

```text
<verify-python> -m harness triage <target> --backend <current-host>
```

Identify suspicious steps and the smallest useful next check. Do not begin full
verification automatically. Run the module from the runtime source directory
returned by the root preflight. Ask one concise question, such as whether the
user wants the questionable inequality falsified or wants complete Lean
verification.

Triage is prioritization-only and cannot establish correctness.
