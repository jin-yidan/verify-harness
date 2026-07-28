/-
# Generative Model: Re-export Shim

This file re-exports the generative-model infrastructure that was
split into four focused modules:

* `GenerativeModelCore` — product measure, independence, Hoeffding PAC
* `GenerativeModelEmpirical` — empirical MDP definitions, policy converters
* `GenerativeModelBernstein` — Bernstein concentration for the product space
* `GenerativeModelMinimax` — deterministic minimax reductions, high-probability lifts
* `GenerativeModelPAC` — sample complexity inversion, capstone PAC theorems

All downstream imports of `GenerativeModel` continue to work via
transitive re-export.
-/

import RLGeneralization.Concentration.GenerativeModelPAC
