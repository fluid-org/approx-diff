# Agda supplementary material accompanying "Approximation as Automatic Differentiation"

## Notes

Compiled with Agda version 2.7.0.1 and Agda standard library version 2.2.

### Entry point

- From this folder (the folder containing `approx-diff.agda-lib`), compile `src/everything.agda`
- See documentation in that file for relationship to results in paper

## Open proofs

Parked metatheory for the dependence-graph development (`language-operational/{path,graph,hide}.agda`), in dependency order:

- Forward-edge lemma: a non-zero entry of `graph D` strictly increases `rank`; acyclicity follows. Requires expanding the judgement's catch-all clause into explicit cases, since it does not reduce on neutral vertices; plan is to generate those clauses mechanically.
- Order-independence of `hide-all` on acyclic graphs (path-sum characterisation of hiding).
- Maintenance: `hide-at` and `reveal-at` preserve the invariant that a configuration's pairs are the regions of the hidden set with their summaries, and are mutually inverse.
- Agreement is proved: `language-operational/agreement.agda` shows by mutual induction that
  collapsing a derivation's graph recovers its relation, across all three judgement forms.
