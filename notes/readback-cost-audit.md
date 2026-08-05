# Evaluation-path cost audit (task 28), working notes 2026-08-05

## Counted recurrences (per single output-coordinate query, model side = SemiMod pairs)

- `under-root r = (inj ∘ (r ∘ pm id payloadL)) +m ((root ∘ tagL) ∘ π₂)` (lifting-fold:711):
  payload coord → 1 query of r + O(1); root coord → 1 head query of input + O(1). Fan-in 1.
- `strip-root c r` (lifting-fold:715): 1 query of r + 1 head query of scrutinee + O(1).
- Enriched `pair f g = (in₁∘f) +m (in₂∘g)`, `copair f g = (f∘p₁) +m (g∘p₂)` (cmon-enriched):
  per coord, one expensive arm + one arm that is ε of the other component. ε access is a record
  projection on a shared thunk. Fan-in 1 + cheap.
- `strong-prod-m f g = pair (f∘strong-p₁) (g∘strong-p₂)` (categories:610): context fibre
  duplicated into both arms; per coord still one expensive arm.
- Fam strong copair (fam.agda:884): direct dispatch on the index, no substs. Fan-in 1.
- Fold (fam-mu-lifting/fold.agda): per cons cell, alg application + 2 under-root + strong-prod-m;
  index-level fold-shape-idx recomputed per node: O(d) each, O(d²) total, cheap scalars.
  Fibre side: T(level i) = T(level i+1) + k·C_in + O(1) → linear in d.
- Comparison isos (fibrewise fwd, 𝓥-Lp-iso, blocks iso): per node constant redirects; the
  backward μ-comparison (fibrewise:501) fires a full-tree fib-subst per application, but for
  length only fwd is on the input side; closed-iso.bwd at base type is trivial.
- Primitives: mat→mor at disc widths 1-2, Σ over ≤2.
- Input coordinate query = `colv` = one B-entry of the context Pos. Over two, `⊔`/`⊓` compile to
  case on FIRST arg only (Qtwo.hs:104,131): `I ⊔ _` and `O ⊓ _` do not force the second arg, so
  Σ short-circuits at the first I and skips coords under O entries. B-entry ≈ O(dim·nesting).

## Contradiction

Static count ⇒ per-entry cost is low-polynomial in d. Measured: d2 ≈ 1.6–2.5 s/entry with 148 GB
allocation; d3 > 13.5 min for ONE entry (>300×/level). Two prior hypotheses (copair duplication,
optimiser) already refuted by measurement. So the growth driver is NOT visible in the designed
combinator structure; it must be a compilation/sharing artifact not captured above.

## Probe (graph-viz/probe-scaling.agda, committed)

Depth axis: unit-payload list μ(unit + (unit × var0)), lengths at d1..d4 (fold layers grow, width
minimal). Width axis: pair-of-pairs payload at fixed d2 (width doubles). Anchors: pair payload d1
full row, d2 single entry + full row. Stages write /tmp/probe-*.txt in cost order; timestamps
attribute per-stage cost even if killed.

Predictions:
- layer-driven: u-ratios large (u3/u2 ≈ pair d3/d2 shape); w2e ≈ p2e × small const.
- dim-driven: u-series flat; w2e ≫ p2e.
- mixed dim^Θ(d): u grows with smaller ratio than pair series.

## Probe run 2026-08-05 15:11 (-O0, fresh process)

- u1 (unit d1, 5 entries): ~1 s incl start-up. Row 11010.
- u2 (unit d2, 8 entries): ~2 s. Row 11011010.
- p1 (pair d1, 6 entries): <1 s. Row 110010 (matches baseline).
- p2e (pair d2, 1 entry): ~1 s.
- w2e (pair-of-pairs d2, 1 entry): ~55 s.  → width alone ×55 at fixed depth.
- u3e (unit d3, 1 entry): >2 min and counting. → depth alone ≥×500 per level at fixed width.
Both axes multiply independently; neither dim nor layer count alone explains it. Earlier run
wedged: Mac idle sleep (0% CPU, paged out); enforce budgets with caffeinate -i + kill-loop
watchdog; perl alarm unreliable under GHC RTS.

Final probe numbers: u3e = 205 s (15:12:27→15:15:52), p2 row = 12 s. Ratios: unit-payload per-entry
d1→d2 ≈ ×12 (startup-corrected), d2→d3 ≈ ×800; width d2 pair→pairpair ≈ ×55. The per-level ratio
itself grows ~×70 per level: compounding recomputation, per-level query count growing with depth.
No smooth single-exponential fits; threshold or nested compounding. Profiled binary
(_build-prof/probe-prof, -fprof-auto-top -O0) over anchor(p2e)+wide(w2e)+deep(u3e): entry counts
per cost centre will give the counted recurrence.

## Profile (probe-prof, 405 s, 474 GB alloc, anchor+wide+deep)

Flat: Σ 35%, matrix.in₂ 11.4%, order-idempotent.B 6.5%, matrix.e 6.2%, dictionary projections
(additive/+/ε/lattice/multiplicative) ~19%, matrix.∘ 4.2%.
Tree: 79.1% inherited in one stack ending at colv, +17.8% in a second colv stack (97% total).
Ancestry: deep → dep-mat → dep.func → ctxt-iso fwd → fibrewise-μ-iso fwd-mor → fib-ciso →
fib-shape-ciso → fib-el-ciso → [semimodule.biproduct → ⊕ → ⊗-setoid → FamF.fobj → changeCat →
𝓥F → 𝒟 → biproducts→products → blocks-biproduct → rightV] → colv. Under colv: Σ entries
507M, B entries 55M, in₂ entries 308M. So: cost = (#input-coordinate reads) × (B-entry cost),
reads compound with depth, B-entry cost with width/nesting. The object tower (blocks-biproduct,
𝒟, FamF fobj, ⊕) is rebuilt per read: MAlonzo shares nothing across module-parameter application.

FIX 1 (landed): colv-tab in order-idempotent.agda (tabulate the basis column, Fixed proof via
lookup∘tabulate); readback dep-mat reads the tabulated column. Kills the per-read B-entry cost
(~97% of profiled time). Residual: the read count itself (compounds with depth) now hits an O(1)
lookup; u4e stage added to measure the residual compounding post-fix.

## Negative result 2026-08-05 pm

colv-tab v2 (table passed as argument; compiled code verified: one tabulate thunk per column,
lookup closure captures it; dep-mat confirmed calling it) leaves timings UNCHANGED: w2e 56 s,
u3e 210 s. So the dominant cost is NOT per-read recomputation of ord entries. Revised reading of
the profile: the ~507M Σ calls under the colv stack are mostly the READS themselves, i.e. cheap
executions of app/Σ-shaped layers (widths 1-2, plus dictionary projections), attributed beneath
colv by closure-entry accounting (lexical CCS: costs run under the closure's creation stack, and
the value chain bottoms out at the input column). The COUNT (~5×10^8 per entry at u3e) is the
cost. Fix must reduce the count: memoise intermediate vector VALUES per layer (Data.Vec
representation or targeted tabulation), not the input column. Re-profiling with current code to
locate the fan-out chain via per-function entry counts.

## Resolution 2026-08-05 evening (counted)

Post-colv-tab profile: 78.5% inherited on the path dep-mat → colv-tab → tabulate → ord → ctxt
fibre → blocks ⊕ → B → ∘ₘ → Σ. With reads memoised, computing ~11 column ENTRIES is 78.5% of the
run: one entry of a nested block order costs Π(dims) across the ⊕-nesting (each B level scans its
dimension via Σ to find the one nonzero of in/p, recursing one level per Lp and per ⊕; two's
laziness prunes the · arms but every level still pays a full Σ scan per child entry). u3 dims
11·10·8·7·5·4·2 ≈ 2.5e5 raw steps/entry × dictionary overhead ≈ observed 210 s. Depth ratio
~800×/element = two nesting levels ≈ dim² per level; width ratio 55× = extra payload nesting.
READ-COUNT COMPOUNDING REFUTED (third dead hypothesis); reads were always few. colv-tab stays:
it localises all ord-entry evaluation into the one tabulation site.

CONCLUSION: driver = entry-oriented evaluation of nested block orders. The agreed action-primary
Pos redesign is the fix and is ASYMPTOTIC, not a constant factor as previously estimated: orders
as structural actions make a ⊕-entry O(nesting) (split index, recurse into one block), total
column cost O(dim × nesting). Interim alternative if wanted sooner: tabulate each ⊕ node's B
matrix at construction (argument-passing discipline), O(dim²) per node once, but proofs that use
(P ⊕ Q).ord ≡ B definitionally need pointwise-≡ bridges; the action-primary layer supersedes it.
