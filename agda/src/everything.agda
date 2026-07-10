{-# OPTIONS --prop --postfix-projections --safe #-}

module everything where

import example.all

-- Section 3 "Models of Semiring Dependency": Fam(C) is bicartesian closed when C has biproducts and
-- all small products (Lucatelli Nunes and Vákár 2023). (Imported by ho-model; here for documentation.)
import fam-exponentials

-- Section 4 "Higher-Order Language": the interpretation of the higher-order language.
import ho-model

-- The first-order models (Section 3): self-dual semimodules over a commutative semiring, and the
-- Boolean special case, self-dual Boolean algebras.
import ho-model-sd-semimod
import ho-model-boolalg-sd-semimod

-- Mat(S) embeds in any biproduct category with a chosen object, factoring through the self-dual
-- semimodules: the Jacobian-as-matrix picture of Section 2.
import matrix-embedding-semimod

-- Semirings for the examples: min-times tropical for relative perturbation bounds, and the
-- rule-of-signs domain for the signed-saliency analysis.
import semiring-Q-tropical-mult
import semiring-sign

-- Section 6 "Correctness of the Higher-Order Interpretation": the Fiore and Simpson 1999 definability
-- theorem gives agreement of the underlying function with the Set interpretation at first order.
-- Conservativity at first-order types comes from H being full and faithful (Section 3).
import conservativity

-- Bicartesian closure of CM (bounded meet semilattices and conditionally multiplicative functions),
-- supporting the stable-function material now discussed as future work in the Conclusion.
import bounded-meet
