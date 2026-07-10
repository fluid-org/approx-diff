{-# OPTIONS --prop --postfix-projections --safe #-}

module everything where

-- The examples of Section 5, one interpretation instance per semiring.
import example.all

-- Section 3 "Models of Semiring Dependency": Fam(C) is bicartesian closed when C has biproducts
-- and all small products (Lucatelli Nunes and Vákár 2023).
import fam-exponentials

-- The first-order models (Section 3): self-dual semimodules over a commutative semiring, and the
-- Boolean special case, self-dual Boolean algebras.
import ho-model-sd-semimod
import ho-model-boolalg-sd-semimod

-- Section 6 "Correctness of the Higher-Order Interpretation": the Fiore and Simpson 1999
-- definability theorem, in the conservativity module, gives agreement of the underlying function
-- with the Set interpretation at first order.
import conservativity
