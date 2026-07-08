{-# OPTIONS --prop --postfix-projections --safe #-}

module everything where

import example.all

-- Proof from Section 2.2 (Theorem 2.3) that CM (category of bounded
-- meet semilattices and conditionally multiplicative functions) is
-- bicartesian closed. We have not yet formalised Theorem 2.14 on
-- bicartesian-ness of L-posets and stable functions.
import bounded-meet

-- Proof from section 3.2 (Theorem 3.6) that Fam(C) is a cartesian
-- closed if C has biproducts and all small products (Lucatelli Nunes
-- and Vákár 2023). (Imported by ho-model anyway, but included here
-- for documentation purposes.)
import fam-exponentials

-- Construction of the interpretation of the higher-order language in
-- Section 4
import ho-model

-- Instantiations of the interpretation, with self-dual semimodules and self-dual Boolean algebras
-- as the first-order models.
import ho-model-sd-semimod
import ho-model-boolalg-sd-semimod

-- Mat(S) embeds in any biproduct category with a chosen object; instantiated at SemiMod(S) and 𝕀,
-- the embedding factors through the self-dual semimodules.
import matrix-embedding-semimod

-- The nonzero entries of a rational matrix as a lax functor Mat(ℚ) → Mat(𝟚); composition is
-- preserved only laxly, the chain-rule over-approximation of Boolean dependency tracking.
import matrix-nonzero

-- Further semirings awaiting worked examples: relative perturbation bounds (min-times tropical)
-- and the rule-of-signs abstract domain.
import semiring-Q-tropical-mult
import semiring-sign

-- Proofs from Section 5 "Definability"
--
-- (1) a factorisation of the embedding of the first-order semantic
--     domain into the higher-order one via a category of Grothendieck
--     Logical Relations (Fiore and Simpson 1999) (Theorem 5.1). See
--     the declaration "definability" in the conservativity module.
--
-- (2) every morphism definable in the higher-order language is
--     definable in the first-order language (Theorem 5.2). See the
--     declaration "syntactic-definability" in the conservativity
--     module.
--
-- Imported by ho-model anyway, but included here for documentation
-- purposes.
import conservativity
