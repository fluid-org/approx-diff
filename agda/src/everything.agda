{-# OPTIONS --prop --postfix-projections --safe #-}

module everything where

import examples

-- Backward analyses of the list and rose-tree examples for the language with
-- general recursive types, over the self-dual Boolean algebras.
import example-bools-2

-- Backward (Galois) analysis of the examples, with rational-interval
-- approximation.
import example-intervals

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
import fam-realisation
import product-cocontinuity
import fam-mu-realisation

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

-- Polynomials over a category and their parameterised initial algebras; the
-- action of a functor on polynomials, and the action of componentwise
-- morphisms and isomorphisms on μ-objects.
import polynomial-functor-2

-- For the language with general recursive types: every first-order type's
-- interpretation in the higher-order model is isomorphic to the image of its
-- first-order interpretation.
import language-fo-interpretation-2
