{-# OPTIONS --prop --postfix-projections --safe #-}

module everything where

-- The examples of Section 5, one interpretation instance per semiring.
import example.all

-- Section 3 "Models of Semiring Dependency": Fam(C) is bicartesian closed when C has biproducts
-- and all small products (Lucatelli Nunes and Vákár 2023).
import fam-exponentials

-- The first-order model (Section 3): self-dual semimodules over a commutative semiring.
import ho-model-sd-semimod

-- Section 6 "Correctness of the Higher-Order Interpretation": the Fiore and Simpson 1999
-- definability theorem, in the conservativity module, gives agreement of the underlying function
-- with the Set interpretation at first order.
import conservativity

-- Polynomials over a category and their parameterised initial algebras; the
-- action of a functor on polynomials, and the action of componentwise
-- morphisms and isomorphisms on μ-objects.
import polynomial-functor

-- For the language with general recursive types: every first-order type's
-- interpretation in the higher-order model is isomorphic to the image of its
-- first-order interpretation.
import language-fo-interpretation
