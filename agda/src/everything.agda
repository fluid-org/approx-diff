{-# OPTIONS --prop --postfix-projections --safe #-}

module everything where

-- Value-level tests of the examples: Boolean dependency, rational AD, and perturbation bounds,
-- each a Primitives record with its model derived by interp-primitives. Renderings are tested as
-- artefacts (graph-viz.dump-graphs and script/check-dot.sh).
import test.all

-- Fam(C) is bicartesian closed when C has biproducts and all small products (Lucatelli Nunes and
-- Vákár 2023).
import fam-exponentials

-- The first-order model: self-dual semimodules over a commutative semiring, with the higher-order
-- model over it and the interpretation of the primitives.
import ho-model-sd-semimod

-- The Fiore and Simpson 1999 definability theorem gives agreement of the underlying function with
-- the Set interpretation at first order.
import conservativity

-- Polynomials over a category and their parameterised initial algebras; the
-- action of a functor on polynomials, and the action of componentwise
-- morphisms and isomorphisms on μ-objects.
import polynomial-functor

-- For the language with general recursive types: every first-order type's
-- interpretation in the higher-order model is isomorphic to the image of its
-- first-order interpretation.
import language-fo-interpretation
