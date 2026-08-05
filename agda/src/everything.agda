{-# OPTIONS --prop --postfix-projections --safe #-}

module everything where

-- Value-level tests: the position-order matrix laws.
import test.all

-- Fam(C) is bicartesian closed when C has biproducts and all small products (Lucatelli Nunes and
-- Vákár 2023).
import fam-exponentials

-- The higher-order model: families over the position orders, roots as isolated positions via the
-- biproduct lifting, with first-order definability of the interpretation.
import ho-model-roots-order-idempotent

-- The β and η laws of the rooted μ-types over an arbitrary lifting.
import fam-mu-lifting.laws

-- Polynomials over a category and their parameterised initial algebras; the
-- action of a functor on polynomials, and the action of componentwise
-- morphisms and isomorphisms on μ-objects.
import polynomial-functor

-- For the language with general recursive types: every first-order type's
-- interpretation in the higher-order model is isomorphic to the image of its
-- first-order interpretation.
import language-fo-interpretation

-- The instrumented operational semantics with its dependence graphs, totality of evaluation, and
-- the value renderer.
import language-operational.instrument
import language-operational.dependence-graph
import language-operational.totality
import language-operational.render

-- Generic category theory retained beyond its current consumers: presheaf machinery, predicate
-- systems and the glueing construction.
import yoneda
import functor-cat-limits
import functor-cat-products
import functor-cat-coproducts
import product-cocontinuity
import stable-coproducts-indexed
import finite-coproducts-from-indexed
import fam-stable-indexed
import presheaf-predicate
import closure-predicate
import glueing-simple
