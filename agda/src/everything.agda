{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- The results of the paper and the tests. A module outside this dependency chain is not part of the
-- development.
module everything where

-- Existence half of the determinism theorem: fundamental, eval.
import language-operational.totality

-- Fundamental lemma: fundamental-val, fundamental. Map lemma: map-val, map-dep.
-- Soundness: soundness-val, soundness-dep. Injectivity of the value interpretation, for adequacy: val-idx-inj.
import ho-agreement

-- Reading of a first-order value as a tree on the first-order side, ahead of the value-level agreement
-- that complements conservativity.
import value-interpretation

-- Tests.
import example.interaction
import example.render.relations
import example.render.dep-graph
