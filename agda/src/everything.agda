{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- The results of the paper and the tests. A module outside this dependency chain is not part of the
-- development.
module everything where

-- Existence half of the determinism theorem: fundamental, eval.
import language-operational.totality

-- Fundamental lemma: fundamental-val, fundamental. Map lemma: map-val, map-dep.
-- Soundness: soundness-val, soundness-dep. Injectivity of the value interpretation, for adequacy: val-idx-inj.
import ho-agreement

-- Tests.
import example.interaction
import example.value-flow
import example.render.relations
import example.render.dep-graph
