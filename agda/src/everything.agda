{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- The results of the paper and the tests. A module outside this dependency chain is not part of the
-- development.
module everything where

-- Existence half of the determinism theorem: fundamental, eval.
import language-operational.totality

-- Fundamental lemma: fundamental-val, fundamental. Map lemma: map-val, map-dep.
-- Soundness: soundness-val, soundness-dep. Injectivity of the value interpretation, for adequacy: val-idx-inj.
import ho-agreement

-- Hiding in any order gives the same relation: hide-all-perm.
import interaction.graph

-- Operational agreement: agree, agree-s, agree-m.
import interaction.dependence-graph

-- Summaries assemble: summaries-assemble. Moves maintain the configuration: initial-summarised,
-- hide-at-summarised, reveal-at-summarised. Hide and reveal are mutually inverse: hide-reveal, reveal-hide.
import interaction.moves

-- Tests.
import example.interaction
import example.value-flow
import example.render.relations
import example.render.dep-graph
