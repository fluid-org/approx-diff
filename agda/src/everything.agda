{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- The results of the paper and the tests. A module outside this dependency chain isn't part of the development.
module everything where

-- Every value and environment is total: val-total, env-total. Existence half of the determinism theorem: eval.
import language-operational.totality

-- Uniqueness half of the determinism theorem, including the derivation: unique.
import language-operational.uniqueness

-- Fundamental lemma: fundamental-val, fundamental. Map lemma: map-val, map-dep.
-- Soundness of values at every type: soundness-val; of dependence at first-order types: soundness-dep.
-- Injectivity of the value interpretation: val-idx-inj. Adequacy, for the derivation eval provides: adequacy.
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
