{-# OPTIONS --prop --postfix-projections --safe #-}

module example.all where

import example.bool-fwd
import example.bool-bwd
import example.bool-mult
-- import example.dependency-mavg  -- typechecks very slowly
import example.dependency-total
import example.rationals-fwd
import example.rationals-bwd
import example.rationals-total
import example.counting-total
import example.free-total
import example.intervals-query
import example.intervals-mult-total
import example.signs-score
