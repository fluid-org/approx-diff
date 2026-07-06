{-# OPTIONS --prop --postfix-projections --safe #-}

module examples where

import example-bool-fwd
import example-bool-bwd
import example-bool-mult
import example-dependency-mavg
import example-dependency-total
import example-rationals-fwd
import example-rationals-bwd
import example-rationals-total
import example-counting-total
import example-free-total
import example-intervals-query
import example-intervals-mult-total

-- Slow (several minutes each):
-- import example-bool-cbn-1
-- import example-bool-cbn-2
