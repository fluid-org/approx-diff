{-# OPTIONS --prop --postfix-projections --safe #-}

module example.all where

-- import example.dependency-mavg  -- typechecks very slowly
import example.dependency-total
import example.rationals-fwd
import example.rationals-bwd
import example.rationals-total
import example.intervals-query
