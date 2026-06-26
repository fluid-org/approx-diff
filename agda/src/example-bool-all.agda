{-# OPTIONS --prop --postfix-projections --safe #-}

-- Examples with Two-valued (Bool) approximation.  Each analysis lives in its own file for fast independent
-- compilation; this module just aggregates them.
module example-bool-all where

import example-bool-fwd    -- forward slice
import example-bool-bwd    -- Galois backward slice (to-gal)
import example-bool-mult   -- value-dependent derivative interpretation of `mult`

-- These take several mins to run each; commented out for now
-- import example-bool-cbn-bwd-a     -- CBN backward slice (label a)
-- import example-bool-cbn-bwd-b     -- CBN backward slice (label b)
