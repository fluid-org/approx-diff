{-# OPTIONS --prop --postfix-projections --safe #-}

-- Examples with Two-valued (Bool) approximation.  Each analysis lives in its own file for fast incremental
-- compilation; the shared model setup is in the harnesses example-bools-matrix (value-carrying, BaseInterp1)
-- and example-bools-cbn (call-by-name, BaseInterp0).  This module just aggregates them.
module example-bools where

import example-bools-matrix-fwd    -- forward slice
import example-bools-matrix-bwd    -- Galois backward slice (to-gal)
import example-bools-matrix-mult   -- value-dependent derivative interpretation of `mult`
import example-bools-cbn-bwd-a     -- CBN backward slice (label a)
import example-bools-cbn-bwd-b     -- CBN backward slice (label b)
