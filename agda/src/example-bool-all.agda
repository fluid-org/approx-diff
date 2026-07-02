{-# OPTIONS --prop --postfix-projections --safe #-}

-- Examples with Two-valued (Bool) approximation.
module example-bool-all where

import example-bool-fwd    -- forward slice (query)
import example-bool-bwd    -- Galois backward slice (query)
import example-bool-mult   -- derivative interpretation of `mult`
