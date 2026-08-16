{-# OPTIONS --prop --postfix-projections --safe #-}

-- The examples over the Booleans, instantiated once so consumers pay for the module application
-- through the interface file.
module example.runs-two where

import two
open import example.runs two.semiring two.I public
