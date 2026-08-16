{-# OPTIONS --prop --postfix-projections --safe #-}

-- The examples over the Booleans, instantiated once so consumers pay for the module application
-- through the interface file.
module example.relations-two where

import two
open import example.relations two.semiring two.I public
