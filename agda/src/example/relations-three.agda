{-# OPTIONS --prop --postfix-projections --safe #-}

-- The examples over the three-chain, instantiated once so consumers pay for the module application
-- through the interface file.
module example.relations-three where

import three
open import example.relations three.semiring three.C public
