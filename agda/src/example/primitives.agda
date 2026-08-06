{-# OPTIONS --prop --postfix-projections --safe #-}

-- The Boolean instance of the example primitives, the dependency reading the tests and dumps use.
module example.primitives where

import two
open import two renaming (I to ⊤; O to ⊥) using () public
import example.primitives-over
open module EPO = example.primitives-over two.semiring public
