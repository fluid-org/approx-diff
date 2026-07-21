module Talk where

import Prelude

data MGraph a
   = Empty
   | Vertex a
   | Overlay (MGraph a) (MGraph a)
   | Connect (MGraph a) (MGraph a)

empty :: forall a. MGraph a
empty = Empty

vertex :: forall a. a -> MGraph a
vertex = Vertex

overlay :: forall a. MGraph a -> MGraph a -> MGraph a
overlay = Overlay

connect :: forall a. MGraph a -> MGraph a -> MGraph a
connect = Connect

edge :: forall a. a -> a -> MGraph a
edge x y = connect (vertex x) (vertex y)

-- | Generalised 'Graph' folding: recursively collapse a 'Graph' by applying
-- | the provided functions to the leaves and internal nodes of the expression.
-- | The order of arguments is: empty, vertex, overlay and connect.
foldg :: forall a b. b -> (a -> b) -> (b -> b -> b) -> (b -> b -> b) -> MGraph a -> b
foldg e v o c = go
   where
   go = case _ of
      Empty -> e
      Vertex x -> v x
      Overlay x y -> o (go x) (go y)
      Connect x y -> c (go x) (go y)

isEmpty :: forall a. MGraph a -> Boolean
isEmpty = foldg true (const false) (&&) (&&)

size :: forall a. MGraph a -> Int
size = foldg 1 (const 1) (+) (+)

-- | We almost have that Graph satisfies the axioms of a semiring, it is a semiring without
-- | multiplicative inverse and with a new decomposition law. Taking + to be overlay,
-- | and connect to be * we obtain:
-- | (Graph, +):
-- | (a + b) + c = a + (b + c), by structuralEquality
-- | Empty + a = a = a + Empty
-- | a + b = b + a, by structuralEquality
-- | (Graph, *):
-- | (a * b) * c = a * (b * c), by structuralEquality
-- | (Empty * a) = a = (a*Empty)
-- | (Graph,+,*)
-- | a * (b + c) = (a * b) + (a * c)
-- | (a + b) * c = (a * c) + (b * c)
-- | We do not have an annihilation law, ie: connect Empty a != 0 != connect a Empty
-- | Instead we have:
-- | x * y * z = (x * y) + (x * z) + (y * z)

type Name =
   { firstName :: String
   , surname :: String
   }

addSuffixJr :: forall r. { surname :: String | r } -> { surname :: String | r }
addSuffixJr record = record { surname = record.surname <> " Jr." }

data Either a b = Left a | Right b
data Either3 a b c = Left3 a | Middle3 b | Right3 c