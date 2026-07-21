module Test.Main where

import Prelude

import Algebra.Graph (Graph(..), edgeList, clique)
import Algebra.Graph.Internal (fromArray)
import Data.List.Types (List(..), (:))
import Data.Map (fromFoldable)
import Data.Tuple (Tuple(..), snd)
import Effect (Effect)
import Graph.Utils.Monads (addVertex, baRunTest, outDegrees)
import Test.Unit (suite, test)
import Test.Unit.Assert as Assert
import Test.Unit.Main (runTest)

main :: Effect Unit
main = runTest do
   suite "graph utils" do
      test "Correctness of addVertex" do
         Assert.equal (edgeList (snd (addVertex Empty 1 [ 2, 3, 4, 5 ]))) (fromArray [ (Tuple 1 2), (Tuple 1 3), (Tuple 1 4), (Tuple 1 5) ])
      test "outDegrees correct" do -- odd, due to the directional nature of the graphs
         Assert.equal (outDegrees (clique (fromArray [ 1, 2, 3, 4 ]))) (fromFoldable ((Tuple 1 3) : (Tuple 2 2) : (Tuple 3 1) : (Tuple 4 0) : Nil))
      test "baRunTest correct" do
         Assert.equal (show $ baRunTest 3 20 1234598134) ("(fromFoldable [(Tuple 1 4),(Tuple 2 6),(Tuple 3 21),(Tuple 4 17),(Tuple 5 2),(Tuple 6 16),(Tuple 7 3),(Tuple 8 2),(Tuple 9 2),(Tuple 10 3),(Tuple 11 3),(Tuple 12 3),(Tuple 13 3),(Tuple 14 3),(Tuple 15 3),(Tuple 16 3),(Tuple 17 3),(Tuple 18 3),(Tuple 19 3),(Tuple 20 3),(Tuple 21 2),(Tuple 22 2),(Tuple 23 2),(Tuple 24 2)])")
