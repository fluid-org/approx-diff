module Graph.Utils.Monads
   ( addVertex
   , baNewNodeST
   , baRunT
   , baRunTest
   , cmpSnd
   , deltaGraph
   , inDegrees
   , newNeighbours
   , outDegrees
   , outStarG
   , shuffle
   , toAdjacencyMap
   , totDegrees
   , printGraph
   ) where

import Prelude

import Algebra.Graph (Graph, connect, foldg, overlay, transpose, vertex, vertexCount, vertices, clique)
import Algebra.Graph.AdjacencyMap as AM
import Algebra.Graph.Internal (fromArray)
import Control.Monad.Reader (Reader, runReader)
import Control.Monad.Reader.Trans (ask)
import Control.Monad.State (StateT, get, put, lift, runStateT)
import Data.Array (filter, fromFoldable, sortBy, take, zip, zipWith, length, unzip)
import Data.Foldable (foldl)
import Data.Function (on)
import Data.List (List)
import Data.Map (Map, intersectionWith, values)
import Data.Map.Internal (showTree)
import Data.Newtype (unwrap)
import Data.Set (size)
import Data.Tuple (Tuple(..), fst, snd)
import Data.Unfoldable (replicateA)
import Effect (Effect)
import Effect.Console (log)
import Random.PseudoRandom (Seed, mkSeed, randomRs)

cmpSnd :: forall a. Tuple a Number -> Tuple a Number -> Ordering
cmpSnd = compare `on` snd

shuffle :: forall a. Array a -> Reader Seed (Array a)
shuffle xs = do
   seed <- ask
   let
      randomDraws = randomRs 0.0 1.0 (length xs) seed :: Array Number
      zipped = zip xs randomDraws :: Array (Tuple a Number)
   pure (fst (unzip (sortBy cmpSnd zipped)))

-- compareNonEmptys :: NonEmptyArray Int -> NonEmptyArray Int -> NonEmptyArray Boolean
-- compareNonEmptys xs ys = zipWith (>=) xs ys

newNeighbours :: Array Int -> Int -> Reader Seed (Array Int)
newNeighbours nodeDegrees m = do
   seed <- ask
   let
      numNodes = length nodeDegrees
      maxNum = foldl (+) 0 nodeDegrees
      randomDraws = randomRs 1 maxNum numNodes seed -- imperative random numbers
      flags = zipWith (>=) randomDraws nodeDegrees :: Array Boolean
      selectionPairs = zip nodeDegrees flags :: Array (Tuple Int Boolean)
      selected = fst (unzip (filter snd selectionPairs)) :: Array Int
      shuffled = shuffle selected
   take m <$> shuffled

deltaGraph :: Int -> Graph Int -> Reader Seed (Graph Int) -- State (Graph Int) (Graph Int)
deltaGraph m prev =
   do
      let
         newId = 1 + (vertexCount prev)
         degrees = fromFoldable (values (totDegrees prev)) -- Array Integers
      neighbours :: Array Int <- newNeighbours degrees m
      let
         diffGraph = outStarG newId neighbours
      pure diffGraph

baNewNodeST :: Int -> StateT (Graph Int) (Reader Seed) (Graph Int)
baNewNodeST m = do
   prev <- get
   diffNew <- lift (deltaGraph m prev)
   let
      newGraph = overlay prev diffNew
   put newGraph
   pure diffNew

baRunT ∷ Int → Int → Graph Int -> Seed → Tuple (List (Graph Int)) (Graph Int)
baRunT m numSteps initG seed =
   runReader (runStateT (replicateA numSteps (baNewNodeST m)) initG) seed

printGraph :: Graph Int -> Effect Unit
printGraph = toAdjacencyMap >>> unwrap >>> showTree >>> log

-- test m initial = runStateT (baNewNodeST m) initial

-- Utilities Which Make deltaGraph and baNewNodeST work
-- Needed to reexport these for constructing degree functions
toAdjacencyMap :: forall a. Ord a => Graph a -> AM.AdjacencyMap a
toAdjacencyMap = foldg AM.empty AM.vertex AM.overlay AM.connect

outDegrees :: forall a. Ord a => Graph a -> Map a Int
outDegrees g = map size (unwrap (toAdjacencyMap g))

inDegrees :: forall a. Ord a => Graph a -> Map a Int
inDegrees = transpose >>> outDegrees

totDegrees :: forall a. Ord a => Graph a -> Map a Int
totDegrees g = intersectionWith (+) (inDegrees g) (outDegrees g)

-- deltaGraph construction
outStarG :: Int -> Array Int -> Graph Int
outStarG newId neighbours = connect (vertex newId) (vertices (fromArray neighbours))

-- version required for test case in test/Main.purs
addVertex :: Graph Int -> Int -> Array Int -> Tuple (Graph Int) (Graph Int)
addVertex prevGraph newNodeId neighbours = Tuple diffGraph newGraph
   where
   diffGraph = connect (vertex newNodeId) (vertices (fromArray neighbours))
   newGraph = overlay prevGraph diffGraph

baRunTest :: Int -> Int -> Int -> Map Int Int
baRunTest m t seedI =
   let
      seed = mkSeed seedI
      initGraph = clique (fromArray [ 1, 2, 3, 4 ])
      outGraph = baRunT m t initGraph seed
   in
      totDegrees $ snd outGraph
