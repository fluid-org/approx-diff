{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
module Main where
{-# LANGUAGE DuplicateRecordFields #-}


import Data.Graph
import Data.List (elemIndices)
import Text.Read hiding (lift)
import Control.Monad
import Data.Functor.Identity
import Control.Monad.Trans
import Control.Applicative
import Data.Char (isAlpha, isNumber, isPunctuation)
import GHC.Arr
import System.Random
import Control.Monad.Trans.State.Lazy
type EdgeList = [(Int, Int)]


main :: IO Graph
main = do
    putStrLn "How many nodes does your graph have? "
    max <- read <$> getLine 
    putStrLn "Input your edges: "
    let edges = graphBuild
    let out = buildG (0, max) <$> edges
    out


graphBuild :: IO EdgeList
graphBuild = graphBuildInner []

-- Initial construction with single monad
graphBuildInner :: EdgeList -> IO EdgeList
graphBuildInner g = do
    putStrLn "Edge source:"
    source <- read <$> getLine
    putStrLn "Edge sink: "
    sink <- read <$> getLine
    let edge = (source, sink) :: (Int, Int)
    if edge == (0,0) then 
        pure g
    else
        graphBuildInner (g ++ [edge])

probsToArray :: [Float] -> (Int, Int) -> Array Int Float
probsToArray list bounds = listArray bounds list

probsToEdges :: Int -> [Bool] -> [(Int, Int)]
probsToEdges newId flags = 
    let edgeIds = elemIndices True flags in
    map (\x -> (newId, x)) edgeIds

-- StateT Graph IO [(Int, Int)]
baUpdate :: StateT Graph IO [Edge]
baUpdate = do 
    g <- Control.Monad.Trans.State.Lazy.get 
    
    let vertId = (length . vertices) g
        normalizer :: Float
        normalizer = fromIntegral (((* 2) . length . edges) g)
        probs = fmap (\deg -> fromIntegral deg / normalizer) (arraySum (indegree g) (outdegree g))
        probsL = elems probs
    
    randoms <- replicateM (vertId - 1) (randomIO :: StateT Graph IO Float)
    
    let prPairs = zip randoms probsL
        newEdgeFlags = map (uncurry (<)) prPairs
        newEdges = probsToEdges vertId newEdgeFlags
        newEdges' = edges g ++ newEdges     -- These 2 lines may need to be changed 
        newG = buildG (0, vertId) newEdges' --
    put newG
    return newEdges

-- Barabasi-Albert Model will use StateT around IO, soon
barabasiAlbert :: Graph -> Int -> IO ([[(Int, Int)]], Graph)
barabasiAlbert g i = 
    runStateT (replicateM i baUpdate) g

-- Does slightly invite the question of why we need the state in this scenario

arraySum :: Array Vertex Int -> Array Vertex Int -> [Int]
arraySum a1 a2 =
    zipWith (+) (elems a1) (elems a2)