module Main where

import Prelude

import Algebra.Graph (clique)
import Algebra.Graph.Internal (fromArray)
import Data.Array (range)
import Data.Int (fromString)
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Effect (Effect)
import Effect.Class.Console (logShow)
import Effect.Console (log)
import Graph.Utils.Run (baRunT, totDegrees)
import Node.ReadLine (createConsoleInterface, noCompletion, prompt, setLineHandler, setPrompt, close, question)
import Random.PseudoRandom (mkSeed)

main :: Effect Unit
main = do
   inputInterface <- createConsoleInterface noCompletion
   setPrompt "> " inputInterface
   prompt inputInterface
   log "Begin test?"
   inputInterface # setLineHandler \s ->
      if s == "quit" then
         close inputInterface
      else do
         inputInterface # question "How many initial nodes do you want? " \initN -> do
            let
               list = case fromString initN of
                  Just n -> fromArray $ range 1 n
                  Nothing -> fromArray $ range 1 10

               initGraph = clique list
            -- log "T = 0"
            -- logShow (totDegrees initGraph)
            inputInterface # question "How many edges will a new node be connected to? " \m -> do
               inputInterface # question "What is the seed for random number generation? " \inpSeed -> do
                  let
                     initSeed = mkSeed case fromString inpSeed of
                        Just n -> n
                        Nothing -> 1234598134
                  inputInterface # question "How many timesteps should the code run for? " \t -> do
                     let
                        m' = case fromString m of
                           Just n' -> n'
                           Nothing -> 3
                        t' = case fromString t of
                           Just k' -> k'
                           Nothing -> 20
                        graphOne = baRunT m' t' initGraph initSeed
                        graphTwo = baRunT m' t' initGraph initSeed
                     log ("T = " <> t)
                     logShow (totDegrees $ fst graphOne)
                     logShow (graphTwo == graphOne)
                     log "Test complete, start again?"
--printGraph (snd graphOne)
