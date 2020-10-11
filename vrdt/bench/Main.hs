{-# LANGUAGE BangPatterns #-}
module Main where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (foldM)
import qualified Data.Char as Char
import Data.Fixed
import Data.List (foldl', genericLength, transpose, sort)
import System.CPUTime
import System.Mem
import System.Random
-- import System.TimeIt
import Text.CSV

import Generators
import Types

main :: IO ()
main = do
  -- Benchmark each VRDT.
  benchmarkAndOutput [
      graph0
    --   graph1
    -- , graph2
    -- , graph3
    ]
  
  where
    graph0 = [
        LabeledGenerator "TwoPMap" twoPMapGen
      , LabeledGenerator "MultiSet" multisetGen
      , LabeledGenerator "Baseline (Data.Map)" mapGen
      , LabeledGenerator "CausalTree" causalTreeGen
      , LabeledGenerator "Baseline (Data.List)" listGen
      ]
    graph1 = [
        LabeledGenerator "Min" minGen
      , LabeledGenerator "Max" maxGen
      , LabeledGenerator "LWW" lwwGen
      , LabeledGenerator "Sum" sumGen
      ]
    graph2 = [
        LabeledGenerator "TwoPMap" twoPMapGen
      , LabeledGenerator "MultiSet" multisetGen
      , LabeledGenerator "Baseline (Data.Map)" mapGen
      ]
    graph3 = [
        LabeledGenerator "CausalTree" causalTreeGen
      , LabeledGenerator "Baseline (Data.List)" listGen
      ]

benchmarkAndOutput :: [[LabeledGenerator]] -> IO ()
benchmarkAndOutput = mapM_ benchmarkGraph . zip [0..]

benchmarkGraph :: (Int,[LabeledGenerator]) -> IO ()
benchmarkGraph (graphNum, gens) = do
  putStrLn $ "Generating graph " <> show graphNum

  -- Run benchmarks.
  rs <- flip mapM gens $ \gen -> do
    (label, rs) <- runBenchmark dx c n gen

    -- Write raw output to file.
    writeRaw graphNum label rs

    return (label, transpose rs)

  
  -- Write average, median, quartile 1, quartile 3.
  writeStatistic "mean" average rs
  writeStatistic "median" median rs
  writeStatistic "quartile_1" quartile1 rs
  writeStatistic "quartile_3" quartile3 rs
  

  where
    dx = 1000
    c = 50
    n = 11

    writeRaw :: Int -> String -> [[Nano]] -> IO ()
    writeRaw graphNum label rs = do
      let filename = "raw_" <> show graphNum <> "_" <> labelToName label <> ".csv"
      let header = label:map (show . (dx*)) [1..c]

      let rs' = map (\(trial, r) -> ("Trial " <> show trial):map show r) $ zip [1..] rs
    
      writeFile filename $ printCSV $ header:rs'

    writeStatistic name statF rs = do
      let filename = "graph" <> show graphNum <> "_" <> name <> ".csv"
      let header = name:map (show . (dx*)) [1..c]

      let rs' = map (\(label, rs) -> 
              label:map (show . statF) rs 
            ) rs
  
      writeFile filename $ printCSV $ header:rs'

    -- https://stackoverflow.com/a/2377067/382462
    average xs = sum xs / (genericLength xs * fromIntegral dx)
    median xs = sort xs !! (genericLength xs `div` 2)
    quartile1 xs = sort xs !! (genericLength xs `div` 4)
    quartile3 xs = sort xs !! ((genericLength xs * 3) `div` 4)


labelToName :: String -> String
labelToName = map (\c -> if c == ' ' then '_' else Char.toLower c)

-- Output std dev too?
-- runBenchmark :: Int -> Int -> Int -> LabeledGenerator -> IO [String]
runBenchmark :: Int -> Int -> Int -> LabeledGenerator -> IO (String, [[Nano]])
runBenchmark dx c n (LabeledGenerator label g) = do
  -- Run n times.
  rs <- mapM (run dx c g) [0..n-1]
  -- mapM_ print rs

  return (label, rs)
  
  where
    run dx c g seed = do
      -- Set seed.
      let rng = mkStdGen seed

      -- Init (and force) gen state.
      init <- evaluate $ force $ genInit g

      -- Generate (and force) operations.
      opss <- evaluate $ force $ genOps dx c rng init (gen g)
      -- let opss = genOps dx c rng init (gen g)

      -- print $ map length opss
      -- print opss

      -- Benchmark applying (and forcing) each operation.
      s0 <- evaluate $ force $ initSt g
      app' <- evaluate $ force $ app g
      (reverse . snd) <$> foldM (\(st, acc) ops' -> do
          -- ops <- evaluate $ force ops'
          let ops = ops'

          -- Force GC.
          performMajorGC

          (!runtime, !st') <- timeItT $

            -- Apply (and force) each operation.
            foldM (\ !st !op ->
                evaluate $ force $ app' st op
              ) st ops

          -- print st'
          return (st', runtime:acc)
        ) (s0,[]) opss

    -- Returns ms.
    timeItT m = do
      t0 <- getCPUTime
      res <- m >>= evaluate . force
      tf <- getCPUTime
      return (MkFixed (tf-t0) :: Nano, res) -- Pico for seconds

    -- genOps dx 0 rng st gen = []
    genOps dx c rng st gen = helper dx c $ genOps' rng st gen
    --   -- Generate dx operations.
    --   let (rng', st', ops) = foldl' (\(rng, st, acc) () -> 
    --           let (rng', st', op) = gen rng st in
    --           (rng', st', op:acc)
    --         ) (rng, st, []) $ take dx $ repeat ()
    --   in

    --   reverse ops:genOps dx (c-1) rng' st' gen

    helper dx 0 ops = []
    helper dx c ops = 
      let (ops', rest) = splitAt dx ops in
      ops':helper dx (c-1) rest

    -- Generate an infinite list of ops.
    genOps' rng st gen = 
      let (rng', st', op) = gen rng st in
      op:genOps' rng' st' gen

