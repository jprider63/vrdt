{-# LANGUAGE BangPatterns #-}
module Main where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (foldM)
import Data.Fixed
import Data.List (foldl', genericLength, transpose)
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
      graph1
    ]
  
  
  where
    graph1 = [
        LabeledGenerator "Min" minGen
      , LabeledGenerator "Max" maxGen
      , LabeledGenerator "LWW" lwwGen
      , LabeledGenerator "Sum" sumGen
      ]

benchmarkAndOutput :: [[LabeledGenerator]] -> IO ()
benchmarkAndOutput = mapM_ benchmarkGraph . zip [0..]

benchmarkGraph :: (Int,[LabeledGenerator]) -> IO ()
benchmarkGraph (graphNum, gens) = do
  putStrLn $ "Generating graph " <> show graphNum

  -- Run benchmarks.
  let dx = 1000
  let c = 10
  let n = 20
  rs <- mapM (runBenchmark dx c n) gens

  -- Write to file
  let filename = "graph" <> show graphNum <> ".csv"
  let header = "":map (show . (dx*)) [1..c]

  writeFile filename $ printCSV $ header:rs



-- Output std dev too?
-- runBenchmark :: Int -> Int -> Generator t op st -> [String] -- (String, [Double])
runBenchmark :: Int -> Int -> Int -> LabeledGenerator -> IO [String] -- (String, [Double])
runBenchmark dx c n (LabeledGenerator label g) = do
  -- Run n times.
  rs <- mapM (run dx c g) [0..n-1]
  mapM_ print rs
  
  -- Compute averages.
  let avgs = map average $ transpose rs

  -- stdev??

  return $ label:map show avgs

  where
    -- https://stackoverflow.com/a/2377067/382462
    average xs = sum xs / (genericLength xs * fromIntegral dx)

    run dx c g seed = do
      -- Set seed.
      let rng = mkStdGen seed

      -- Init (and force) gen state.
      init <- evaluate $ force $ genInit g

      -- Generate (and force) operations.
      opss <- evaluate $ force $ genOps dx c rng init (gen g)
      -- let opss = genOps dx c rng init (gen g)

      print $ map length opss
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

          print st'
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

