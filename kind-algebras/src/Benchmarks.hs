module Main where

import Criterion.Main

import Generics.Kind.RecursorSimpleGADTs

main :: IO ()
main = defaultMain [
  bgroup "algebra"
    [ bench "1"     $ nf applyLengthList [0..1]
    , bench "10"    $ nf applyLengthList [0..10]
    , bench "100"   $ nf applyLengthList [0..100]
    , bench "1000"  $ nf applyLengthList [0..1000]
    , bench "10000" $ nf applyLengthList [0..10000]
    ],
  bgroup "direct"
    [ bench "1"     $ nf length [0..1]
    , bench "10"    $ nf length [0..10]
    , bench "100"   $ nf length [0..100]
    , bench "1000"  $ nf length [0..1000]
    , bench "10000" $ nf length [0..10000]
    ],
  bgroup "foldr"
    [ bench "1"     $ nf lengthViaFoldr [0..1]
    , bench "10"    $ nf lengthViaFoldr [0..10]
    , bench "100"   $ nf lengthViaFoldr [0..100]
    , bench "1000"  $ nf lengthViaFoldr [0..1000]
    , bench "10000" $ nf lengthViaFoldr [0..10000]
    ]
  ]
  where lengthViaFoldr :: [Int] -> Int
        lengthViaFoldr = foldr (+) 0