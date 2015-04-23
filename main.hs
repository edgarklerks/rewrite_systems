module Main where

import RewriteSystem
import Data.Graph.Analysis.Algorithms
import Control.DeepSeq

main :: IO ()
main = do
   let ts = transformSystem (initialAxiom "tppqtpqtp") cyclicSystem  (Just 4)
   print (rnf ts)

   _ <-  toDotWith coreOf ts "core.dot"
   _ <-  saveAsXDot "core.dot" ts 
   return ()
