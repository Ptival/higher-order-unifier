module Main where

import GHC.Exception (prettyCallStack)
import Unifier (runUnifier)
import Unifier.Types (Term (Constant))

main :: IO ()
main = do
  (res, _) <- runUnifier (Constant "A") (Constant "A")
  case res of
    Left cs -> do
      putStrLn "Failure!"
      putStrLn $ prettyCallStack cs
    Right r -> do
      putStrLn "Success!"
      print r
