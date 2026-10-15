{-# OPTIONS_GHC -fno-warn-missing-fields #-}
module HTab.CommandLine (
    Params(..),
    defaultParams, configureStats, checkParams
) where

import System.Console.CmdArgs
import Data.List ( sort )
import HTab.Statistics( StatisticsState, setPrintOutInterval )

data Params = Params {
           filename        :: FilePath,
           genModel        :: Maybe FilePath,
           dotModel        :: Bool,
           timeout         :: Int,
           stats           :: Int,
           strategy        :: String,
           semBranch       :: Bool,
           backjumping     :: Bool,
           patternBlocking :: Bool,
           showFormula     :: Bool,
           minimal         :: Bool,
           random          :: Bool,
           seed            :: Maybe Int
         } deriving (Show, Data, Typeable)


defaultParams :: Annotate Ann
defaultParams
 = record Params{}
     [ filename       := "" += name "f" += typFile += help "input file",
       genModel       := Nothing += name "m" += typFile += help "output model file",
       dotModel       := False   += help "output model in dot format (otherwise: hylolib format)",
       timeout        := 0       += name "t" += help "timeout (in seconds, default=none)",
       stats          := 0       += help "display statistics every n steps (default=none)",
       strategy       := strategyVal += help "specify rule order",
       semBranch      := True    += help "enable semantic branching (default)",
       backjumping    := True    += help "enable backjumping (default)",
       patternBlocking:= False   += help "enable patternBlocking (default False)",
       showFormula    := False   += help "display formula",
       minimal        := False   += help "look for minimal model (slow)",
       random         := False   += help "randomly select next disjunctive formula, also randomize disjuncts",
       seed           := Nothing += help "set random seed (integer)"
      ] += verbosity

strategyVal :: String
strategyVal = "n<|"

checkParams :: Params -> IO Bool
checkParams p
 | strategy p `notPermutationOf` strategyVal =
    do putStrLn
        $ unlines ["ERROR",
                   "strategy should contain all of the following characters: ",
                   "  n = nominals",
                   "  < = diamond",
                   "  | = or",
                   "",
                   "The default is \"" ++ strategyVal ++ "\"",
                   "The rules conjunction and box",
                   "are applied immediately, thus do not belong to the strategy."]
       return False
 | null (filename p)=
    do putStrLn $ unlines ["ERROR: No input specified.","Run with --help for usage options"]
       return False
 | otherwise = return True
  where notPermutationOf l1 l2 = sort l1 /= sort l2

configureStats :: Params -> StatisticsState ()
configureStats p = setPrintOutInterval $ stats p
