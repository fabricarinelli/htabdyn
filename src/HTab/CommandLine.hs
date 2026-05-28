{-# OPTIONS_GHC -fno-warn-missing-fields #-}
module HTab.CommandLine (
    Params(..), UnitProp(..),
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
           lazyBranching   :: Bool,
           unitProp        :: UnitProp,
           showFormula     :: Bool,
           allTransitive   :: Bool,
           allReflexive    :: Bool
         , translate       :: Bool
         , minimal         :: Bool
         , random          :: Bool
         , seed            :: Maybe Int
         , test_translations :: Bool
         } deriving (Show, Data, Typeable)

data UnitProp = UPYes | Eager | UPNo deriving (Data, Typeable, Eq, Show)

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
       lazyBranching  := True    += help "enable lazy branching (default)" ,
       unitProp `enum_` [atom UPYes += explicit += name "unit-prop"    += help "unit propagation on selected disjunction (default)",
                         atom Eager += explicit += name "eager"        += help "unit propagation on all disjunctions",
                         atom UPNo  += explicit += name "no-unit-prop" += help "unit propagation disabled"] ,
       showFormula    := False   += help "display formula",
       allTransitive  := False   += help "make all relations transitive",
       allReflexive   := False   += help "make all relations reflexive",
       translate      := False   += help "translate relation-changing formulas to hybrid",
       minimal        := False   += help "look for minimal model (slow)",
       random         := False   += help "randomly select next disjunctive formula, also randomize disjuncts",
       seed           := Nothing += help "set random seed (integer)",
       test_translations := False   += help "run the memory-to-relation-changing test suite"
      ] += verbosity

strategyVal :: String
strategyVal = "n@E<b|r"

checkParams :: Params -> IO Bool
checkParams p
 | strategy p `notPermutationOf` strategyVal =
    do putStrLn
        $ unlines ["ERROR",
                   "strategy should contain all of the following characters: ",
                   "  n = nominals               @ = satisfaction operator",
                   "  E = existential modality   < = diamond",
                   "  b = down-arrow binder      | = or",
                   "  r = role inclusion",
                   "",
                   "The default is \"" ++ strategyVal ++ "\"",
                   "The rules conjunction, box, and universal modality",
                   "are applied immediately, thus do not belong to the strategy."]
       return False
 | null (filename p) && not (test_translations p)=
    do putStrLn $ unlines ["ERROR: No input specified.","Run with --help for usage options"]
       return False
 | translate p && (allTransitive p || allReflexive p) = 
    do putStrLn $ unlines ["ERROR: --translate incompatible with --all-transitive or --all-reflexive."]
       return False
 | otherwise = return True
  where notPermutationOf l1 l2 = sort l1 /= sort l2

configureStats :: Params -> StatisticsState ()
configureStats p = setPrintOutInterval $ stats p
