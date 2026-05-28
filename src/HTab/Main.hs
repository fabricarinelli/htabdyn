module HTab.Main

( runWithParams, TaskRunFlag(..))

where
import Control.Monad       ( when, forM_ )
import Control.Monad.State( runStateT )

import Data.List ( intersperse )
import qualified Data.Map as Map
import System.Console.CmdArgs ( whenNormal, whenLoud )
import System.CPUTime( getCPUTime )
import qualified System.Timeout as T
import System.Random (StdGen, getStdGen, mkStdGen)
import System.IO.Strict ( readFile )
import Prelude hiding ( readFile )

import HyLo.InputFile.Parser ( QueryType(..) )

import HTab.CommandLine( filename, random, seed, test_translations,
                         timeout, Params, genModel, dotModel, showFormula )
import HTab.Branch( BranchInfo(..), initialBranch)
import HTab.Statistics( Statistics, initialStatisticsStateFor, printOutMetricsFinal )
import HTab.Tableau( OpenFlag(..), tableauStart )
import HTab.Formula( Theory, RelInfo, LanguageInfo(..), Task,
                     Formula(Con), encodeValidityTest, encodeSatTest, encodeRetrieveTask,
                     showRelInfo, list )
import HTab.Memory (unsats, sats)
import qualified HTab.Formula as F
import qualified HyLo.Signature.String as S
import HTab.ModelGen ( Model, toDot )

data TaskRunFlag = SUCCESS | FAILURE

runWithParams :: Params -> IO (Maybe TaskRunFlag)
runWithParams p | test_translations p =
 do putStrLn "Running memory logic to relation-changing logics test suite."
    g <- case seed p of
        Nothing -> getStdGen
        Just s  -> do putStrLn "Using given random seed."
                      return (mkStdGen s)
    putStrLn "=== UNSAT formulas ==="
    forM_ (zip [1::Int ..] unsats) $ \(i,(mf,rc,h,name)) ->
        do myPutStrLn (show i ++ " " ++ show mf ++ " via " ++ name)
           r <- inTimeout (timeout p) $
                  do (result,_) <- tableauInit p g $ initialBranch p (LanguageInfo []) Map.empty h
                     return result
           case r of
            Nothing         -> myPutStrLn "Timeout"
            Just (CLOSED _) -> myPutStrLn "OK"
            Just (OPEN _)   -> myPutStrLn ("ERROR: formula is sat\n" ++ show rc)
    putStrLn "=== SAT formulas ==="
    forM_ (zip [(length unsats + 1)::Int ..] sats) $ \(i,(mf,rc,h,name)) ->
        do myPutStrLn (show i ++ " " ++ show mf ++ " via " ++ name)
           r <- inTimeout (timeout p) $
                  do (result,_) <- tableauInit p g $ initialBranch p (LanguageInfo []) Map.empty h
                     return result
           case r of
            Nothing         -> myPutStrLn "Timeout"
            Just (OPEN _)   -> myPutStrLn "OK"
            Just (CLOSED _) -> myPutStrLn ("ERROR: formula is unsat\n" ++ show rc)
    return (Just SUCCESS)

runWithParams p =
 time "Total time: " $ do
  g <- case seed p of
        Nothing -> getStdGen
        Just s  -> do putStrLn "Using given random seed."
                      return (mkStdGen s)
  when (random p) $ putStrLn ( unlines ["Will use random seed:",show g])
  i <- readFile (filename p)
  if head (words i) == "begin"
   then do
    let (f,relInfo,fLang) = F.simpleParse p i
    when (showFormula p) $
     myPutStrLn $
      unlines ["Input for SAT test:",
               "{ " ++ show f ++ " }",
               "End of input",
               "Relations properties :" ++ showRelInfo relInfo ]
    --
    tResult <- inTimeout (timeout p) $
                do (result,s) <- tableauInit p g $
                                  initialBranch p fLang relInfo f
                   whenNormal $ printOutMetricsFinal s
                   return result
    --
    case tResult of
       Nothing         -> do myPutStrLn "\nTimeout.\n" >> return Nothing
       Just (OPEN m)   -> do myPutStrLn "The formula is satisfiable."
                             saveGenModel (genModel p) p m
                             return (Just SUCCESS)
       Just (CLOSED _) -> do myPutStrLn "The formula is unsatisfiable."
                             return (Just FAILURE)
   else do
    let allTasks = F.parse p i
    result <- inTimeout (timeout p) (runTasks allTasks p g)
    --
    case result of
       Nothing      -> myPutStrLn "\nTimeout.\n"
       Just SUCCESS -> myPutStrLn "\nAll tasks successful.\n"
       Just FAILURE -> myPutStrLn "\nOne task failed.\n"
    --
    return result

inTimeout :: Int -> IO a -> IO (Maybe a)
inTimeout 0 action = Just <$> action
inTimeout t action = T.timeout (t * (10::Int)^(6::Int)) action

--

runTasks :: (Theory,RelInfo,LanguageInfo,[Task]) -> Params -> StdGen -> IO TaskRunFlag
runTasks allTasks@(theory,relInfo,fLang,tasks) p g =
 do
    myPutStrLn "== Checking theory satisfiability =="
    res <- time "Task time:" $
            runTask (Satisfiable, genModel p, []) relInfo fLang theory p g
    case res of
     SUCCESS | null tasks -> return SUCCESS
             | otherwise  -> do myPutStrLn "\n==         Starting tasks         =="
                                res2 <- runTasks2 allTasks p g
                                myPutStrLn "\n==         End of   tasks         =="
                                return res2
     FAILURE              -> return FAILURE

--

runTasks2 :: (Theory,RelInfo,LanguageInfo,[Task]) -> Params -> StdGen -> IO TaskRunFlag
runTasks2 (_,_,_,[]) _ _               = error "runTasks2 empty list error"
runTasks2 (theory,relInfo,fLang,(hd:tl)) p g =
 do res <- time "Task time:" $ runTask hd relInfo fLang theory p g
    case res of
      SUCCESS | null tl   -> return SUCCESS
              | otherwise -> runTasks2 (theory,relInfo,fLang,tl) p g
      FAILURE             -> do _ <- runTasks2 (theory,relInfo,fLang,tl) p g
                                return FAILURE

--

runTask :: Task -> RelInfo -> LanguageInfo -> Formula -> Params -> StdGen -> IO TaskRunFlag
runTask (Retrieve,mOutFile,fs) relInfo fLang theory p g =
 do myPutStrLn "\n* Instance retrieval task"
    let (noms,encfs) = encodeRetrieveTask relInfo fLang theory fs
    --
    myPutStrLn $ "Instances making true: " ++ show fs
    --
    results <- mapM (tableauInit p g . initialBranch p fLang relInfo) encfs -- NOTE: we reuse the same random generator
    let goods = [ S.NomSymbol n | (n,(CLOSED _ ,_)) <- zip noms results]
    myPutStrLn $ show goods
    let doWrite f = do writeFile f (show goods ++ "\n")
                       myPutStrLn ("Nominals saved as " ++ f)
    maybe (return ()) doWrite mOutFile
    return SUCCESS

runTask (Satisfiable,mOutFile,fs) relInfo fLang theory p g =
 do myPutStrLn "\n* Satisfiability task"
    let f = encodeSatTest relInfo theory fs
    --
    let f_lines = case f of
                   Con cs -> list cs
                   _ -> [f]
    when (showFormula p) $
     myPutStrLn $ unlines $ ["Input for SAT test:",
                           "{"] ++ intersperse "" (map show f_lines) ++
                           ["}", "End of input",
                           "Relations properties :" ++ showRelInfo relInfo ]
    --
    (result,stats) <- tableauInit p g $ initialBranch p fLang relInfo f
    --
    whenNormal $ printOutMetricsFinal stats
    --
    case result of
       OPEN m   -> do myPutStrLn "The formula is satisfiable."
                      saveGenModel mOutFile p m
                      return SUCCESS
       CLOSED _ -> do myPutStrLn "The formula is unsatisfiable."
                      return FAILURE

runTask (Valid,mOutFile,fs) relInfo fLang theory p g =
 do myPutStrLn "\n* Validity task"
    let f = encodeValidityTest relInfo theory fs
    --
    when (showFormula p) $
     myPutStrLn $ unlines ["Input for SAT test:",
                           "{ " ++ show f ++ " }",
                           "End of input",
                           "Relations properties :" ++ showRelInfo relInfo ]
    --
    (result,stats) <- tableauInit p g $ initialBranch p fLang relInfo f
    --
    whenNormal $ printOutMetricsFinal stats
    --
    case result of
       OPEN m   -> do myPutStrLn "The formula is not valid."
                      saveGenModel mOutFile p m
                      return FAILURE
       CLOSED _ -> do myPutStrLn "The formula is valid."
                      return SUCCESS

runTask (Counting,_,_) _ _ _ _ _ =
 do myPutStrLn "\n* Counting task is NOT supported"
    return FAILURE

--

saveGenModel :: Maybe FilePath -> Params -> Model -> IO ()
saveGenModel mOutFile p m = maybe (return ()) doWrite mOutFile
    where doWrite f = do writeFile f output
                         myPutStrLn ("Model saved as " ++ f)
          output | dotModel p = toDot m
                 | otherwise  = show m

tableauInit :: Params -> StdGen -> BranchInfo -> IO (OpenFlag,Statistics)
tableauInit p g bi =
        do whenLoud $ putStrLn ">> Starting rules application"
           initStatsState $ tableauStart p bi
 where initStatsState  = initialStatisticsStateFor runStateT g

--

time :: String -> IO a -> IO a
time message action =
  do start  <- getCPUTime
     result <- action
     end <- getCPUTime
     let elapsedTime = fromInteger (end - start) / 1000000000000.0
     myPutStrLn $ message ++ show (elapsedTime :: Double)
     return result


myPutStrLn :: String -> IO ()
myPutStrLn str = whenNormal $ putStrLn str

