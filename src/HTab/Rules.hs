module HTab.Rules
(
Rule(..),
applicableRule, applyRule, ruleToId
) where

import System.Random

import qualified Data.Map as Map

import qualified Data.Set as Set
import Data.Maybe ( mapMaybe )

import HTab.Formula( Formula(..), PrFormula(..), showLess,
                     Dependency, DependencySet, dsUnion, dsInsert,
                     prefix, Rel, negPr,
                     Prefix, Nom, Atom(..),
                     replaceVar, Literal(..))
import HTab.Branch( Branch(..), BranchInfo(..), TodoList(..),
                    -- for rules
                    createNewNode, createNewNom,
                    addFormulas, addAccFormula,
                    addDiaRuleCheck, addToBlockedDias,
                    addDownRuleCheck,
                    doLazyBranching,
                    getUrfatherAndDeps, merge,
                    isNominalUrfather, positiveNomOf,
                    -- for choosing rule in todo list
                    patternBlocked,
                    diaAlreadyDone, downAlreadyDone,
                    -- for rules and choosing rule in todo list
                    reduceDisjunctionProposeLazy, getUrfather,
                    ReducedDisjunct(..)
                    )
import HTab.CommandLine(Params, UnitProp(..),
                        lazyBranching, semBranch, unitProp,
                        strategy, minimal)
import qualified HTab.CommandLine as CL ( random )
import HTab.RuleId(RuleId(..))
import qualified HTab.DisjSet as DS
import Debug.Trace (trace)

-- rule constructors contain the data needed to modify a branch

data Rule =  DiaRule    PrFormula Dependency      -- creates a prefix
           | ExistRule  PrFormula Dependency      -- creates a prefix
           | DisjRule   PrFormula [PrFormula]
           | SemBrRule  PrFormula [PrFormula]
           | LazyBrRule PrFormula Prefix Literal [PrFormula]
           | AtRule     PrFormula
           | DownRule   PrFormula
           | DiscardDownRule PrFormula
           | DiscardDiaDoneRule PrFormula
           | DiscardDiaBlockedRule PrFormula
           | DiscardDisjTrivialRule PrFormula
           | ClashDisjRule DependencySet PrFormula
           | MergeRule Prefix Nom DependencySet
           | RoleIncRule Prefix [Rel] Prefix DependencySet


instance Show Rule where
   show (MergeRule pr n _)                = "merge:              " ++ show (pr, show n)
   show (DiaRule   todelete _ )           = "diamond:            " ++ showLess todelete
   show (DisjRule  todelete _ )           = "disjunction:        " ++ showLess todelete
   show (SemBrRule todelete _ )           = "semantic branching: " ++ showLess todelete
   show (AtRule    todelete )             = "at:                 " ++ showLess todelete
   show (DownRule  todelete )             = "down:               " ++ showLess todelete
   show (ExistRule todelete _ )           = "E:                  " ++ showLess todelete

   show (DiscardDownRule todelete)        = "Discard:            " ++ showLess todelete
   show (DiscardDiaDoneRule todelete)     = "Discard done:       " ++ showLess todelete
   show (DiscardDiaBlockedRule todelete)  = "Discard blocked:    " ++ showLess todelete
   show (DiscardDisjTrivialRule todelete) = "Discard trivial:    " ++ showLess todelete

   show (ClashDisjRule bprs f)     = "Clash:              " ++ show bprs ++ " " ++ show f
   show (RoleIncRule p1 rs p2 _)   = "Role inclusion      " ++ show (p1,rs,p2)
   show (LazyBrRule todelete _ _ _)= "Lazy Branch "         ++ showLess todelete

--
ruleToId :: Rule -> RuleId
ruleToId r = case r of
              (MergeRule _ _ _)  -> R_Merge
              (DiaRule _ _)      -> R_Dia
              (DisjRule _ _)     -> R_Disj
              (SemBrRule _ _)    -> R_SemBr
              (AtRule _ )        -> R_At
              (DownRule _)       -> R_Down
              (ExistRule _ _)    -> R_Exist
              (DiscardDownRule _)        -> R_DiscardDown
              (DiscardDiaDoneRule _)     -> R_DiscardDiaDone
              (DiscardDiaBlockedRule _)  -> R_DiscardDiaBlocked
              (DiscardDisjTrivialRule _) -> R_DiscardDisjTrivial
              (ClashDisjRule _ _)      -> R_ClashDisj
              (RoleIncRule _ _ _ _)    -> R_RoleInc
              (LazyBrRule _ _ _ _)     -> R_LazyBranch

-- the rules application strategy is defined here:
-- the first rule is the one that will be applied at the next tableau step
applicableRule :: Branch -> Params -> Dependency -> StdGen -> Maybe (Rule,Branch, StdGen)
applicableRule br p d g =
 case mapMaybe (ruleByChar br p d g) (strategy p) of  -- TODO weird to use the same g, but right after we only take the first rule
   [] -> Nothing
   ((rule,newtodo,g'):_) -> Just (rule, br{todoList = newtodo}, g')

ruleByChar :: Branch -> Params -> Dependency -> StdGen -> Char -> Maybe (Rule,TodoList, StdGen)
ruleByChar br p d g char =
 case char of
  'n' -> applicableMergeRule
  '|' -> applicableDisjRule
  '<' -> applicableDiaRule
  '@' -> applicableAtRule
  'E' -> applicableExistRule
  'b' -> applicableDownRule
  'r' -> applicableRoleIncRule
  _   -> error "ruleByChar"
 where
  todos  = todoList br

  applicableDiaRule
   = do (f,new) <- Set.minView $ diaTodo todos
        if diaAlreadyDone br f
          then       return ( DiscardDiaDoneRule f,    todos{diaTodo = new}, g)
          else
           if patternBlocked br f
             then return ( DiscardDiaBlockedRule f, todos{diaTodo = new}, g)
             else return ( DiaRule f d,             todos{diaTodo = new}, g)
  applicableAtRule    = do (f,new) <- Set.minView $ atTodo todos
                           return (AtRule f, todos{atTodo = new}, g)

  applicableDownRule  = do (f,new) <- Set.minView $ downTodo todos
                           if downAlreadyDone br f
                            then return (DiscardDownRule f, todos{downTodo = new}, g)
                            else return (DownRule f, todos{downTodo = new}, g)

  applicableExistRule = do (f,new) <- Set.minView $ existTodo todos
                           return (ExistRule f d, todos{existTodo = new}, g)
  applicableRoleIncRule
   = do ((ds, p1, p2, rs),new) <- Set.minView $ roleIncTodo todos
        return (RoleIncRule p1 rs p2 (dsInsert d ds), todos{roleIncTodo = new}, g)

  applicableMergeRule  = do ((ds,pr,n),new) <- Set.minView $ mergeTodo todos
                            return (MergeRule pr n ds, todos{mergeTodo = new}, g)
  applicableDisjRule
   = case unitProp p of
      Eager -> {- scan all disjuncts until one can be discarded,
                  reduced to one disjunct or clashes -}
          case mapMaybe (makeInteresting p br d) $ Set.toList $ disjTodo todos of
            ((r,pf):_) -> return (r, todos{disjTodo = Set.delete pf $ disjTodo todos}, g)
            [] -> regularApplicableDisjRule
         -- todo: update counter (CurCount, MaxCount) step 10
         -- to space out unit propagation lookup
      _     ->  regularApplicableDisjRule
  regularApplicableDisjRule
      | not (CL.random p)
          = do (f,new) <- Set.minView $ disjTodo todos
               return (disjRule p f br d, todos{disjTodo = new}, g)
      | otherwise
          = if Set.null s then Nothing
             else let (n, g') = randomR (0, Set.size s - 1) g
                      f = Set.elemAt n s  -- pick formula
                      new = Set.deleteAt n s -- remove from Set
                  in  Just (disjRule p f br d, todos{disjTodo = new}, g')
           where s = disjTodo todos

makeInteresting :: Params -> Branch -> Dependency -> PrFormula ->  Maybe (Rule,PrFormula)
makeInteresting p br d df@(PrFormula pr spr ds (Dis fs))
 = case reduceDisjunctionProposeLazy br pr fs of
          Triviality               -> Just (DiscardDisjTrivialRule df,df)
          Contradiction ds_clash   -> Just (ClashDisjRule (dsUnion ds ds_clash) df,df)
          Reduced new_ds disjuncts mProposed
           | Set.size disjuncts == 1
              -> Just (DisjRule df ( prefix spr ur newDeps disjuncts ), df)
           | lazyBranching p
              -> case mProposed of
                  Nothing  -> Nothing
                  Just lit
                   -> Just (LazyBrRule df ur lit [PrFormula ur spr newDeps (Dis disjuncts)],
                            df)
           | otherwise  -> Nothing
             where newDeps = dsInsert d $ dsUnion ds new_ds
                   ur = getUrfather br (DS.Prefix pr)
           -- TODO should not insert d if the formula was actually not changed
              -- --> reduceDisjunctionProposeLazy should return a boolean
              -- -->  or have a constructor "Unchanged" ?

makeInteresting _ _ _ _ = error "makeInteresting on a non disjunction"


(>>?) :: BranchInfo -> (Branch -> BranchInfo) -> BranchInfo
clash@(BranchClash _ _ _ _) >>? _ = clash
(BranchOK br) >>? f = f br

applyRule :: Params -> Rule -> Branch -> StdGen -> ([BranchInfo], StdGen)
applyRule p rule br g
 = trace ("se ejecuto applyRule con: " ++ show rule) $
   case rule of
    DiaRule (PrFormula pr spr ds (Dia r f)) d -- here, if minimal, branch on all prefixes
     | minimal p -> if CL.random p then shuffle g choices else (choices, g)
     | otherwise -> (properNewBranch, g)
          where
                tryAllPrefixes = map reusePrefix $ filter (isNominalUrfather br) [0..lastPref br]
                reusePrefix pr' = case r of
                  "R0" ->
                    trace ("  -> Blocking: L intenta reusar el mundo " ++ show pr') $
                    addAccFormula p (dsInsert d (dsUnion ds ds2), "R0", ur, pr') br >>?
                    addFormulas p [PrFormula pr' spr (dsInsert d ds) f] >>?
                    addDiaRuleCheck pr spr (r,f) pr'
                  "R1" ->
                    trace("  -> Blocking: R intenta reusar el mundo " ++ show pr') $
                    addAccFormula p (dsInsert d (dsUnion ds sds2), "R0", sur, pr') br >>?
                    addFormulas p [PrFormula pr pr' (dsInsert d ds) f] >>?
                    addDiaRuleCheck pr spr (r,f) pr'
                  _ -> error "Syntaxis error on diamonds"
                properNewBranch = case r of
                  "R0" ->
                    trace "Aplicando regla diamante para L"
                    [ createNewNode p br >>?
                      addAccFormula p (depsL, "R0", ur, newPr) >>?
                      addFormulas p [PrFormula newPr spr ds f] >>?
                      addDiaRuleCheck pr spr (r,f) newPr
                    ]
                  "R1" ->
                    trace "Aplicando regla diamante para R"
                    [ createNewNode p br >>?
                      addAccFormula p (depsR, "R0", sur, newPr) >>?
                      addFormulas p [PrFormula pr newPr ds f] >>?
                      addDiaRuleCheck pr spr (r,f) newPr
                    ]
                  _ -> error "Syntaxis error on diamonds"
                depsL = if CL.random p && minimal p then dsInsert d (dsUnion ds ds2) else dsUnion ds ds2
                depsR = if CL.random p && minimal p then dsInsert d (dsUnion ds sds2) else dsUnion ds sds2
                choices = tryAllPrefixes ++ properNewBranch
                newPr      = lastPref br + 1
                (ur,ds2,_) = getUrfatherAndDeps br (DS.Prefix pr)
                (sur,sds2,_) = getUrfatherAndDeps br (DS.Prefix spr)
    ExistRule (PrFormula _ spr ds (E f2)) d -- here, if minimal, branch on all prefixes
     | minimal p -> if CL.random p then shuffle g choices else (choices, g)
     | otherwise -> (properNewBranch, g)
       where
             tryAllPrefixes = map reusePrefix $ filter (isNominalUrfather br) [0..lastPref br]
             reusePrefix pr' = addFormulas p [PrFormula pr' spr (dsInsert d ds) f2] br
             properNewBranch = [createNewNode p br >>? addFormulas p [PrFormula newPr spr deps f2]]
             deps = if CL.random p && minimal p then dsInsert d ds else ds
             choices = tryAllPrefixes ++ properNewBranch
             newPr = lastPref br + 1

    DisjRule _ prFormulas
     | CL.random p -> shuffle g choices
     | otherwise -> (choices, g)
     where choices = [ addFormulas p [toadd] br |  toadd <- prFormulas ]
    SemBrRule _ prFormulas
     | CL.random p  -> shuffle g choices
     | otherwise -> (choices, g)
             where
              choices = [ addFormulas p toadds br |  toadds <- go prFormulas [] ]
              go (hd:tl) negs = (hd:negs):(go tl (negPr hd:negs))
              go [] _ = []
    LazyBrRule _ pr lit prFormulas ->
            ([ doLazyBranching pr lit prFormulas br ], g)
    AtRule  (PrFormula _ spr ds (At n f)) ->
            ([ addFormulas p [toadd] br{ nomPrefClasses = equiv }], g)
            where (ur,ds2,equiv) = getUrfatherAndDeps br (DS.Nominal n)
                  toadd = PrFormula ur spr (dsUnion ds ds2) f
    DownRule (PrFormula pr spr ds f@(Down v f2)) ->
                 case positiveNomOf br pr of -- reuse positive nominal if we can
                  Nothing -> ( [ createNewNom br >>?
                                 addFormulas p [toadd1, toadd2] >>?
                                 addDownRuleCheck pr f ],               g)
                    where toadd1 = PrFormula pr spr ds (replaceVar v newNom f2)
                          toadd2 = PrFormula pr spr ds $ Lit $ PosLit $ N newNom
                          newNom = '_':(show $ nextNom br)
                  Just n' ->
                   ( [ addFormulas p [PrFormula pr spr ds (replaceVar v n' f2)] br >>?
                       addDownRuleCheck pr f ], g)
    DiscardDownRule _         -> ([BranchOK br], g)
    DiscardDiaDoneRule _      -> ([BranchOK br], g)
    DiscardDisjTrivialRule _  -> ([BranchOK br], g)
    DiscardDiaBlockedRule f   -> ([addToBlockedDias f br], g)

    ClashDisjRule ds (PrFormula pr spr ds2 f) -> ([BranchClash br pr (dsUnion ds ds2) f], g)
    MergeRule pr n ds -> ([merge p pr ds n br], g)
    RoleIncRule p1 rs p2 ds ->
     ([addAccFormula p (ds, r, p1, p2) br | r <- rs], g)
    _ -> error $ "applyRule with bad argument: " ++ show rule

disjRule :: Params -> PrFormula -> Branch -> Dependency -> Rule
disjRule p df@(PrFormula pr spr ds (Dis fs)) br d
  = if unitProp p == UPNo
     then rule df $ prefix pr spr (dsInsert d ds) fs
     else case reduceDisjunctionProposeLazy br pr fs of
             Triviality               -> DiscardDisjTrivialRule df
             Contradiction ds_clash   -> ClashDisjRule (dsUnion ds ds_clash) df
             Reduced new_ds disjuncts _
               -> rule df (prefix pr spr (dsInsert d $ dsUnion ds new_ds) disjuncts)
    where rule = if semBranch p then SemBrRule else DisjRule
-- todo: if only one conjunct remaining, do not add d , but still create a DisjRule
disjRule _ _ _ _ = error "disjRule"


-- list shuffler
-- http://okmij.org/ftp/Haskell/perfect-shuffle.txt 

fisherYatesStep :: RandomGen g => (Map.Map Int a, g) -> (Int, a) -> (Map.Map Int a, g)
fisherYatesStep (m, gen) (i, x) = ((Map.insert j x . Map.insert i (m Map.! j)) m, gen')
  where
    (j, gen') = randomR (0, i) gen

shuffle :: RandomGen g => g -> [a] -> ([a], g)
shuffle gen [] = ([], gen)
shuffle gen l =
  toElems $ foldl fisherYatesStep (initial (head l) gen) (numerate (tail l))
  where
    toElems (x, y) = (Map.elems x, y)
    numerate = zip [1..]
    initial x gen' = (Map.singleton 0 x, gen')

