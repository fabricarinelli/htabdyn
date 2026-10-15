module HTab.Branch
(
Branch(..), BranchInfo(..), TodoList(..),
createNewNode, createNewNom,
addFormulas, addAccFormula,
addToBlockedDias,
addDiaRuleCheck,
initialBranch,
merge,
getUrfather, getUrfatherAndDeps,
getModelRepresentative, patternBlocked,
diaAlreadyDone,
patternOf, findByPattern,
prefixes, isNominalUrfather, isInTheModel,
positiveNomOf
) where

import Data.Maybe( mapMaybe )

import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set
import Data.IntMap ( IntMap)
import qualified Data.IntMap as I

import qualified HTab.DMap as D
import qualified HTab.DisjSet as DS
import HTab.CommandLine(Params(..))
import HTab.Formula hiding ( list )
import HTab.Relations ( OutRels, emptyRels, insertRelation, mergePrefixes,
                        successors, showRels, mergeInnerLists )
import HTab.Literals ( UpdateResult(..), Literals,
                       SlotUpdateResult(..), LiteralSlot,
                       updateMap, lsUnions, lsAddDeps, lsQuery,
                       positiveNom)

data BranchInfo = BranchOK Branch |
                  BranchClash Branch Prefix DependencySet Formula

type BoxConstraints     = IntMap {- Prefix -} [((Formula,Prefix,Rel),DependencySet)]
type EquivClasses = DS.DisjSet DS.Pointer

data Branch =
              Branch {
                 -- the premodel
                      literals :: Literals,
                        accStr :: OutRels,
                 -- local and global constraints
                        boxFwd :: BoxConstraints,
                 -- pending formulas / todo lists
                      todoList :: TodoList,
                 -- saturation of rules
                       diaRlCh :: IntMap {- Prefix -} (Set (Prefix,Rel,Formula)),
                 -- pattern blocking
                      patterns :: IntMap (Set Formula),
                 -- backjumping data attached to equivalence classes
                    prToDepSet :: IntMap {- Prefix -} DependencySet,
                 -- prefix/nominal equivalence classes
                nomPrefClasses :: EquivClasses,
                 -- book keeping
                      lastPref :: Prefix,
                       nextNom :: Int,
                 -- information about language of input formula and blocking mode
                 inputLanguage :: LanguageInfo,
                   blockedDias :: IntMap {- Prefix -} [PrFormula],
                       relInfo :: RelInfo}

--

instance Show Branch where
 show br = concat
  [  show (inputLanguage br),
     "\nLiterals:", showIMap (\v -> "(" ++ showMap_lits v ++ ")") "\n " (literals br),
     "\nRelations: ", showRels (accStr br),
     "\nBoxes: ", showIMap (\v -> "(" ++ showMap_rel v ++ ")") "\n " (boxFwd br),
     "\n", showTodo (todoList br),
     "\nDia rule chart: ", show (diaRlCh br),
     "\nIndividual patterns: ", show (patterns br),
     "\nPrefix to dependency set: ", showIMap  dsShow "\n " (prToDepSet br),
     "\nPrefix-Nominal classes : ", showMap ", " (nomPrefClasses br),
     "\nlastPref : ", show (lastPref br),
     " nextnom : ", show (nextNom br),
     "\nRel info:", show (relInfo br), "\n"
  ]
   where
    showIMap :: (a -> String) -> String -> IntMap a -> String
    showIMap vShow sep im
     = I.foldrWithKey (\k v -> (++ sep ++ show k ++ " -> " ++ vShow v )) "" im
    showMap sep = Map.foldrWithKey (\k v -> (++ sep ++ show k ++ " -> " ++ show v )) ""
    showMap_lits ml = Map.foldrWithKey (\l d -> (++ show l ++ " " ++ dsShow d  ++ ", ")) "" ml
    showMap_rel bxList = concatMap (\((f,pr,r),ds) -> "-" ++ r ++ "-> " ++ show f ++ ", ") bxList
data TodoList= TodoList{disjTodo :: Set PrFormula,
                         diaTodo :: Set PrFormula,
                       mergeTodo :: Set (DependencySet, Prefix, Nom)}

showTodo :: TodoList -> String
showTodo t = unlines
 [ "DisjTodo  " ++ show (disjTodo t)
 , "DiaTodo   " ++ show (diaTodo t)
 , "MergeTodo " ++ show (mergeTodo t)
 ]

emptyTodoList :: TodoList
emptyTodoList =
      TodoList {  disjTodo = Set.empty,
                   diaTodo = Set.empty,
                 mergeTodo = Set.empty
               }

addFormulas :: Params -> [PrFormula] -> Branch -> BranchInfo
addFormulas p fs br =
 foldr (\f bi ->
          case bi of
           BranchOK br2 -> addFormula p br2 f
           clash -> clash
       )
       (BranchOK br)
       fs

addFormula :: Params -> Branch -> PrFormula -> BranchInfo
addFormula p br pf
 =   putAwayFormula  p pf
   $ bookKeepFormula p pf br

bookKeepFormula :: Params -> PrFormula -> Branch -> Branch
bookKeepFormula p pf_@(PrFormula pr spr ds f) br
 =   rescheduleBlockedDias    ur br
  where
   (ur,ds2,_) = getUrfatherAndDeps br (DS.Prefix pr)
   pf = if ur == pr then pf_
         else PrFormula ur spr (dsUnion ds ds2) f


putAwayFormula :: Params -> PrFormula -> Branch -> BranchInfo
putAwayFormula p pf@(PrFormula pr spr ds f2) br =
 case f2 of
   Con fs     -> addFormulas p (prefix pr spr ds fs) br
   Dis _      -> BranchOK $ addToTodo pf br
   Dia _ _    -> BranchOK $ addToTodo pf br
   Box r f -> addBoxConstraint pr spr r f ds p br
   Lit l | isPositiveNom l -> addToLiterals pr ds l $ addToTodo pf br
   Lit l | isLProp l   -> addToLiterals pr  ds l br
   Lit l | isRProp l  -> addToLiterals spr ds l br  
   Lit l                   -> addToLiterals pr ds l br

-- TODO
-- when doing a merge, do all the witness checks!
-- when formula is sat and doing model building, add all witnesses!

{- todo list functions -}

addToTodo :: PrFormula -> Branch -> Branch
addToTodo pf@(PrFormula p spr ds f2) br =
  if alreadyDone
   then br
   else br{todoList = newTodoList}
  where
   utodo = todoList br
   newTodoList =
       case f2 of
         Dis _              -> utodo{ disjTodo = Set.insert pf ( disjTodo utodo)}
         Dia _ _            -> utodo{  diaTodo = Set.insert pf (  diaTodo utodo)}
         Lit l
          | isPositiveNom l -> utodo{mergeTodo = Set.insert (ds,p,s)
                                                            (mergeTodo utodo)}
                                where (PosLit (N s)) = l
         _                  -> error $ "addToTodo: " ++ show f2
   alreadyDone =
    case f2 of
     Dia  _ _           -> False -- test happens when the todo list is processed
     Dis _              -> False -- test happens when the todo list is processed
     Lit l
      | isPositiveNom l -> inSameClass br p s
                            where (PosLit (N s)) = l
     _                  -> error $ "alreadyDone: " ++ show f2
rescheduleBlockedDias :: Prefix -> Branch -> Branch
rescheduleBlockedDias  pr br
 = foldr addToTodo br2 toAdd
  where toAdd = iget [] pr (blockedDias br)
        br2 = br{blockedDias = I.delete pr $ blockedDias br}

addToBlockedDias :: PrFormula -> Branch -> BranchInfo
addToBlockedDias f@(PrFormula pr spr _ _) br
 = BranchOK br{blockedDias = I.insertWith (++) ur [f] (blockedDias br)}
   where ur = getUrfather br (DS.Prefix pr)

{-    helper functions for equivalence class merge     -}

merge :: Params -> Prefix -> DependencySet -> Nom -> Branch -> BranchInfo
merge p pr fDs n br
 = let
       (DS.Prefix ur1,classes1) = DS.find  (DS.Prefix pr) (nomPrefClasses br)
       (poAncestor   ,classes2) = DS.find  (DS.Nominal n) classes1
       classes3                 = DS.union (DS.Prefix pr) (DS.Nominal n) classes2
   in
    case poAncestor of
     DS.Nominal _   -> BranchOK $ addClassDeps ur1 fDs $ br { nomPrefClasses = classes3 }
                         -- new nominal from down-arrow rule
     DS.Prefix ur2
      | ur1 == ur2 -> BranchOK $ addClassDeps ur1 fDs br
      | otherwise
         ->
          let
           oldUr           = max ur1 ur2
           newUr           = min ur1 ur2
           literalSlots    = mapMaybe (\ur -> I.lookup ur (literals br)) [ur1,ur2]
           currentDeps     = dsUnions $ fDs:(map (findDeps br) [ur1,ur2])
           newPrToDepSet   = I.insert newUr currentDeps (prToDepSet br)
           newUrfatherSlot = lsAddDeps currentDeps $ lsUnions literalSlots
          in
           case newUrfatherSlot of
            SlotUpdateFailure clashingDeps ->
             let newBr = br{nomPrefClasses = classes3} in
             BranchClash newBr pr (dsUnion clashingDeps currentDeps) (neg taut)

            SlotUpdateSuccess slot ->
             let
              newLiterals = I.delete oldUr $ I.insert newUr slot $ literals br

              -- structures that merge
              newBoxFwd       = mergeInnerLists fDs (boxFwd br) oldUr newUr
              newAccStr       = mergePrefixes (accStr br) oldUr newUr fDs
              newDiaRlCh      = moveInMap (diaRlCh br)  oldUr newUr Set.union
              newBlockedDias  = moveInMap (blockedDias br) oldUr newUr (++)

              -- structures that combine
              mapBoxFwd = map (\idx -> iget [] idx (boxFwd br) ) [ur1,ur2]
              mapAccFwd = map (successors (accStr br)) [ur1,ur2]
              forms1    = concatMap (boxRule currentDeps) $ combine mapBoxFwd mapAccFwd

              formulasToAdd = nubAndMergeDeps forms1

              newBr           = br{nomPrefClasses = classes3,
                                   boxFwd         = newBoxFwd,
                                   accStr         = newAccStr,
                                   prToDepSet     = newPrToDepSet,
                                   diaRlCh        = newDiaRlCh,
                                   blockedDias    = newBlockedDias,
                                   literals       = newLiterals}
             in
              addFormulas p formulasToAdd newBr


nubAndMergeDeps :: [PrFormula] -> [PrFormula]
-- Rationale : because of the equivalence classes, a same formula can be added
-- to a branch as several prefixed formulas with different branching dependencies.
-- This functions takes a list of prefixed formulas, looks which inner formulas
-- are the same and merge their branching dependencies.
nubAndMergeDeps prfs =  namd prfs (Map.empty::Map (Prefix,Formula) DependencySet)

namd :: [PrFormula] -> Map (Prefix,Formula) DependencySet -> [PrFormula]
namd ((PrFormula p spr ds f):prfs) theMap =
  namd prfs (Map.insertWith dsUnion (p,f) ds theMap)

namd [] theMap = map (\((p,f),ds) -> PrFormula p 1 ds f) (Map.assocs theMap)

{-     handling nominal urfathers, equivalence classes and dependencies     -}

isNominalUrfather :: Branch -> Prefix -> Bool
isNominalUrfather b p = DS.isRoot (DS.Prefix p) classes
                         where classes = nomPrefClasses b


-- May look redundant with getUrfatherAndDeps, but it is important not
-- to make the test isRoot for performance
getUrfather :: Branch -> DS.Pointer -> Prefix
getUrfather br p =
    ur
  where
        (DS.Prefix ur) = DS.onlyFind p (nomPrefClasses br)

getUrfatherAndDeps :: Branch -> DS.Pointer -> (Prefix,DependencySet,EquivClasses)
getUrfatherAndDeps br p =
   if DS.isRoot p classes then defaultAnswer
                          else (ur,deps,newClasses)
  where classes = nomPrefClasses br
        (urfather, newClasses) = DS.find p classes
        (DS.Prefix ur) = urfather
        DS.Prefix unboxedP = p
        defaultAnswer = (unboxedP,dsEmpty,classes)
        deps = findDeps br ur

findDeps :: Branch -> Prefix -> DependencySet
findDeps br pr = iget dsEmpty pr (prToDepSet br)

addClassDeps :: Prefix -> DependencySet -> Branch -> Branch
addClassDeps pr ds br = br { prToDepSet = I.insertWith dsUnion pr ds (prToDepSet br) }

inSameClass :: Branch -> Prefix -> String -> Bool
inSameClass br p n
 = case fst $ DS.find (DS.Nominal n) (nomPrefClasses br) of
    DS.Nominal _ -> False
    DS.Prefix p2 -> getUrfather br (DS.Prefix p) == p2

{-     box-related constraints     -}

boxRule :: DependencySet
            -> ([((Formula,Prefix,Rel),DependencySet)],
               [(Prefix,DependencySet)]) 
            -> [PrFormula]
boxRule deps (listBox, listAcc) 
  = [buildFormula player p inactive f ds1 ds2
    |((f,inactive, player),ds1) <- listBox,
    (p,ds2) <- listAcc]
    where
      buildFormula :: Rel -> Prefix -> Prefix -> Formula -> DependencySet -> DependencySet -> PrFormula
      buildFormula player p inactive f ds1 ds2 = case player of
        "R0"-> PrFormula p inactive (dsUnions [deps,ds1,ds2]) f
        "R1"-> PrFormula inactive p (dsUnions [deps,ds1,ds2]) f 
        _   -> error("Syntaxis error on boxes")

addBoxConstraint :: Prefix -> Prefix -> Rel -> Formula -> DependencySet -> Params -> Branch
                     -> BranchInfo
addBoxConstraint pr_ spr_ r f ds p br
 | boxAlreadyDone br pr spr (r,f) = BranchOK br
 | otherwise = 
      let newBr = br{boxFwd = I.insert targetPr (((f, inactivePr, r), ds) : I.findWithDefault [] targetPr (boxFwd br)) (boxFwd br)}
          succs = successors (accStr br) targetPr
          fromBox = map (\(newNode,ds2) -> buildFormula newNode ds2) succs
      in
         addFormulas p fromBox newBr
 where
  (targetPr, inactivePr, buildFormula) = case r of 
    "R0"->(pr, spr, \newNode ds2 -> PrFormula newNode spr (dsUnion ds ds2) f)
    "R1"->(spr, pr, \newNode ds2 -> PrFormula pr newNode (dsUnion ds ds2) f)
    _   ->error("Error in box sintaxis") 
  pr = getUrfather br (DS.Prefix pr_)
  spr = getUrfather br (DS.Prefix spr_)

boxAlreadyDone :: Branch -> Prefix -> Prefix -> (Rel,Formula) -> Bool
boxAlreadyDone br ur sur (r,f)
  = let targetNode = case r of
                        "R0" -> ur
                        "R1" -> sur
                        _    -> error "Syntaxis error on boxes"
  in case I.lookup targetNode (boxFwd br) of 
    Nothing       -> False
    Just boxList  -> any (\((fBox, _, rBox), _) -> fBox == f && rBox == r) boxList

-- accessibility Formulas

addAccFormula :: Params -> (DependencySet,Prefix,Prefix) -> Branch -> BranchInfo
addAccFormula p (ds, p1_, p2_) br
   = addFormulas p boxApplications newBr
     where
      p1 = getUrfather br (DS.Prefix p1_)
      p2 = getUrfather br (DS.Prefix p2_)
      boxesInNode = iget [] p1 (boxFwd br)
      boxApplications = map (\((f, inactivePrefix, player), ds2) -> case player of
        "R0"-> PrFormula p2 inactivePrefix (dsUnion ds ds2) f 
        "R1"-> PrFormula inactivePrefix p2 (dsUnion ds ds2) f
        _   -> error("Syntaxis error on boxes")) boxesInNode
      newBr = insertRelationBranch br p1 p2 ds


insertRelationBranch :: Branch -> Prefix -> Prefix -> DependencySet -> Branch
insertRelationBranch br p1 p2 ds
 = br{accStr = insertRelation (accStr br) p1 p2 ds}

{- model building -}

isInTheModel :: Branch -> Prefix -> Bool
isInTheModel br pr | isNominalUrfather br pr = True
isInTheModel _ _ = False

getModelRepresentative :: Branch -> Prefix -> Prefix
getModelRepresentative br pr
 = getUrfather br (DS.Prefix pr)

-- <r>f is pattern blocked if its pattern is a subset
-- of one pattern of the branch's pattern store
patternBlocked :: Branch -> PrFormula -> Bool
patternBlocked br f = not $ I.null $ I.filter lookForSuperset (patterns br)
 where lookForSuperset = Set.isSubsetOf (patternOf br f)

-- given a p:<r>f formula, return the pattern:
-- { f } U { f' | p:[r]f' in branch }
-- r has to be forward
patternOf :: Branch -> PrFormula -> Set Formula
patternOf br (PrFormula pr spr _ (Dia r f))
 = Set.insert f boxes
    where ur  = getUrfather br (DS.Prefix pr)
          sur = getUrfather br (DS.Prefix spr)
          boxes = boxesOf br target_node r
          target_node = case r of
            "R0"-> ur
            "R1"-> sur

patternOf _ _ = error "patternOf called with a non diamond formula"

boxesOf :: Branch -> Prefix -> Rel -> Set Formula
boxesOf br p r
 = set $ map (\((e,_,_),_) -> e) $ iget [] p (boxFwd br)

findByPattern :: Branch -> Set Formula -> Prefix
findByPattern br pattern =
       head $ [ pr | (pr,pat2)  <- I.toList $ patterns br,
                     pattern `Set.isSubsetOf` pat2 ]

{-     modifications done by rule application     -}

-- add checks for
--  1. pattern blocking
--  2. prefix-level diamond rule saturation
addDiaRuleCheck :: Prefix -> Prefix -> (Rel,Formula) -> Prefix -> Branch -> BranchInfo
addDiaRuleCheck pr spr (r,f) newPr br =
  BranchOK br2
   where pattern = patternOf br (PrFormula ur sur dsEmpty (Dia r f))
         br1 = br{patterns = I.insert newPr pattern (patterns br)}
         br2 = br1{diaRlCh=I.insertWith Set.union ur (Set.singleton (sur,r,f)) (diaRlCh br1)}
         ur = getUrfather br (DS.Prefix pr)
         sur = getUrfather br (DS.Prefix spr)

diaAlreadyDone :: Branch -> PrFormula -> Bool
diaAlreadyDone b (PrFormula p spr _ (Dia r f)) =
    case I.lookup ur (diaRlCh b) of
      Nothing  -> False
      Just fset -> Set.member (sur, r,f) fset
 where ur = getUrfather b (DS.Prefix p)
       sur = getUrfather b (DS.Prefix spr)

diaAlreadyDone _ _ = error "dia already done : wrong formula kind"


-- | return some nominal that holds at a given prefix
positiveNomOf :: Branch -> Prefix -> Maybe String
positiveNomOf b p = positiveNom (literals b) ur
 where ur = getUrfather b (DS.Prefix p)

createNewNode :: Params -> Branch -> BranchInfo
createNewNode _ br = BranchOK br{lastPref = lastPref br + 1}

createNewNom :: Branch -> BranchInfo
createNewNom br
 = BranchOK br{nextNom = nextNom br + 1}

-- preparation of the branch at the beginning of the calculus:
--  - add the input formula at prefix 0
--  - add a nominal formula at a fresh prefix for each nominal of the input language
--    (even if the nominal was filtered out during lexical normalisation)
--  - add reflexive links for prefixes 0 and nominal witnesses
initialBranch :: Params -> LanguageInfo -> RelInfo -> Formula
                  -> BranchInfo
initialBranch p fLang relInfo_ f
 = addFormulas p [pf] br
    where
          pf = firstPrefixedFormula f
          ns = languageNoms fLang
          initPrefixes = [0,1]
          br = emptyBr
          initClasses = foldr (\(pr,n) -> DS.union (DS.Prefix pr) (DS.Nominal n))
                              DS.mkDSet
                              (zip [1..] ns)
          initLiterals = foldr (\(pr,n) -> D.insert pr (PosLit (N n)) dsEmpty)
                               I.empty
                               (zip [1..] ns)
          emptyBr =
           Branch{ literals          = initLiterals,
                   accStr            = emptyRels,
                   todoList          = emptyTodoList,
                   boxFwd            = I.empty,
                   diaRlCh           = I.empty,
                   patterns          = I.empty,
                   lastPref          = 1,
                   nextNom           = 0,
                   prToDepSet        = I.empty,
                   nomPrefClasses    = initClasses,
                   inputLanguage     = fLang,
                   blockedDias       = I.empty,
                   relInfo           = relInfo_
                 }

addToLiterals :: Prefix -> DependencySet -> Literal -> Branch -> BranchInfo
addToLiterals pr_ ds1 l br
  = case updateMap (literals br) pr ds l of
     UpdateSuccess ls  -> BranchOK br{literals = ls}
     UpdateFailure dsf -> BranchClash br pr dsf (Lit l)
   where (pr,ds2,_) = getUrfatherAndDeps br (DS.Prefix pr_)
         ds = ds1 `dsUnion` ds2

{-     function used for unit propagation     -}

{-     other functions     -}
prefixes :: Branch -> [Prefix]
prefixes br = [0..(lastPref br)]

hasProperty :: RelProperty -> RelInfo -> Rel -> Bool
hasProperty p relI r = case Map.lookup r relI of
                        Nothing         -> False
                        Just properties -> p `elem` properties


combine :: [a] -> [b] -> [(a,b)]
combine [] _  = error "combine: first list empty"
combine _  [] = error "combine: second list empty"
combine as bs = [(a,b) | (idxA,a) <- zip [(0::Int)..] as,
                         (idxB,b) <- zip [(0::Int)..] bs,
                         idxA /= idxB]

moveInMap :: IntMap b -> Int -> Int -> (b -> b -> b) -> IntMap b
moveInMap m origKey destKey mergeF
 = case I.lookup origKey m of
    Nothing -> m
    Just origValue
     -> I.insertWith mergeF destKey origValue $ I.delete origKey m

list :: Ord a => Set.Set a -> [a]
list = Set.toList

set :: Ord a => [a] -> Set.Set a
set = Set.fromList

iget :: a -> Int -> IntMap a -> a
iget = I.findWithDefault

get :: (Ord k) => a -> k -> Map k a -> a
get = Map.findWithDefault

