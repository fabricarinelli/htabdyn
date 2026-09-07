module HTab.Branch
(
Branch(..), BranchInfo(..), TodoList(..),
createNewNode, createNewNom,
addFormulas, addAccFormula,
addToBlockedDias,
addDiaRuleCheck, addDownRuleCheck,
initialBranch,
reduceDisjunctionProposeLazy, doLazyBranching,
merge,
getUrfather, getUrfatherAndDeps,
getModelRepresentative, patternBlocked,
diaAlreadyDone, downAlreadyDone,
ReducedDisjunct(..),
patternOf, findByPattern,
prefixes, isNominalUrfather, isInTheModel,
positiveNomOf,
isTransitive
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
                        successors, linksFromTo, showRels )
import HTab.Literals ( UpdateResult(..), Literals,
                       SlotUpdateResult(..), LiteralSlot,
                       updateMap, lsUnions, lsAddDeps, lsQuery,
                       positiveNom)

data BranchInfo = BranchOK Branch |
                  BranchClash Branch Prefix DependencySet Formula

type BoxConstraints     = IntMap {- Prefix -} (Map Rel [(Formula,DependencySet)])
type BranchingWitnesses = IntMap {- Prefix -} (Map Literal [PrFormula])
type EquivClasses = DS.DisjSet DS.Pointer

data Branch =
              Branch {
                 -- the premodel
                      literals :: Literals,
                        accStr :: OutRels,
                 -- local and global constraints
                        boxFwd :: BoxConstraints,
                      univCons :: [(DependencySet,Formula)],
                 -- pending formulas / todo lists
                      todoList :: TodoList,
                 -- saturation of rules
                       diaRlCh :: IntMap {- Prefix -} (Set (Prefix,Rel,Formula)),
                      downRlCh :: IntMap {- Prefix -} (Set Formula),
                        atRlCh :: Set (Nom,Formula),
                     existRlCh :: Set Formula,
                 -- pattern blocking
                      patterns :: IntMap (Set Formula),
                 -- backjumping data attached to equivalence classes
                    prToDepSet :: IntMap {- Prefix -} DependencySet,
                 -- prefix/nominal equivalence classes
                nomPrefClasses :: EquivClasses,
                 -- book keeping
                      lastPref :: Prefix,
                       nextNom :: Int,
                 -- lazy branching
                   brWitnesses :: BranchingWitnesses,
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
     "\nWitnesses: ",
     showIMap (\v -> "(" ++ showMap_lits2 v ++ ")") "\n " (brWitnesses br),
     "\nDia rule chart: ", show (diaRlCh br),
     "\nIndividual patterns: ", show (patterns br),
     "\nDown rule chart: ", show (downRlCh br),
     "\n@ rule chart: ", show (list $ atRlCh br),
     "\nExist rule chart: ", show (list $ existRlCh br),
     "\nUniv constraints: ", show (univCons br),
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
    showMap_lits2 = Map.foldrWithKey (\l fs -> (++ show l ++ " :" ++ show fs ++ ", ")) ""
    showMap_rel
     = Map.foldrWithKey (\r dxs -> (++ "-" ++ r ++ "-> " ++ show dxs ++ ", ")) ""

data TodoList= TodoList{disjTodo :: Set PrFormula,
                         diaTodo :: Set PrFormula,
                       existTodo :: Set PrFormula,
                          atTodo :: Set PrFormula,
                        downTodo :: Set PrFormula,
                       mergeTodo :: Set (DependencySet, Prefix, Nom),
                     roleIncTodo :: Set (DependencySet, Prefix, Prefix, [Rel]) }

showTodo :: TodoList -> String
showTodo t = unlines
 [ "DisjTodo  " ++ show (disjTodo t)
 , "DiaTodo   " ++ show (diaTodo t)
 , "ExistTodo " ++ show (existTodo t)
 , "AtTodo    " ++ show (atTodo t)
 , "DownTodo  " ++ show (downTodo t)
 , "MergeTodo " ++ show (mergeTodo t)
 , "RoleITodo " ++ show (roleIncTodo t)
 ]

emptyTodoList :: TodoList
emptyTodoList =
      TodoList {  disjTodo = Set.empty,
                   diaTodo = Set.empty,
                 existTodo = Set.empty,
                    atTodo = Set.empty,
                  downTodo = Set.empty,
                 mergeTodo = Set.empty,
               roleIncTodo = Set.empty
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
 =   rescheduleLazyBranching  p pf
   $ rescheduleBlockedDias    ur br
  where
   (ur,ds2,_) = getUrfatherAndDeps br (DS.Prefix pr)
   pf = if ur == pr then pf_
         else PrFormula ur spr (dsUnion ds ds2) f

rescheduleLazyBranching :: Params -> PrFormula -> Branch -> Branch
rescheduleLazyBranching p (PrFormula pr spr ds (Lit l)) br   -- pr already urfather
 | lazyBranching p && isProp l
   =
     let (Just innerMap) = I.lookup pr (brWitnesses br)
     in

     case D.lookup pr l (brWitnesses br) of
      Just _
        -> let innerMap2 = Map.delete l innerMap
               newBrW    = I.insert pr innerMap2 (brWitnesses br)
               newBr     = br{brWitnesses = newBrW}
           in
            newBr -- forget  the disjunctions, they are really satisfied
      Nothing
       -> case D.lookup pr (negLit l) (brWitnesses br) of
           Just fs
             -> let innerMap2 = Map.delete (negLit l) innerMap
                    newBrW    = I.insert pr innerMap2 (brWitnesses br)
                    newBr     = br{brWitnesses = newBrW}
                in
                 foldr addToTodo newBr (map (addDeps ds) fs) --reschedule
           Nothing
            -> br -- do nothing

rescheduleLazyBranching _ _ br = br


putAwayFormula :: Params -> PrFormula -> Branch -> BranchInfo
putAwayFormula p pf@(PrFormula pr spr ds f2) br =
 case f2 of
   Con fs     -> addFormulas p (prefix pr spr ds fs) br
   Dis _      -> putAwayDisjunction p pf br
   Dia _ _    -> BranchOK $ addToTodo pf br
   Box r f    -> addBoxConstraint      pr r f ds p br
   A f        -> addUnivConstraint          f ds p br
   E _        -> BranchOK $ addToTodo pf br
   At _ _     -> BranchOK $ addToTodo pf br
   Down _ _   -> BranchOK $ addToTodo pf br
   Lit l | isPositiveNom l -> addToLiterals pr ds l $ addToTodo pf br
   Lit l | isLProp l   -> addToLiterals pr  ds l br
   Lit l | isRProp l  -> addToLiterals spr ds l br  
   Lit l                   -> addToLiterals pr ds l br

putAwayDisjunction :: Params -> PrFormula -> Branch -> BranchInfo
putAwayDisjunction p pf@(PrFormula pr spr ds f@(Dis fs)) br
 | lazyBranching p
  = case reduceDisjunctionProposeLazy br pr fs of
     Contradiction dsClash -> BranchClash br pr (dsUnion ds dsClash) f
     Triviality -> BranchOK br
     Reduced new_ds disjuncts mProposed
      -> let fNew = PrFormula pr spr (dsUnion ds new_ds) (Dis disjuncts)
              -- TODO if there was no reduction, leave ds
         in
          case mProposed of
            Nothing -> BranchOK $ addToTodo fNew br
            Just lit -- add pr, lit, ((++) disjuncts) aux witnesses
             -> doLazyBranching ur lit [fNew] br
 | otherwise
  = BranchOK $ addToTodo pf br
 where ur = getUrfather br (DS.Prefix pr)

putAwayDisjunction _ pf _ = error ("putAwayDisjunction " ++ show pf)

-- assume the tests have been done beforehand, always returns BranchOK
doLazyBranching :: Prefix -> Literal -> [PrFormula] -> Branch -> BranchInfo
doLazyBranching pr lit pfs br
 = case I.lookup pr (brWitnesses br) of
    Nothing -> let newBrW = D.insert pr lit pfs (brWitnesses br)
               in BranchOK br{brWitnesses = newBrW}
    Just innerMap
     -> case Map.lookup lit innerMap of
        -- assume this is the only place where l or (negLit l) occur
         Nothing -> let newInner = Map.insert lit pfs innerMap
                        newBrW = I.insert pr newInner (brWitnesses br)
                    in BranchOK br{brWitnesses = newBrW}
         Just fs -- assume the test was already done
          -> let newInner = Map.insert lit (pfs++fs) innerMap
                 newBrW = I.insert pr newInner (brWitnesses br)
             in BranchOK br{brWitnesses = newBrW}


-- TODO
-- when doing a merge, do all the witness checks!
-- when formula is sat and doing model building, add all witnesses!

{- todo list functions -}

addToTodo :: PrFormula -> Branch -> Branch
addToTodo pf@(PrFormula p spr ds f2) br =
  if alreadyDone
   then br
   else brWithSaturation{todoList = newTodoList}
  where
   utodo = todoList br
   newTodoList =
       case f2 of
         Dis _              -> utodo{ disjTodo = Set.insert pf ( disjTodo utodo)}
         Dia _ _            -> utodo{  diaTodo = Set.insert pf (  diaTodo utodo)}
         E _                -> utodo{existTodo = Set.insert pf (existTodo utodo)}
         At _ _             -> utodo{   atTodo = Set.insert pf (   atTodo utodo)}
         Down _ _           -> utodo{ downTodo = Set.insert pf ( downTodo utodo)}
         Lit l
          | isPositiveNom l -> utodo{mergeTodo = Set.insert (ds,p,s)
                                                            (mergeTodo utodo)}
                                where (PosLit (N s)) = l
         _                  -> error $ "addToTodo: " ++ show f2
   alreadyDone =
    case f2 of
     E  f3              -> Set.member f3 (existRlCh br)
     At n f3            -> Set.member (n,f3) (atRlCh br)
     Down _ _           -> downAlreadyDone br pf
     Dia  _ _           -> False -- test happens when the todo list is processed
     Dis _              -> False -- test happens when the todo list is processed
     Lit l
      | isPositiveNom l -> inSameClass br p s
                            where (PosLit (N s)) = l
     _                  -> error $ "alreadyDone: " ++ show f2
   brWithSaturation =
    case f2 of
     E f3        -> br{existRlCh = Set.insert f3 (existRlCh br)}
     At n f3     -> br{atRlCh    = Set.insert (n,f3) (atRlCh br)}
     _           -> br

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
              newBoxFwd       = D.moveInnerPlusDeps fDs (boxFwd br) oldUr newUr
              newAccStr       = mergePrefixes (accStr br) oldUr newUr fDs
              newDiaRlCh      = moveInMap (diaRlCh br)  oldUr newUr Set.union
              newBlockedDias  = moveInMap (blockedDias br) oldUr newUr (++)
              (newBrWit,unwitnessed) = mergeWitnesses oldUr newUr slot (brWitnesses br)

              -- structures that combine
              mapBoxFwd = map (\idx -> iget Map.empty idx (boxFwd br) ) [ur1,ur2]
              mapAccFwd = map (successors (accStr br)) [ur1,ur2]
              forms1    = concatMap (boxRule currentDeps) $ combine mapBoxFwd mapAccFwd

              formulasToAdd = nubAndMergeDeps $ forms1 ++ unwitnessed

              newBr           = br{nomPrefClasses = classes3,
                                   boxFwd         = newBoxFwd,
                                   accStr         = newAccStr,
                                   prToDepSet     = newPrToDepSet,
                                   diaRlCh        = newDiaRlCh,
                                   blockedDias    = newBlockedDias,
                                   literals       = newLiterals,
                                   brWitnesses    = newBrWit}
             in
              addFormulas p formulasToAdd newBr

mergeWitnesses :: Prefix -> Prefix -> LiteralSlot -> BranchingWitnesses
                   -> (BranchingWitnesses, [PrFormula])
mergeWitnesses oldUr newUr urfatherSlot brWits
 =( I.insert newUr newDest2 ( I.delete oldUr brWits ), toAdd1 ++ toAdd2 )
  where
   srcInnerMap  = iget Map.empty oldUr brWits
   destInnerMap = iget Map.empty newUr brWits
   (newDest1,toAdd1) = mergeWitnessesWitnessesMap srcInnerMap destInnerMap
   (newDest2,toAdd2) = mergeWitnessesAgainstLiterals newDest1 urfatherSlot

mergeWitnessesWitnessesMap :: Map Literal [PrFormula] -> Map Literal [PrFormula]
                               -> (Map Literal [PrFormula], [PrFormula])
mergeWitnessesWitnessesMap srcWitMap destWitMap
 = foldr go (destWitMap,[]) $ Map.assocs srcWitMap
   where
      go (l,fs) (destMap,toAddAgain)
         = case Map.lookup l destMap of
            Just fs2 -> (Map.insert l (fs2++fs) destMap, toAddAgain)
            Nothing
             -> case Map.lookup (negLit l) destMap of
       -- (negLit l) is just one bit away from l in the map, but we don't use it
                  Just fs2 -> (Map.delete (negLit l) destMap, fs++fs2++toAddAgain)
                  Nothing ->  (Map.insert l fs destMap, toAddAgain)

mergeWitnessesAgainstLiterals :: Map Literal [PrFormula] -> LiteralSlot
                                   -> (Map Literal [PrFormula],[PrFormula])
mergeWitnessesAgainstLiterals  witMap ls
 = foldr go (witMap,[]) $ Map.assocs witMap
   where
    go (lit,fs) (destMap,toAddAgain)
      | lit `Map.member` ls = (Map.delete lit destMap,toAddAgain)
      | negLit lit `Map.member` ls = (Map.delete lit destMap,fs++toAddAgain)
          -- same remark as above
      | otherwise = (destMap,toAddAgain)

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
            -> (Map Rel [(Formula,DependencySet)],
                Map Rel [(Prefix,DependencySet)] )
            -> [PrFormula]
boxRule deps (mapBox, mapAcc)
 = [PrFormula p 1 (dsUnions [deps,ds1,ds2]) f |
                      r1 <- Map.keys mapBox,
                      r2 <- Map.keys mapAcc,
                      r1 == r2,
                      (f,ds1) <- (Map.!) mapBox r1,
                      (p,ds2) <- (Map.!) mapAcc r2     ]

addBoxConstraint :: Prefix -> Rel -> Formula -> DependencySet -> Params -> Branch
                     -> BranchInfo
addBoxConstraint pr_ r f ds p br
 | boxAlreadyDone br pr (r,f) = BranchOK br
 | otherwise
    = let newBr = br{boxFwd = updateBoxConstr pr r f ds (boxFwd br)}
          succs  = get [] r $ successors (accStr br) pr
          toAdd = fromTrans ++ fromBox
          fromTrans
           = if isTransitive (relInfo br) r
              then map (\(pr2,ds2) -> PrFormula pr2 1 (dsUnion ds ds2) (Box r f)) succs
              else []
          fromBox = map (\(pr2,ds2) -> PrFormula pr2 1 (dsUnion ds ds2) f) succs
    -- todo check again with new pattern, create successor if new pattern not realized
      in
         addFormulas p toAdd newBr
 where pr = getUrfather br (DS.Prefix pr_)

updateBoxConstr :: Prefix -> Rel -> Formula -> DependencySet -> BoxConstraints
                    -> BoxConstraints
updateBoxConstr p1_ r_ f_ ds_ boxConstr_ =
  case I.lookup p1_ boxConstr_ of
    Nothing       -> I.insert p1_ (Map.singleton r_ [(f_,ds_)]) boxConstr_
    Just innerMap ->
       case Map.lookup r_ innerMap of
        Nothing
         -> I.insert p1_ (Map.insert r_ [(f_,ds_)] innerMap)                boxConstr_
        Just innerInnerList
         -> I.insert p1_ (Map.insert r_ ((f_,ds_):innerInnerList) innerMap) boxConstr_

boxAlreadyDone :: Branch -> Prefix -> (Rel,Formula) -> Bool
boxAlreadyDone br ur (r,f)
 = case ( do inner <- I.lookup ur (boxFwd br)
             boxes <- map (\(e,_) -> e) <$> Map.lookup r inner
             return (f `elem` boxes) ) of
     Just True -> True
     _         -> False

-- accessibility Formulas

addAccFormula :: Params -> (DependencySet,Rel,Prefix,Prefix) -> Branch -> BranchInfo
addAccFormula p (ds, r, p1_, p2_) br
   = addFormulas p toAdd newBr
     where
      toAdd = transApplications ++ boxApplications
      transApplications =
       if isTransitive (relInfo br) r
        then map (\(f,ds2) -> PrFormula p2 1 (dsUnion ds ds2) (Box r f)) toSendFwd
        else []
      boxApplications = map (\(f,ds2) -> PrFormula p2 1 (dsUnion ds ds2) f) toSendFwd
      p1 = getUrfather br (DS.Prefix p1_)
      p2 = getUrfather br (DS.Prefix p2_)
      toSendFwd = get [] r $ iget Map.empty p1 (boxFwd br)
      newBr = scheduleInclusionRule p1 p2 r ds $ insertRelationBranch br p1 r p2 ds


scheduleInclusionRule :: Prefix -> Prefix -> Rel -> DependencySet -> Branch -> Branch
scheduleInclusionRule p1 p2 r ds br -- todo get all included
 = if null toschedule
    then br
    else br{todoList = newTodoList}
   where parentss = case Map.lookup r (relInfo br) of
                      Nothing -> []
                      Just props -> [ rs | SubsetOf rs <- props]
         toschedule = map (\parents -> (ds,p1,p2,parents)) $ filter (not . alreadyDone)
                          parentss
         alreadyDone = any (`elem` linksFromTo (accStr br) p1 p2)
         utodo       = todoList br
         newTodoList = utodo{roleIncTodo = Set.fromList toschedule
                                           `Set.union` roleIncTodo utodo}

insertRelationBranch :: Branch -> Prefix -> Rel -> Prefix -> DependencySet -> Branch
insertRelationBranch br p1 r p2 ds
 = br{accStr = insertRelation (accStr br) p1 r p2 ds}

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
    where ur = getUrfather br (DS.Prefix pr)
          boxes = if isTransitive (relInfo br) r
                   then boxesOf br ur r
                          `Set.union` (Set.map (Box r) $ boxesOf br ur r)
                   else boxesOf br ur r

patternOf _ _ = error "patternOf called with a non diamond formula"

boxesOf :: Branch -> Prefix -> Rel -> Set Formula
boxesOf br p r
 = set $ map (\(e,_) -> e) $ get [] r $ iget Map.empty p (boxFwd br)

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


addDownRuleCheck :: Prefix -> Formula -> Branch -> BranchInfo
addDownRuleCheck pr f br =
  BranchOK br{downRlCh=I.insertWith Set.union ur (Set.singleton f) (downRlCh br)}
   where ur = getUrfather br (DS.Prefix pr)

downAlreadyDone :: Branch -> PrFormula -> Bool
downAlreadyDone b (PrFormula p spr _ f@(Down _ _)) =
  case I.lookup ur (downRlCh b) of
     Nothing  -> False
     Just fset -> Set.member f fset
 where ur = getUrfather b (DS.Prefix p)

downAlreadyDone _ _ = error "down already done : wrong formula kind"

-- | return some nominal that holds at a given prefix
positiveNomOf :: Branch -> Prefix -> Maybe String
positiveNomOf b p = positiveNom (literals b) ur
 where ur = getUrfather b (DS.Prefix p)

addUnivConstraint :: Formula -> DependencySet -> Params -> Branch -> BranchInfo
addUnivConstraint f ds p br
 = addFormulas p [PrFormula pr 1 ds f | pr <- urfathers] newBr
   where newBr = br{univCons = (ds,f):(univCons br)}
         prefs = [0..(lastPref br)]
         urfathers = filter (isNominalUrfather br) prefs

createNewNode :: Params -> Branch -> BranchInfo
createNewNode p br
 = addFormulas p
               ( map (\(ds,f) -> PrFormula newPr 1 ds f) univConstraints )
               newBrWithRefl
   where newPr = lastPref br + 1
         newBr = br{lastPref = newPr}
         univConstraints = univCons br
         newBrWithRefl = addReflexiveLinks newPr newBr

addReflexiveLinks :: Prefix -> Branch -> Branch
addReflexiveLinks pr br
 = foldr (\rel_ br_ -> insertRelationBranch br_ pr rel_ pr dsEmpty) br reflRels
   where reflRels = Map.keys $ Map.filter (elem Reflexive) (relInfo br)

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
          nbNs = length ns
          initPrefixes = 0:[1..nbNs]
          br = foldr addReflexiveLinks emptyBr initPrefixes
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
                   boxFwd            = D.empty,
                   diaRlCh           = I.empty,
                   downRlCh          = I.empty,
                   atRlCh            = Set.empty,
                   existRlCh         = Set.empty,
                   patterns          = I.empty,
                   univCons          = [],
                   lastPref          = nbNs,
                   nextNom           = 0,
                   prToDepSet        = I.empty,
                   brWitnesses       = I.empty,
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

data ReducedDisjunct
 =   Triviality
   | Contradiction DependencySet
   | Reduced DependencySet (Set Formula) (Maybe Literal)
               -- proposable witness for lazy branching
 deriving Show

reduceDisjunctionProposeLazy :: Branch -> Prefix -> Set Formula -> ReducedDisjunct
reduceDisjunctionProposeLazy br pr fs
 =  case Set.fold go (Just ( Set.empty , dsEmpty, Nothing )) fs of
     Nothing -> Triviality
     Just (disjuncts,ds,proposed)
       | Set.null disjuncts -> Contradiction ds
       | otherwise -> Reduced ds disjuncts proposed
            -- what if not reduced ? and no proposed witness ?
   where
      ur = getUrfather br (DS.Prefix pr)
      go _ Nothing = Nothing
      go l@(Lit current) (Just (disjuncts,ds_,proposed))
       = case (lsQuery (literals br) ur current, proposed) of
          (Just (True,_)    ,_) -> Nothing
          (Just (False,ds2) ,_) -> Just (disjuncts,dsUnion ds_ ds2, proposed)
          (Nothing, Nothing)
           -> if isPositiveNom current
               then Just (Set.insert l disjuncts,ds_,Nothing)
                    -- no lazy branching with positive nominals
               else case D.lookup ur (negLit current) (brWitnesses br) of
                      -- if current is a negated nominal,
                      -- we know the "just" case is impossible
                     Just _  -> Just (Set.insert l disjuncts,ds_,Nothing)
                      -- there's an opposed witness
                     Nothing -> Just (Set.insert l disjuncts,ds_, Just current)
                      -- propose for witness
          _ {- already a proposed witness -}
           -> Just (Set.insert l disjuncts,ds_,proposed)
      go f (Just (disjuncts,ds_,proposed)) = Just (Set.insert f disjuncts, ds_,proposed)


{-     other functions     -}
prefixes :: Branch -> [Prefix]
prefixes br = [0..(lastPref br)]

hasProperty :: RelProperty -> RelInfo -> Rel -> Bool
hasProperty p relI r = case Map.lookup r relI of
                        Nothing         -> False
                        Just properties -> p `elem` properties

isTransitive :: RelInfo -> Rel -> Bool
isTransitive = hasProperty Transitive

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

