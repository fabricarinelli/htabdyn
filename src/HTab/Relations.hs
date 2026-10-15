module HTab.Relations

( OutRels, emptyRels, insertRelation, mergePrefixes,
  successors, allRels, null,
  showRels, mergeInnerLists )

where

import qualified Data.IntMap as I
import Data.IntMap ( IntMap )
import Data.Map ( Map )

import qualified Data.List as List

import HTab.Formula (Prefix, Rel, DependencySet, dsShow, dsUnion )
import Prelude hiding (id, pred, succ, null)

type OutRels = IntMap {- Prefix -} [(Prefix,DependencySet)]

emptyRels :: OutRels
emptyRels = I.empty

null :: OutRels -> Bool
null = I.null

allRels :: OutRels -> [(Prefix,Rel,Prefix)]
allRels rels = [ (p1,"R",p2) | (p1,ds_out_s) <-  I.toList rels,
                             (p2,_) <- ds_out_s ]

successors :: OutRels -> Prefix -> [(Prefix,DependencySet)]
successors rels p = I.findWithDefault [] p rels

-- assumes you never add twice the same relation
insertRelation :: OutRels -> Prefix -> Prefix -> DependencySet -> OutRels
insertRelation rels p1 p2 ds = I.insertWith (++) p1 [(p2,ds)] rels


mergePrefixes :: OutRels -> Prefix -> Prefix -> DependencySet -> OutRels
mergePrefixes r pr ur _ | pr == ur = r
mergePrefixes r pr ur ds = mergeInnerLists ds r pr ur

showRels :: OutRels -> String
showRels r = prettyShowMap_ r (\v -> "(" ++ prettyShowMap_bps_x v ++ ")") "\n "

prettyShowMap_ :: (Show y) => IntMap y -> (y -> String) -> String -> String
prettyShowMap_ m valueShow separator
 = List.intercalate separator $ map (\(k,v) -> show k ++ " -> " ++ valueShow v)
          $ I.toList m

prettyShowMap_bps_x :: (Show a) => [(a,DependencySet)] -> String
prettyShowMap_bps_x m
 = "-R-> " ++ List.intercalate ", " (map (\(x,bp) -> show x ++ " " ++ dsShow bp) m)

-- provided two keys of the IntMap and a merge function, 
-- merge the list of both keys
-- delete the first list from the IntMap
-- and add the given dependencies
mergeInnerLists :: DependencySet -> IntMap[(c,DependencySet)] -> Int -> Int
                        -> IntMap [(c,DependencySet)]
mergeInnerLists newDeps m origKey destKey
 = case I.lookup origKey m of
     Nothing  -> m
     Just origList
        -> let newList = map (\(c, oldDeps)->(c, dsUnion newDeps oldDeps )) origList
               prunedM = I.delete origKey m
            in I.insertWith (++) destKey newList prunedM

