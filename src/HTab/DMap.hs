module HTab.DMap
(DMap, empty, flatten,
 delete, insert, insertWith, (!),
 insert1, lookup, lookup1, lookupInter)

where

import Data.IntMap ( IntMap )
import qualified Data.IntMap as I
import Data.Map ( Map )
import qualified Data.Map as M

import HTab.Formula(DependencySet, dsUnion)

import Prelude hiding ( lookup )

{- a DMap , or double map, is a nesting of two Maps -}

type DMap c = IntMap (Map String c)

empty :: DMap c
empty = I.empty

insert1 :: Int -> Map String c -> DMap c -> DMap c
insert1 k1 v m = I.insert k1 v m

insert :: (Ord k) => Int -> k -> c -> IntMap (Map k c) -> IntMap (Map k c)
insert k1 k2 v m
 = case I.lookup k1 m of
    Nothing     -> I.insert k1 (M.singleton k2 v) m
    Just innerM -> I.insert k1 (M.insert k2 v innerM) m


insertWith :: (c -> c -> c) -> Int -> String -> c -> DMap c -> DMap c
insertWith f k1 k2 v m
 = case I.lookup k1 m of
    Nothing     -> I.insert k1 (M.singleton k2 v) m
    Just innerM -> I.insert k1 (M.insertWith f k2 v innerM) m

flatten :: IntMap (Map b c) -> [(Int,b,c)]
flatten m
 = let ambcs = I.assocs m  in --  [(a,IntMap c)]
    concatMap (\(a_,innerM_) ->  map  (\(b_,c_) -> (a_,b_,c_))  (M.assocs innerM_ )) ambcs

infixl 9 !

(!) :: DMap c -> Int -> String -> c
(!) m k1 k2 = (M.!) ( (I.!) m k1 ) k2


lookup :: (Ord k) => Int -> k -> IntMap (Map k c) -> Maybe c
lookup k1 k2 m = do innerMap <- I.lookup k1 m
                    M.lookup k2 innerMap

lookup1 :: Int -> DMap c -> Maybe (Map String c)
lookup1 k1 m = I.lookup k1 m

delete ::  Int -> DMap c -> DMap c
delete k1 m = I.delete k1 m

lookupInter :: Int -> DMap c -> [String]
lookupInter k1 m = case I.lookup k1 m of
                    Nothing -> []
                    Just innerMap -> M.keys innerMap
