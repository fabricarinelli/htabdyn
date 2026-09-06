module HTab.ModelGen (Model, buildModel, toDot )

where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.IntMap as I
import HyLo.Model.Herbrand ( inducedModel )
import HyLo.Model.PrettyPrint ( toDotStr )
import qualified HyLo.Model.Herbrand as H
import qualified HyLo.Model as M

import qualified HyLo.Signature.String as S

import HTab.Formula( PrFormula(..), Formula(..), Literal(..), Atom(..),
                     Prefix, Rel, LanguageInfo(..),
                     RelInfo, isPositiveProp )
import HTab.Branch( Branch(..), prefixes, getUrfather,
                    patternOf, findByPattern,
                    isInTheModel, getModelRepresentative,
                    isTransitive )
import qualified HTab.DisjSet as DS
import HTab.DMap (flatten)
import HTab.Relations ( allRels )

type Model = M.Model S.NomSymbol S.NomSymbol S.PropSymbol S.RelSymbol

buildModel :: Branch -> Model
buildModel br =
  completeTrans (relInfo br) $ inducedModel $ H.herbrand es ps rs
 where
  bias = if null $ languageNoms $ inputLanguage br
          then 0
          else 1 + length ( languageNoms $ inputLanguage br )
  es = Set.fromList $
        [(S.NomSymbol $ show (getUrfather br (DS.Nominal n) + bias), S.NomSymbol n)
         | n <- languageNoms $ inputLanguage br]
        ++ [(S.NomSymbol $ show (p + bias), S.NomSymbol $ show (p + bias))
            | p <- prefixes br, isInTheModel br p]
  ps = Set.fromList
        [(S.NomSymbol $ show (pre + bias), pro) | (pre,pro) <- prefixAndProps br]
  pbBlocked =
         [ (pr, r, pr2) |
             pr <- prefixes br,
             isInTheModel br pr,
             blockedDia@(PrFormula _ _ _ (Dia r _)) <- get [] pr (blockedDias br),
             let pat = patternOf br blockedDia,
             let pr2 = findByPattern br pat ]
  rels = (allRels $ accStr br) ++ pbBlocked
  inModel = flip getModelRepresentative
  rs = Set.fromList
        $ map toSimpSig
        $ map (\(p1,r,p2) -> ((p1 `inModel` br) + bias , r,(p2 `inModel` br) + bias))
          rels

toSimpSig :: (Prefix,Rel,Prefix) -> (S.NomSymbol,S.RelSymbol,S.NomSymbol)
toSimpSig (p1,r,p2) = (S.NomSymbol (show p1), S.RelSymbol r, S.NomSymbol (show p2))

prefixAndProps :: Branch -> [(Prefix,S.PropSymbol)]
prefixAndProps br =
  [(pr, S.PropSymbol s) | (pr , p_) <- prPosLitProp ++ prefWitPositive,
                           let (PosLit (P s)) = p_ ]
 where
  litsRelevant = I.filterWithKey (\k _ -> isInTheModel br k) (literals br)
  prPosLitProp = [ (a,b)  | (a,b,_)  <- flatten litsRelevant, 
                            isPositiveProp b ]
  --
  witMap = brWitnesses br
  witMapRelevant = I.filterWithKey (\k _ -> isInTheModel br k) witMap
  prefWitPositive = [ (a,b)  | (a,b,_)  <- flatten witMapRelevant,
                               isPositiveProp b ]

completeTrans :: RelInfo -> Model -> Model
completeTrans relI m
 = m{M.succs = \rs@(S.RelSymbol r) w
                 -> if isTransitive relI r
                     then getTransClos (M.succs m) rs w
                     else M.succs m rs w}

getTransClos :: (Ord w) => (r -> w -> Set w) -> r -> w -> Set w
getTransClos succs_ r_ w_
 = go Set.empty Set.empty succs_ r_ w_
 where
  go seen todo succs r w
   = case Set.minView todo1 of
      Nothing                -> seen
      Just (nextWorld,todo2) -> go (Set.insert nextWorld seen) todo2 succs r nextWorld
     where todo1  = (succs r w `Set.union` todo) `Set.difference` seen

toDot :: Model -> String
toDot = toDotStr

get :: a -> Int -> I.IntMap a -> a
get = I.findWithDefault
