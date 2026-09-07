module HTab.Formula

(Nom, Prop, Rel, Prefix, Formula(..), Literal(..), Atom(..),
DependencySet, Dependency,
dsUnion, dsUnions, dsInsert, dsMember,
dsEmpty, dsMin, dsShow, addDeps,
PrFormula(..),showLess,
LanguageInfo(..), neg,
conj, disj, taut,
prop, nom, prefix, negPr,
replaceVar,
firstPrefixedFormula,
parse, simpleParse, Theory, RelInfo, Task,
showRelInfo, negLit,
encodeValidityTest, encodeSatTest, encodeRetrieveTask,
HyLoFormula, RelProperty(..),
isPositiveNom, isPositiveProp, isProp, isLProp, isRProp, list, imp,
trSab, trSwap, trBri, emptyset
)

 where
import qualified Data.Set as Set
import Data.Set ( Set )
import qualified Data.Map as Map
import Data.Map ( Map )
import qualified Data.IntSet as IntSet
import Data.List ( delete, nub, intercalate )

import Data.Char ( toUpper )

import qualified HyLo.Signature.String as S

import HyLo.Signature( HasSignature(..), nomSymbols, relSymbols )

import qualified HyLo.InputFile as InputFile
import qualified HyLo.InputFile.Parser as P
import qualified HyLo.Formula as F
import HTab.CommandLine ( Params(..) )

type Prefix  = Int
type Rel     = String
type Nom     = String
type Prop    = String
data Atom    = Taut | N String | P String deriving(Eq, Ord)
data Literal = PosLit Atom | NegLit Atom deriving(Eq, Ord)

negLit :: Literal -> Literal
negLit (PosLit a) = NegLit a
negLit (NegLit a) = PosLit a

isPositiveNom, isPositiveProp, isProp, isLProp, isRProp :: Literal -> Bool
isPositiveNom (PosLit (N _))  = True
isPositiveNom _               = False
isPositiveProp (PosLit (P _)) = True
isPositiveProp _              = False
isProp (PosLit (P _))         = True
isProp (NegLit (P _))         = True
isProp _                      = False 
isLProp (PosLit (P ('P':'0':'_':_))) = True
isLProp (NegLit (P ('P':'0':'_':_))) = True
isLProp _                        = False
isRProp (PosLit (P ('P':'1':'_':_))) = True
isRProp (NegLit (P ('P':'1':'_':_))) = True
isRProp _                        = False

instance Show Atom where
 show (Taut) = "T"
 show (N n)  = n
 show (P p)  = p

instance Show Literal where
 show (PosLit a) = show a
 show (NegLit a) =  '!' : show a

data Formula
     = Lit    Literal
     | Con   (Set Formula)
     | Dis   (Set Formula)
     | At     Nom Formula
     | Down   Nom Formula
     | Box    Rel     Formula
     | Dia    Rel     Formula
     | A      Formula
     | E      Formula
  deriving (Eq, Ord)

instance Show Formula where
 show (Lit a)    = show a
 show (Con fs)   = "^" ++ show (list fs)
 show (Dis fs)   = "v" ++ show (list fs)
 show (At n f)   =  n  ++ ":(" ++ show f ++ ")"
 show (Box r f)  = "[" ++ r ++ "]"   ++ show f
 show (Dia r f)  = "<" ++ r ++ ">"   ++ show f
 show (A f)      = "A " ++ show f
 show (E f)      = "E " ++ show f
 show (Down n f) = "down " ++ n ++ "." ++ show f

-- parsing of the input file

type Theory  = Formula
type Task    = P.InferenceTask
type PRelInfo = [P.RelInfo]

type RelInfo = Map String [RelProperty]
data RelProperty   =   Reflexive
                     | Transitive
                     | Universal
                     --
                     | SubsetOf [Rel]
                     deriving (Eq, Show, Ord)

showRelInfo :: RelInfo -> String
showRelInfo = Map.foldrWithKey (\r v -> (++ " " ++ show r ++ " -> " ++ show v )) ""

data RelationChanging = Sabotage | Bridge | Swap

parse :: Params -> String -> (Theory,RelInfo,LanguageInfo,[Task])
parse p s
  = (theory, relInfo, fLang, tasks)
    where parseOutput = InputFile.myparse s       -- direct parse from hylolib
          pRelInfo    = P.relations parseOutput
          relInfo     = if translate p
                         then monomodal $ convertToOurType pRelInfo
                         else forceProperties p parseOutput $ convertToOurType pRelInfo
          theory      = if translate p
                          then doTranslate (detectRCLogic pRelInfo) $ P.theory parseOutput
                          else convert relInfo $ P.theory parseOutput
          tasks       = P.tasks parseOutput
          fLang       = langInfo parseOutput

-- add properties specified by the --all-PROP parameters
-- in order to work in case of automatic signature

forceProperties :: Params -> P.ParseOutput -> RelInfo -> RelInfo
forceProperties p po relI
 = foldr addToAll relI (list rels)
   where
         rels = Set.map (\(S.RelSymbol r) -> up r) $ Set.unions $ map (relSymbols . getSignature) theory
         addToAll r = Map.insertWith (\c1 c2 -> nub $ c1 ++ c2) r conds
         conds = map snd $
                   filter fst   [(allTransitive p, Transitive),
                                 (allReflexive  p, Reflexive )]
         theory =  P.theory po

-- assume input formula is relation-changing
-- then it is monomodal, only relation is R
monomodal :: RelInfo -> RelInfo
monomodal _ = Map.fromList [("R", [])]
 -- TODO check parameter and fail if relation other than R used in input file


detectRCLogic :: PRelInfo -> RelationChanging
detectRCLogic prelI
 |  "sb" `elem` rels = Sabotage
 |  "gsb" `elem` rels = Sabotage
 |  "sw"  `elem` rels = Swap
 |  "gsw" `elem` rels = Swap
 |  "br"  `elem` rels = Bridge
 |  "gbr"  `elem` rels = Bridge
 | otherwise = error "does not seem like a relation-changing formula!"
 where rels = map fst prelI


convertToOurType :: PRelInfo -> RelInfo
 -- and add for each relation in the formula, the relevant key
convertToOurType prelI = foldr insertRelProp Map.empty (concatMap convertOne prelI)
 where insertRelProp (rs,pr) = Map.insertWith (++) rs [pr]
       convertOne (r,props)  = concatMap (c r) props
       c r P.Reflexive       = [(up r,Reflexive    )]
       c _ P.Symmetric       = error "Symmetric not handled"
       c r P.Transitive      = [(up r,Transitive   )]
       c r P.Universal       = [(up r,Universal    )]
       c _ (P.InverseOf _)   = error "InverseOf not handled" 
       c r (P.SubsetOf ss)   = [(up r,SubsetOf [ up s | s <- ss])]
       c r (P.Equals ss)     = [(up r,SubsetOf [ up s | s <- ss])]
                               ++ [(up s,SubsetOf [up r]) | s <- ss]
       c _ (P.TClosureOf _)  = error "TClosureOf not handled"
       c _ (P.TRClosureOf _) = error "TRClosureOf not handled"
       c _ P.Functional      = error "Functional not handled"
       c _ P.Injective       = error "Injective not handled"
       c _ P.Difference      = error "Difference not handled"

simpleParse :: Params -> String -> (Theory,RelInfo,LanguageInfo)
simpleParse p s =
 let (t,r,i,_) = parse p $ "signature { automatic } theory { " ++ removeBeginEnd s ++ "}"
 in (t,r,i)
 where removeBeginEnd = unwords . delete "begin" . delete "end" . words

-- convert from hylolib format to htab's
convert :: RelInfo -> [F.Formula S.NomSymbol S.PropSymbol S.RelSymbol]
             -> Formula
convert relI = conv_ relI . foldr (F.:&:) F.Top

conv_ :: RelInfo -> F.Formula S.NomSymbol S.PropSymbol S.RelSymbol
           -> Formula
conv_  _   F.Top               = taut
conv_  _   F.Bot               = neg taut
conv_  _   (F.Prop p)          = prop p
conv_  _   (F.Nom  n)          = nom n
conv_ relI (F.Neg  f)          = neg $ conv_ relI f
conv_ relI (f1 F.:&:    f2)    = conv_ relI f1 `conj` conv_ relI f2
conv_ relI (f1 F.:|:    f2)    = conv_ relI f1 `disj` conv_ relI f2
conv_ relI (f1 F.:-->:  f2)    = conv_ relI f1 `imp`  conv_ relI f2
conv_ relI (f1 F.:<-->: f2)    = conv_ relI f1 `dimp` conv_ relI f2
conv_ relI (F.Diam (S.RelSymbol r) f)        = specialiseDia (up r) relI (conv_ relI f)
conv_ relI (F.Box  (S.RelSymbol r) f)        = specialiseBox (up r) relI (conv_ relI f)
conv_ relI (F.At   n f)        = at        n (conv_ relI f)
conv_ relI (F.Down v f)        = downArrow v (conv_ relI f)
conv_ relI (F.A f)             = univMod     (conv_ relI f)
conv_ relI (F.E f)             = existMod    (conv_ relI f)
conv_ _    f                 = error (show f ++ "not supported")

type Connector = Formula -> Formula

specialiseDia :: String -> RelInfo -> Connector
specialiseDia r relI = specialise r relI (diamond, existMod)

specialiseBox :: String -> RelInfo -> Connector
specialiseBox r relI = specialise r relI (box, univMod)

specialise :: String -> RelInfo -> (String -> Connector, Connector)
                -> Connector
specialise r relI (relational, global)
 | Universal `elem` props  = global
 | otherwise = relational r
 where props = Map.findWithDefault [] r relI


-- COMMON STRUCTURES FOR ALL RELATION-CHANGING TRANSLATIONS --
type S = ( [(String, String)] , Int)    -- Int = next nominal number to use
emptyset :: S -- directly nominal strings (uppercase)
emptyset = ([],0)
-- generate unused nominal and update S
next :: S -> (String,S)
next (ss,n) = ("N" ++ show n, (ss, n + 1))

-- SABOTAGE TRANSLATION --
-- not exactly a union but we're mimicking the article
union :: S -> (String, String) -> S
union (ss,n) nm = (ss ++ [nm], n)
-- macro for translation
belongs :: String -> S -> Formula
belongs n (ss,_) = foldr disj (neg taut) $ set [ (n' y) `conj` At n (n' x) | (x,y) <- ss ]
 where n' = Lit . PosLit . N

-- SWAP TRANSLATION --
inverse :: S -> S
inverse (ss,n) =  (map (\(a,b) -> (b,a)) ss, n)
-- | slightly different from paper: phi must be already translated
isSat :: S -> Formula -> Formula
isSat (ss,_) phi = foldr disj (neg taut) [ n x `conj` At y phi | (x,y) <- ss ]
 where n = Lit . PosLit . N

-- | swap again some pair in S
again :: S -> (String, String) -> S
again (ss,n) xy@(x,y)
  | xy `elem` ss =  ( (y,x):(delete xy ss), n)
  | otherwise    = error "trying to swap again something that is not here"

doTranslate :: RelationChanging -> [F.Formula S.NomSymbol S.PropSymbol S.RelSymbol] -> Formula
doTranslate rc input =  -- TODO detect if sabotage, if bridge, if swap
  case rc of
   Sabotage -> trSab  emptyset bigAnd
   Swap     -> trSwap emptyset bigAnd
   Bridge   -> trBri  emptyset bigAnd
 where bigAnd = convert Map.empty input

trSab :: S -> Formula -> Formula
trSab _ l@(Lit _)           = l
trSab s (Con fs)            = Con (Set.map (trSab s) fs)
trSab s (Dis fs)            = Dis (Set.map (trSab s) fs)
trSab s (At n f)            = At n (trSab s f)
trSab s (Down v f)          = Down v (trSab s f)
trSab s (A f)               = A    (trSab s f)
trSab s (E f)               = E    (trSab s f)
trSab s (Box r f)           = neg $ trSab s (Dia r (neg f))
trSab s (Dia r f)
    | up r `elem` ["R","R1"] =
        case s of
         ([],_)  ->  Dia "R" (trSab s1 f)
         _       ->  Down newNom1 ( Dia "R" ( (neg $ belongs newNom1 s1) `conj` (trSab s1 f)))
    | up r == "SB" =
        Down newNom1 (Dia "R" ( (neg $ belongs newNom1 s2) `conj` (Down newNom2 (trSab s2u12 f)))) 
    | up r == "GSB"     =
        Down newNom1 $ E $ Down newNom2
          $ (Dia "R" ( (neg $ belongs newNom2 s2) `conj` (Down newNom3 $ At newNom1 (trSab s4u23 f))))
    | otherwise         = error ("Relation is not r, r1, sb or gsb: " ++ r)
    where (newNom1,s1) = next s
          (newNom2,s2) = next s1
          s2u12 = s2 `union` (newNom1,newNom2)
          (newNom3,s3) = next s2
          s4u23 = s3 `union` (newNom2,newNom3)

trBri :: S -> Formula -> Formula
trBri _ l@(Lit _)           = l
trBri s (Con fs)            = Con (Set.map (trBri s) fs)
trBri s (Dis fs)            = Dis (Set.map (trBri s) fs)
trBri s (At n f)            = At   n (trBri s f)
trBri s (Down v f)          = Down v (trBri s f)
trBri s (A f)               = A    (trBri s f)
trBri s (E f)               = E    (trBri s f)
trBri s (Box r f)           = neg $ trBri s (Dia r (neg f))
trBri s (Dia r f)
    | up r `elem` ["R","R1"] =
        case s of
         ([],_)  ->  Dia "R" (trBri s1 f)
         _       ->  Down newNom1 $ E $ Down newNom2
                       ( (( At newNom1 (Dia "R" (n newNom2))) `disj` (belongs newNom1 s1))
                         `conj` (trBri s2 f)
                       )
    | up r == "BR" =
        Down newNom1 $ E $ Down newNom2
          (   ( neg $ At newNom1 (Dia "R" (n newNom2)))
            `conj` (neg $ belongs newNom1 s1)
            `conj` (trBri s2u12 f)
          )
    | up r == "GBR"     =
        Down newNom1 $ E $ Down newNom2 $ E $ Down newNom3
          (   ( neg $ At newNom2 (Dia "R" (n newNom3)))
            `conj` (neg $ belongs newNom2 s1)
            `conj` At newNom1 (trBri s4u23 f)
          )
    | otherwise         = error ("Relation is not r, r1, br or gbr: " ++ r)
    where (newNom1,s1) = next s
          (newNom2,s2) = next s1
          s2u12 = s2 `union` (newNom1,newNom2)
          (newNom3,s3) = next s2
          s4u23 = s3 `union` (newNom2,newNom3)
          n = Lit . PosLit . N

trSwap :: S -> Formula -> Formula
trSwap _ l@(Lit _)           = l
trSwap s (Con fs)            = Con (Set.map (trSwap s) fs)
trSwap s (Dis fs)            = Dis (Set.map (trSwap s) fs)
trSwap s (At n f)            = At        n (trSwap s f)
trSwap s (Down v f)          = Down      v (trSwap s f)
trSwap s (A f)               = A    (trSwap s f)
trSwap s (E f)               = E    (trSwap s f)
trSwap s (Box r f)           = neg $ trSwap s (Dia r (neg f))
trSwap s@(ss,_) (Dia r f)
    | up r `elem` ["R","R1"] =
        case s of
         ([],_)  ->  Dia "R" (trSwap s1 f)
         _       ->  (Down newNom1 ( Dia "R" ( (neg $ belongs newNom1 s1) `conj` (trSwap s1 f))))
                     `disj`
                     (isSat (inverse s) (trSwap s f))
    | up r == "SW" =
          ( Down newNom1 (Dia "R" (n newNom1)) `conj` trSwap s f )
        `disj`
          ( Down newNom1 $ Dia "R" 
               $    neg (n newNom1)
                 `conj` neg (belongs newNom1 s)
                 `conj` neg (belongs newNom1 (inverse s))
                 `conj` (Down newNom2 $ trSwap s2u12 f))
        `disj`
          foldr disj (neg taut) [ n y `conj` At x (trSwap (again s (x,y)) f) | (x,y) <- ss ]
    | up r == "GSW" =
          ( (E $ Down newNom1 $ Dia "R" $ n newNom1) `conj` trSwap s f )
        `disj`
          ( Down newNom1 $ E $ Down newNom2 $ Dia "R"
               $    neg (n newNom2)
                 `conj` neg (belongs newNom2 s)
                 `conj` neg (belongs newNom2 (inverse s))
                 `conj` (Down newNom3 $ At newNom1 $ trSwap s4u23 f))
        `disj`
          foldr disj (neg taut) [ trSwap (again s (x,y)) f | (x,y) <- ss ]
    | otherwise         = error ("Relation is not r, r1, sw or gsw: " ++ r)
    where (newNom1,s1) = next s
          (newNom2,s2) = next s1
          s2u12 = s2 `union` (newNom1,newNom2)
          (newNom3,s3) = next s2
          s4u23 = s3 `union` (newNom2,newNom3)
          n = Lit . PosLit . N

type HyLoFormula = F.Formula S.NomSymbol S.PropSymbol S.RelSymbol

encodeValidityTest :: RelInfo -> Formula -> [HyLoFormula] -> Formula
encodeValidityTest relI th fs
 = neg $ conj th (convert relI fs)

encodeSatTest :: RelInfo -> Formula -> [HyLoFormula] -> Formula
encodeSatTest relI th fs
 = conj th (convert relI fs)

encodeRetrieveTask :: RelInfo -> LanguageInfo -> Formula -> [HyLoFormula]
                        -> ([String],[Formula])
encodeRetrieveTask relI fLang theory fs
 = (noms , map (\n -> conj theory (At n (neg $ convert relI fs))) noms)
   where noms = languageNoms fLang

-- CONSTRUCTORS

{- Atoms -}
taut :: Formula
nom  :: S.NomSymbol -> Formula
prop :: S.PropSymbol -> Formula

taut                  = Lit $ PosLit Taut
nom  (S.NomSymbol n)  = Lit $ PosLit $ N $ up n
prop (S.PropSymbol p) = Lit $ PosLit $ P $ up p

{- Modalities -}
box, diamond :: String -> Formula -> Formula
univMod, existMod :: Formula -> Formula
box        r    = Box   r
diamond    r    = Dia   r
univMod    = A
existMod   = E

{- binder -}
downArrow :: S.NomSymbol -> Formula -> Formula
downArrow (S.NomSymbol n) = Down (up n)

{- Hybrid operators -}
at :: S.NomSymbol -> Formula -> Formula
at (S.NomSymbol n) = At (up n)

{- Conjunction and disjunction -}

conj, disj :: Formula -> Formula -> Formula

conj    (Con xs) (Con ys) = Con (Set.union xs ys)
conj     f     c@(Con  _) = conj c f
conj c@(Con xs)   f
    | isTrue f            = c
    | isFalse f           = neg taut
    | otherwise           = Con (Set.insert f xs)
conj     f        f'
    | isTrue f            = f'
    | isFalse f           = neg taut
    | isTrue f'           = f
    | isFalse f'          = neg taut
    | otherwise           = skipSingleton Con (set [f,f'])

disj   (Dis xs)   (Dis ys) = Dis (Set.union xs ys)
disj    f       c@(Dis  _) = disj c f
disj c@(Dis xs)    f
    | isTrue f             = taut
    | isFalse f            = c
    | otherwise            = Dis (Set.insert f xs)
disj    f          f'
    | isTrue f             = taut
    | isFalse f            = f'
    | isTrue f'            = taut
    | isFalse f'           = f
    | otherwise            = skipSingleton Dis (set [f,f'])

dimp :: Formula -> Formula -> Formula
dimp f1 f2 = (neg f1 `disj` f2) `conj` (f1 `disj` neg f2)
-- this form is preferred so as to enhance lazy branching

-- TODO
-- ala Spartacus:
-- when there is no literal in the double implication,
-- use the following form:
--dimp f1 f2 = (f1 `conj` f2) `disj` (neg f1 `conj` neg f2)

imp :: Formula -> Formula -> Formula
imp f1 f2 = neg f1 `disj` f2

skipSingleton :: (Set Formula -> Formula) -> Set Formula -> Formula
skipSingleton c xs
 | Set.size xs == 1 = Set.findMin xs
 | otherwise       = c xs

isTrue, isFalse :: Formula -> Bool
isTrue  (Lit (PosLit Taut)) = True
isTrue   _                  = False
isFalse (Lit (NegLit Taut)) = True
isFalse  _                  = False

-- invariant : neg is only called on literals during
-- the run of the algorithm
neg :: Formula -> Formula
neg (Con l)          = Dis (Set.map neg l)
neg (Dis l)          = Con (Set.map neg l)
neg (At n f)         = At   n (neg f)
neg (Down v f)       = Down v (neg f)
neg (Box r f)        = Dia  r (neg f)
neg (Dia r f)        = Box  r (neg f)
neg (A f)            = E (neg f)
neg (E f)            = A (neg f)
neg (Lit (PosLit a)) = Lit (NegLit a)
neg (Lit (NegLit a)) = Lit (PosLit a)


-- prefixed formula

data PrFormula = PrFormula Prefix Prefix DependencySet Formula
 deriving Eq

instance Show PrFormula where
 show (PrFormula pr spr ds f) = show pr ++ ":" ++ dsShow ds ++ ":" ++ show f

showLess :: PrFormula -> String
showLess (PrFormula pr spr _ f) = show pr ++ ":" ++ show f

prefix :: Prefix -> Prefix -> DependencySet -> Set Formula -> [PrFormula]
prefix p spr bps fs = [PrFormula p spr bps formula|formula <- list fs]

firstPrefixedFormula :: Formula -> PrFormula
firstPrefixedFormula = PrFormula 0 1 dsEmpty

negPr :: PrFormula -> PrFormula
negPr (PrFormula p spr ds f) = PrFormula p spr ds (neg f)

-- formula language

data LanguageInfo = LanguageInfo { languageNoms :: [String] } -- ascending

instance Show LanguageInfo where
 show li = "Input Language:\n|" ++ yesnol "Noms " ( languageNoms li )
  where yesnol s l | null l = "no " ++ s
        yesnol s l = s ++ intercalate ", " l

langInfo :: P.ParseOutput -> LanguageInfo
langInfo po
 = LanguageInfo { languageNoms = noms }
    where noms = nub $ map (\(S.NomSymbol n) -> up n) $ concatMap (list . nomSymbols . getSignature) theory
          theory =  P.theory po

-- composeXX functions follow the idea from
-- "A pattern for almost compositional functions", Bringert and Ranta.
composeMap :: (Formula -> Formula)
           -> (Formula -> Formula)
           -> (Formula -> Formula)
composeMap baseCase g e = case e of
    Con fs     -> Con $ Set.map g fs
    Dis fs     -> Dis $ Set.map g fs
    Dia r f    -> Dia r (g f)
    Box r f    -> Box r (g f)
    At   i f   -> At  i (g f)
    A f        -> A (g f)
    E f        -> E (g f)
    Down x f   -> Down x (g f)
    f          -> baseCase f

replaceVar :: String -> String -> Formula -> Formula
replaceVar v n a@(Lit (PosLit (N v2))) = if v == v2 then Lit (PosLit (N n)) else a
replaceVar v n a@(Lit (NegLit (N v2))) = if v == v2 then Lit (NegLit (N n)) else a
replaceVar v n a@(Down v2 f) = if v == v2 then a   -- variable capture
                                          else Down v2 (replaceVar v n f)
replaceVar v n (At v2 f)   = if v == v2 then At n (replaceVar v n f)
                                        else At v2 (replaceVar v n f)
replaceVar v n f = composeMap id (replaceVar v n) f

-- backjumping

type Dependency = Int
type DependencySet = IntSet.IntSet


-- the ordering of prformula's is used in selecting the next formula in the todo list
-- here we select the one that's most promising for backjumping
instance Ord PrFormula where
 compare (PrFormula pr1 spr1 ds1 f1) (PrFormula pr2 spr2 ds2 f2) =
-- This one seems more performant in many cases:

-- case dsMin ds1 `compare` dsMin ds2 of

-- But this one seems 'fairer' and helps termination on some complicated formulas
  case  IntSet.size ds1  `compare` IntSet.size ds2 of
   LT -> LT
   GT -> GT
   EQ -> compare (pr1,spr1, f1,ds1) (pr2,spr2,f2,ds2)
-- podria cambiarse la lineaa anterior para comparar spr1 y spr 2 

dsUnion :: DependencySet -> DependencySet -> DependencySet
dsUnion = IntSet.union

dsUnions :: [DependencySet] -> DependencySet
dsUnions = IntSet.unions

dsInsert :: Dependency -> DependencySet -> DependencySet
dsInsert = IntSet.insert

dsMember :: Dependency -> DependencySet -> Bool
dsMember = IntSet.member

dsEmpty :: DependencySet
dsEmpty = IntSet.empty

dsMin :: DependencySet -> Int
dsMin ds = maybe 0 fst $ IntSet.minView ds

dsShow :: DependencySet -> String
dsShow = show . IntSet.toList

addDeps :: DependencySet -> PrFormula -> PrFormula
addDeps ds1 (PrFormula p spr ds2 f) = PrFormula p spr (dsUnion ds1 ds2) f

list :: Ord a => Set.Set a -> [a]
list = Set.toList

set :: Ord a => [a] -> Set.Set a
set = Set.fromList

up :: String -> String
up = map toUpper

