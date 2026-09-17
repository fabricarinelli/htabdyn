module HTab.Memory
where

import qualified Data.Set as Set
import HTab.Formula

data MemFormula
     = MLit    Literal
     | MCon   MemFormula MemFormula
     | MDis   MemFormula MemFormula
     | MBox   MemFormula
     | MDia   MemFormula
     | MNeg   MemFormula
     | Re     MemFormula -- ^ Remember
     | Kn                -- ^ Known
  deriving (Eq, Ord )

instance Show MemFormula where
 show (MLit a)   = show a
 show (MCon f1 f2) = "(" ++ show f1 ++ " & " ++ show f2 ++ ")"
 show (MDis f1 f2) = "(" ++ show f1 ++ " v " ++ show f2 ++ ")"
 show (MBox f) = "[](" ++ show f ++ ")"
 show (MDia f) = "<>(" ++ show f ++ ")"
 show (MNeg f) = "¬(" ++ show f ++ ")"
 show (Re f)   = "Re(" ++ show f ++ ")"
 show  Kn      = "Kn"

mtop, mbot :: MemFormula
mtop = MLit $ PosLit Taut
mbot = MLit $ NegLit Taut

-- unsat memory logic formulas
kn, re1, re2, re3 :: MemFormula
kn = Kn
re1 = (MLit (PosLit (P "P"))) `MCon` (Re (MLit (NegLit (P "P")))) 
re2 = (MBox mbot) `MCon` (Re (MDia mtop)) 
re3 = (MDia mbot) `MCon` (Re (MBox mtop)) 
-- bury these unsat formulas in sufficiently deep diamonds
unsats_mem :: [MemFormula]
unsats_mem = concat [ nested f | f <- [kn, re1, re2, re3] ]

-- (interesting) SAT memory logic formulas
rekn1, rekn2, rekn3, rekn4, chain4 :: MemFormula
rekn1 = Re (MDia Kn `MCon` MBox Kn)          -- (r)( <>(k) & [](k) )
rekn2 = MNeg Kn                              -- !(k)
rekn3 = Re ( MDia (MNeg Kn))                 -- (r)<>!(k)
rekn4 = Re (MDia Kn `MCon` MDia (MNeg Kn))   -- (r)( <>(k) & <>!(k) )
chain4 = c [ p "a", q "b", q "c", q "d", MDia
        (c [ q "a", p "b", q "c", q "d", MDia
        (c [ q "a", q "b", p "c", q "d", MDia
        (c [ q "a", q "b", q "c", p "d"])])])]
  where p = MLit . PosLit . P
        q = MLit . NegLit . P
        c = foldr1 MCon

sats_mem :: [MemFormula]
sats_mem = chain4 : concat [ nested f | f <- [rekn1, rekn2, rekn3, rekn4]]

nested :: MemFormula -> [MemFormula]
nested f = [f, MDia f, MDia $ MDia f, MDia $ MDia $ MDia f]


-- ^ translate a memory logic formula into a global sabotage
--   formula where modalities are R and GSB
memGSb :: MemFormula -> Formula
memGSb f_ = struct (mmd f_) `conj` go f_
 where
   struct n = foldr conj neg_s [ nestBox i (neg_s `imp` Dia "R" s) | i <- [0..n]]

   go (Kn)       = neg (Dia "R" s)
   go (Re f)     = Dia "GSB" ( (neg (Dia "R" s)) `conj` go f)
   go (MDia f)   = Dia "R" (neg_s `conj` go f)
   go (MBox f)   = Box "R" (neg_s `imp` go f)
   go (MCon f g) = (go f) `conj` (go g)
   go (MDis f g) = (go f) `disj` (go g)
   go (MLit l)   = Lit l
   go (MNeg f)   = neg (go f)

memGSw :: MemFormula -> Formula
memGSw f_ = struct (mmd f_) `conj` go f_
 where
   struct n = foldr conj neg_s [ nestBox i (neg_s `imp` Dia "R" s) | i <- [0..n]]

   go (Kn)       = neg (Dia "R" s)
   go (Re f)     = Dia "GSW" ( (neg (Dia "R" s)) `conj` go f)
   go (MDia f)   = Dia "R" (neg_s `conj` go f)
   go (MBox f)   = Box "R" (neg_s `imp` go f)
   go (MCon f g) = (go f) `conj` (go g)
   go (MDis f g) = (go f) `disj` (go g)
   go (MLit l)   = Lit l
   go (MNeg f)   = neg (go f)

memGBr :: MemFormula -> Formula
memGBr f_ = struct (mmd f_) `conj` go f_
 where
   struct n = foldr conj taut [ nestBox i neg_s | i <- [0..(n+1)]]

   go (Kn)       = Dia "R" s
   go (Re f)     = Dia "GBR" ( (Dia "R" s) `conj` go f)
   go (MDia f)   = Dia "R" (neg_s `conj` go f)
   go (MBox f)   = Box "R" (neg_s `imp` go f)
   go (MCon f g) = (go f) `conj` (go g)
   go (MDis f g) = (go f) `disj` (go g)
   go (MLit l)   = Lit l
   go (MNeg f)   = neg (go f)

memLSw :: MemFormula -> Formula
memLSw f_ = struct `conj` d (go f_)
  where
   struct = Con $ set
    [ s
    , b neg_s
    , b (neg_s `imp` uniq)
    , b $ b (neg_s `imp` uniq)
    , b $ b $ b (neg_s `imp` uniq)
    , b $ bsw (s `imp` (b $ b $ b (s `imp` b (neg taut))))
    , b $ b $ bsw (s `imp` (b $ b $ b (s `imp` b (neg taut))))
    , bsw $ bsw ( neg_s `imp` dsw (  s `conj` (d (b neg_s `imp` (d $ d (s `conj` d(b(neg_s))))))))
    ]

   go (MDia f)   = Dia "R" (neg_s `conj` go f)
   go (MBox f)   = Box "R" (neg_s `imp` go f)
   go (MCon f g) = (go f) `conj` (go g)
   go (MDis f g) = (go f) `disj` (go g)
   go (MLit l)   = Lit l
   go (MNeg f)   = neg (go f)
   go (Kn)       = neg (d s)
   go (Re f)     = dsw (s `conj` d (go f))

   uniq =        (d (s `conj` (b (neg taut))))
          `conj` bsw (s `imp` b (b neg_s))
   bsw = Box "SW"
   dsw = Dia "SW"

memLBr :: MemFormula -> Formula
memLBr f_ = struct `conj` dbr(neg_s `conj` t `conj` dbr(neg_s `conj` neg_t `conj` go f_))
  where
   struct = Con $ set
            [ s
            , b (neg taut)
            , bbr (s `imp` bbr neg_s)
            , bbr (neg_s `imp` b neg_s)
            ]

   go (MDia f)   = Dia "R" (neg_s_and_neg_t `conj` go f)
   go (MBox f)   = Box "R" (neg_s_and_neg_t `imp` go f)
   go (MCon f g) = (go f) `conj` (go g)
   go (MDis f g) = (go f) `disj` (go g)
   go (MLit l)   = Lit l
   go (MNeg f)   = neg (go f)
   go (Kn)       = d s
   go (Re f)     = dbr( s `conj` dbr ( neg_s `conj` (d s) `conj` (go f)))

   t = Lit (PosLit (P "T"))
   neg_t = Lit (NegLit (P "T"))
   neg_s_and_neg_t = neg_s `conj` neg_t
   dbr = Dia "BR"
   bbr = Box "BR"

memLSb :: MemFormula -> Formula
memLSb f_ = struct `conj` d (go f_)
  where
    struct = Con $ set
     [ s
     , b neg_s
     , b $ d s
     , bsb ( bsb ( s `imp` b (d s)))
     ,   b ( bsb ( s `imp` d (b neg_s )))
     ,   b (   b ( neg_s `imp` d s))


     ,   b ( bsb ( s `imp` ( bsb ( (b neg_s) `imp` (b ( b ( s `imp` b (d s))))))))
     ,   b ( bsb ( s `imp` (   b ( (b neg_s) `imp` (b ( b ( s `imp` d (b neg_s))))))))
     ,   b ( b ( neg_s `imp`( s `imp` d ( b neg_s))))

     ]

    go (MDia f)   = Dia "R" (neg_s `conj` go f)
    go (MBox f)   = Box "R" (neg_s `imp` go f)
    go (MCon f g) = (go f) `conj` (go g)
    go (MDis f g) = (go f) `disj` (go g)
    go (MLit l)   = Lit l
    go (MNeg f)   = neg (go f)
    go (Kn)       = neg (d s)
    go (Re f)     = dsb( s `conj` dsb ( neg (d s) `conj` go f))

    dsb = Dia "SB"
    bsb = Box "SB"


-- helper functions

-- ^ Modal depth of a memory logic formula
mmd :: MemFormula -> Int
mmd Kn         = 0
mmd (MLit _ )  = 0
mmd (MBox f)   = 1 + mmd f
mmd (MDia f)   = 1 + mmd f
mmd (MDis f g) = max (mmd f) (mmd g)
mmd (MCon f g) = max (mmd f) (mmd g)
mmd (MNeg f)   = mmd f
mmd (Re f)     = mmd f

nestBox :: Int -> Formula -> Formula
nestBox 0 f = f
nestBox n f = nestBox (n-1) (Box "R" f)

s, neg_s :: Formula
neg_s = Lit (NegLit (P "S"))
s = Lit (PosLit (P "S"))

set :: Ord a => [a] -> Set.Set a
set = Set.fromList

d, b :: Formula -> Formula
d   = Dia "R"
b   = Box "R"

