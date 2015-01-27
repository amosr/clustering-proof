module Untyped where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

and_rect :: (() -> () -> a1) -> a1
and_rect f =
  f __ __

and_rec :: (() -> () -> a1) -> a1
and_rec f =
  and_rect f

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect x f y =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec x f y =
  eq_rect x f y

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r x h y =
  eq_rec x h y

negb :: Prelude.Bool -> Prelude.Bool
negb b =
  case b of {
   Prelude.True -> Prelude.False;
   Prelude.False -> Prelude.True}

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x y -> x}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) x y -> y}

length :: ([] a1) -> Prelude.Int
length l =
  case l of {
   [] -> 0;
   (:) y l' -> (Prelude.+ 1) (length l')}

app :: ([] a1) -> ([] a1) -> [] a1
app l m =
  case l of {
   [] -> m;
   (:) a l1 -> (:) a (app l1 m)}

compOpp :: Prelude.Ordering -> Prelude.Ordering
compOpp r =
  case r of {
   Prelude.EQ -> Prelude.EQ;
   Prelude.LT -> Prelude.GT;
   Prelude.GT -> Prelude.LT}

compareSpec2Type :: Prelude.Ordering -> Prelude.Ordering
compareSpec2Type c =
  case c of {
   Prelude.EQ -> Prelude.EQ;
   Prelude.LT -> Prelude.LT;
   Prelude.GT -> Prelude.GT}

type CompSpecT a = Prelude.Ordering

compSpec2Type :: a1 -> a1 -> Prelude.Ordering -> CompSpecT a1
compSpec2Type x y c =
  compareSpec2Type c

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
sumbool_rect :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rect f f0 s =
  case s of {
   Prelude.True -> f __;
   Prelude.False -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rec =
  sumbool_rect

plus :: Prelude.Int -> Prelude.Int -> Prelude.Int
plus = (Prelude.+)

nat_iter :: Prelude.Int -> (a1 -> a1) -> a1 -> a1
nat_iter n0 f x =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    x)
    (\n' ->
    f (nat_iter n' f x))
    n0

positive_rect :: (Prelude.Int -> a1 -> a1) -> (Prelude.Int -> a1 -> a1) -> a1
                 -> Prelude.Int -> a1
positive_rect f f0 f1 p =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    f p0 (positive_rect f f0 f1 p0))
    (\p0 ->
    f0 p0 (positive_rect f f0 f1 p0))
    (\_ ->
    f1)
    p

positive_rec :: (Prelude.Int -> a1 -> a1) -> (Prelude.Int -> a1 -> a1) -> a1
                -> Prelude.Int -> a1
positive_rec =
  positive_rect

data N =
   N0
 | Npos Prelude.Int

n_rect :: a1 -> (Prelude.Int -> a1) -> N -> a1
n_rect f f0 n0 =
  case n0 of {
   N0 -> f;
   Npos x -> f0 x}

n_rec :: a1 -> (Prelude.Int -> a1) -> N -> a1
n_rec =
  n_rect

z_rect :: a1 -> (Prelude.Int -> a1) -> (Prelude.Int -> a1) -> Prelude.Int ->
          a1
z_rect f f0 f1 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    f)
    (\x ->
    f0 x)
    (\x ->
    f1 x)
    z

z_rec :: a1 -> (Prelude.Int -> a1) -> (Prelude.Int -> a1) -> Prelude.Int ->
         a1
z_rec =
  z_rect

data Reflect =
   ReflectT
 | ReflectF

iff_reflect :: Prelude.Bool -> Reflect
iff_reflect b =
  case b of {
   Prelude.True -> and_rec (\_ _ -> ReflectT);
   Prelude.False -> and_rec (\_ _ -> ReflectF)}

type T = Prelude.Int

succ :: Prelude.Int -> Prelude.Int
succ x =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p -> (Prelude.* 2)
    (succ p))
    (\p -> ((Prelude..) (Prelude.+ 1) (Prelude.* 2))
    p)
    (\_ -> (Prelude.* 2)
    1)
    x

add :: Prelude.Int -> Prelude.Int -> Prelude.Int
add = (Prelude.+)

add_carry :: Prelude.Int -> Prelude.Int -> Prelude.Int
add_carry x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q -> ((Prelude..) (Prelude.+ 1) (Prelude.* 2))
      (add_carry p q))
      (\q -> (Prelude.* 2)
      (add_carry p q))
      (\_ -> ((Prelude..) (Prelude.+ 1) (Prelude.* 2))
      (succ p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q -> (Prelude.* 2)
      (add_carry p q))
      (\q -> ((Prelude..) (Prelude.+ 1) (Prelude.* 2))
      (add p q))
      (\_ -> (Prelude.* 2)
      (succ p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q -> ((Prelude..) (Prelude.+ 1) (Prelude.* 2))
      (succ q))
      (\q -> (Prelude.* 2)
      (succ q))
      (\_ -> ((Prelude..) (Prelude.+ 1) (Prelude.* 2))
      1)
      y)
    x

pred_double :: Prelude.Int -> Prelude.Int
pred_double x =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p -> ((Prelude..) (Prelude.+ 1) (Prelude.* 2)) ((Prelude.* 2)
    p))
    (\p -> ((Prelude..) (Prelude.+ 1) (Prelude.* 2))
    (pred_double p))
    (\_ ->
    1)
    x

pred :: Prelude.Int -> Prelude.Int
pred x =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p -> (Prelude.* 2)
    p)
    (\p ->
    pred_double p)
    (\_ ->
    1)
    x

pred_N :: Prelude.Int -> N
pred_N x =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p -> Npos ((Prelude.* 2)
    p))
    (\p -> Npos
    (pred_double p))
    (\_ ->
    N0)
    x

data Mask =
   IsNul
 | IsPos Prelude.Int
 | IsNeg

mask_rect :: a1 -> (Prelude.Int -> a1) -> a1 -> Mask -> a1
mask_rect f f0 f1 m =
  case m of {
   IsNul -> f;
   IsPos x -> f0 x;
   IsNeg -> f1}

mask_rec :: a1 -> (Prelude.Int -> a1) -> a1 -> Mask -> a1
mask_rec =
  mask_rect

succ_double_mask :: Mask -> Mask
succ_double_mask x =
  case x of {
   IsNul -> IsPos 1;
   IsPos p -> IsPos (((Prelude..) (Prelude.+ 1) (Prelude.* 2)) p);
   IsNeg -> IsNeg}

double_mask :: Mask -> Mask
double_mask x =
  case x of {
   IsPos p -> IsPos ((Prelude.* 2) p);
   x0 -> x0}

double_pred_mask :: Prelude.Int -> Mask
double_pred_mask x =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p -> IsPos ((Prelude.* 2) ((Prelude.* 2)
    p)))
    (\p -> IsPos ((Prelude.* 2)
    (pred_double p)))
    (\_ ->
    IsNul)
    x

pred_mask :: Mask -> Mask
pred_mask p =
  case p of {
   IsPos q ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 -> IsPos
      (pred q))
      (\p0 -> IsPos
      (pred q))
      (\_ ->
      IsNul)
      q;
   _ -> IsNeg}

sub_mask :: Prelude.Int -> Prelude.Int -> Mask
sub_mask x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q ->
      double_mask (sub_mask p q))
      (\q ->
      succ_double_mask (sub_mask p q))
      (\_ -> IsPos ((Prelude.* 2)
      p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q ->
      succ_double_mask (sub_mask_carry p q))
      (\q ->
      double_mask (sub_mask p q))
      (\_ -> IsPos
      (pred_double p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p ->
      IsNeg)
      (\p ->
      IsNeg)
      (\_ ->
      IsNul)
      y)
    x

sub_mask_carry :: Prelude.Int -> Prelude.Int -> Mask
sub_mask_carry x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q ->
      succ_double_mask (sub_mask_carry p q))
      (\q ->
      double_mask (sub_mask p q))
      (\_ -> IsPos
      (pred_double p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q ->
      double_mask (sub_mask_carry p q))
      (\q ->
      succ_double_mask (sub_mask_carry p q))
      (\_ ->
      double_pred_mask p)
      y)
    (\_ ->
    IsNeg)
    x

sub :: Prelude.Int -> Prelude.Int -> Prelude.Int
sub x y =
  case sub_mask x y of {
   IsPos z -> z;
   _ -> 1}

mul :: Prelude.Int -> Prelude.Int -> Prelude.Int
mul = (Prelude.*)

iter :: Prelude.Int -> (a1 -> a1) -> a1 -> a1
iter n0 f x =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\n' ->
    f (iter n' f (iter n' f x)))
    (\n' ->
    iter n' f (iter n' f x))
    (\_ ->
    f x)
    n0

pow :: Prelude.Int -> Prelude.Int -> Prelude.Int
pow x y =
  iter y (mul x) 1

square :: Prelude.Int -> Prelude.Int
square p =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 -> ((Prelude..) (Prelude.+ 1) (Prelude.* 2)) ((Prelude.* 2)
    (add (square p0) p0)))
    (\p0 -> (Prelude.* 2) ((Prelude.* 2)
    (square p0)))
    (\_ ->
    1)
    p

div2 :: Prelude.Int -> Prelude.Int
div2 p =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    p0)
    (\p0 ->
    p0)
    (\_ ->
    1)
    p

div2_up :: Prelude.Int -> Prelude.Int
div2_up p =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    succ p0)
    (\p0 ->
    p0)
    (\_ ->
    1)
    p

size_nat :: Prelude.Int -> Prelude.Int
size_nat p =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 -> (Prelude.+ 1)
    (size_nat p0))
    (\p0 -> (Prelude.+ 1)
    (size_nat p0))
    (\_ -> (Prelude.+ 1)
    0)
    p

size :: Prelude.Int -> Prelude.Int
size p =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    succ (size p0))
    (\p0 ->
    succ (size p0))
    (\_ ->
    1)
    p

compare_cont :: Prelude.Int -> Prelude.Int -> Prelude.Ordering ->
                Prelude.Ordering
compare_cont x y r =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q ->
      compare_cont p q r)
      (\q ->
      compare_cont p q Prelude.GT)
      (\_ ->
      Prelude.GT)
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q ->
      compare_cont p q Prelude.LT)
      (\q ->
      compare_cont p q r)
      (\_ ->
      Prelude.GT)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q ->
      Prelude.LT)
      (\q ->
      Prelude.LT)
      (\_ ->
      r)
      y)
    x

compare :: Prelude.Int -> Prelude.Int -> Prelude.Ordering
compare x y =
  compare_cont x y Prelude.EQ

min :: Prelude.Int -> Prelude.Int -> Prelude.Int
min p p' =
  case compare p p' of {
   Prelude.GT -> p';
   _ -> p}

max :: Prelude.Int -> Prelude.Int -> Prelude.Int
max p p' =
  case compare p p' of {
   Prelude.GT -> p;
   _ -> p'}

eqb :: Prelude.Int -> Prelude.Int -> Prelude.Bool
eqb p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q0 ->
      eqb p0 q0)
      (\p1 ->
      Prelude.False)
      (\_ ->
      Prelude.False)
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p1 ->
      Prelude.False)
      (\q0 ->
      eqb p0 q0)
      (\_ ->
      Prelude.False)
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 ->
      Prelude.False)
      (\p0 ->
      Prelude.False)
      (\_ ->
      Prelude.True)
      q)
    p

leb :: Prelude.Int -> Prelude.Int -> Prelude.Bool
leb x y =
  case compare x y of {
   Prelude.GT -> Prelude.False;
   _ -> Prelude.True}

ltb :: Prelude.Int -> Prelude.Int -> Prelude.Bool
ltb x y =
  case compare x y of {
   Prelude.LT -> Prelude.True;
   _ -> Prelude.False}

sqrtrem_step :: (Prelude.Int -> Prelude.Int) -> (Prelude.Int -> Prelude.Int)
                -> ((,) Prelude.Int Mask) -> (,) Prelude.Int Mask
sqrtrem_step f g p =
  case p of {
   (,) s y ->
    case y of {
     IsPos r ->
      let {s' = ((Prelude..) (Prelude.+ 1) (Prelude.* 2)) ((Prelude.* 2) s)}
      in
      let {r' = g (f r)} in
      case leb s' r' of {
       Prelude.True -> (,) (((Prelude..) (Prelude.+ 1) (Prelude.* 2)) s)
        (sub_mask r' s');
       Prelude.False -> (,) ((Prelude.* 2) s) (IsPos r')};
     _ -> (,) ((Prelude.* 2) s)
      (sub_mask (g (f 1)) ((Prelude.* 2) ((Prelude.* 2) 1)))}}

sqrtrem :: Prelude.Int -> (,) Prelude.Int Mask
sqrtrem p =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p1 ->
      sqrtrem_step (\x -> ((Prelude..) (Prelude.+ 1) (Prelude.* 2)) x) (\x ->
        ((Prelude..) (Prelude.+ 1) (Prelude.* 2)) x) (sqrtrem p1))
      (\p1 ->
      sqrtrem_step (\x -> (Prelude.* 2) x) (\x ->
        ((Prelude..) (Prelude.+ 1) (Prelude.* 2)) x) (sqrtrem p1))
      (\_ -> (,) 1 (IsPos ((Prelude.* 2)
      1)))
      p0)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p1 ->
      sqrtrem_step (\x -> ((Prelude..) (Prelude.+ 1) (Prelude.* 2)) x) (\x ->
        (Prelude.* 2) x) (sqrtrem p1))
      (\p1 ->
      sqrtrem_step (\x -> (Prelude.* 2) x) (\x -> (Prelude.* 2) x)
        (sqrtrem p1))
      (\_ -> (,) 1 (IsPos
      1))
      p0)
    (\_ -> (,) 1
    IsNul)
    p

sqrt :: Prelude.Int -> Prelude.Int
sqrt p =
  fst (sqrtrem p)

gcdn :: Prelude.Int -> Prelude.Int -> Prelude.Int -> Prelude.Int
gcdn n0 a b =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    1)
    (\n1 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\a' ->
      (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
        (\b' ->
        case compare a' b' of {
         Prelude.EQ -> a;
         Prelude.LT -> gcdn n1 (sub b' a') a;
         Prelude.GT -> gcdn n1 (sub a' b') b})
        (\b0 ->
        gcdn n1 a b0)
        (\_ ->
        1)
        b)
      (\a0 ->
      (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
        (\p ->
        gcdn n1 a0 b)
        (\b0 -> (Prelude.* 2)
        (gcdn n1 a0 b0))
        (\_ ->
        1)
        b)
      (\_ ->
      1)
      a)
    n0

gcd :: Prelude.Int -> Prelude.Int -> Prelude.Int
gcd a b =
  gcdn (plus (size_nat a) (size_nat b)) a b

ggcdn :: Prelude.Int -> Prelude.Int -> Prelude.Int -> (,) Prelude.Int
         ((,) Prelude.Int Prelude.Int)
ggcdn n0 a b =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> (,) 1 ((,) a
    b))
    (\n1 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\a' ->
      (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
        (\b' ->
        case compare a' b' of {
         Prelude.EQ -> (,) a ((,) 1 1);
         Prelude.LT ->
          case ggcdn n1 (sub b' a') a of {
           (,) g p ->
            case p of {
             (,) ba aa -> (,) g ((,) aa (add aa ((Prelude.* 2) ba)))}};
         Prelude.GT ->
          case ggcdn n1 (sub a' b') b of {
           (,) g p ->
            case p of {
             (,) ab bb -> (,) g ((,) (add bb ((Prelude.* 2) ab)) bb)}}})
        (\b0 ->
        case ggcdn n1 a b0 of {
         (,) g p ->
          case p of {
           (,) aa bb -> (,) g ((,) aa ((Prelude.* 2) bb))}})
        (\_ -> (,) 1 ((,) a
        1))
        b)
      (\a0 ->
      (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
        (\p ->
        case ggcdn n1 a0 b of {
         (,) g p0 ->
          case p0 of {
           (,) aa bb -> (,) g ((,) ((Prelude.* 2) aa) bb)}})
        (\b0 ->
        case ggcdn n1 a0 b0 of {
         (,) g p -> (,) ((Prelude.* 2) g) p})
        (\_ -> (,) 1 ((,) a
        1))
        b)
      (\_ -> (,) 1 ((,) 1
      b))
      a)
    n0

ggcd :: Prelude.Int -> Prelude.Int -> (,) Prelude.Int
        ((,) Prelude.Int Prelude.Int)
ggcd a b =
  ggcdn (plus (size_nat a) (size_nat b)) a b

nsucc_double :: N -> N
nsucc_double x =
  case x of {
   N0 -> Npos 1;
   Npos p -> Npos (((Prelude..) (Prelude.+ 1) (Prelude.* 2)) p)}

ndouble :: N -> N
ndouble n0 =
  case n0 of {
   N0 -> N0;
   Npos p -> Npos ((Prelude.* 2) p)}

lor :: Prelude.Int -> Prelude.Int -> Prelude.Int
lor p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q0 -> ((Prelude..) (Prelude.+ 1) (Prelude.* 2))
      (lor p0 q0))
      (\q0 -> ((Prelude..) (Prelude.+ 1) (Prelude.* 2))
      (lor p0 q0))
      (\_ ->
      p)
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q0 -> ((Prelude..) (Prelude.+ 1) (Prelude.* 2))
      (lor p0 q0))
      (\q0 -> (Prelude.* 2)
      (lor p0 q0))
      (\_ -> ((Prelude..) (Prelude.+ 1) (Prelude.* 2))
      p0)
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 ->
      q)
      (\q0 -> ((Prelude..) (Prelude.+ 1) (Prelude.* 2))
      q0)
      (\_ ->
      q)
      q)
    p

land :: Prelude.Int -> Prelude.Int -> N
land p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q0 ->
      nsucc_double (land p0 q0))
      (\q0 ->
      ndouble (land p0 q0))
      (\_ -> Npos
      1)
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q0 ->
      ndouble (land p0 q0))
      (\q0 ->
      ndouble (land p0 q0))
      (\_ ->
      N0)
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 -> Npos
      1)
      (\q0 ->
      N0)
      (\_ -> Npos
      1)
      q)
    p

ldiff :: Prelude.Int -> Prelude.Int -> N
ldiff p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q0 ->
      ndouble (ldiff p0 q0))
      (\q0 ->
      nsucc_double (ldiff p0 q0))
      (\_ -> Npos ((Prelude.* 2)
      p0))
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q0 ->
      ndouble (ldiff p0 q0))
      (\q0 ->
      ndouble (ldiff p0 q0))
      (\_ -> Npos
      p)
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 ->
      N0)
      (\q0 -> Npos
      1)
      (\_ ->
      N0)
      q)
    p

lxor :: Prelude.Int -> Prelude.Int -> N
lxor p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q0 ->
      ndouble (lxor p0 q0))
      (\q0 ->
      nsucc_double (lxor p0 q0))
      (\_ -> Npos ((Prelude.* 2)
      p0))
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q0 ->
      nsucc_double (lxor p0 q0))
      (\q0 ->
      ndouble (lxor p0 q0))
      (\_ -> Npos (((Prelude..) (Prelude.+ 1) (Prelude.* 2))
      p0))
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q0 -> Npos ((Prelude.* 2)
      q0))
      (\q0 -> Npos (((Prelude..) (Prelude.+ 1) (Prelude.* 2))
      q0))
      (\_ ->
      N0)
      q)
    p

shiftl_nat :: Prelude.Int -> Prelude.Int -> Prelude.Int
shiftl_nat p n0 =
  nat_iter n0 (\x -> (Prelude.* 2) x) p

shiftr_nat :: Prelude.Int -> Prelude.Int -> Prelude.Int
shiftr_nat p n0 =
  nat_iter n0 div2 p

shiftl :: Prelude.Int -> N -> Prelude.Int
shiftl p n0 =
  case n0 of {
   N0 -> p;
   Npos n1 -> iter n1 (\x -> (Prelude.* 2) x) p}

shiftr :: Prelude.Int -> N -> Prelude.Int
shiftr p n0 =
  case n0 of {
   N0 -> p;
   Npos n1 -> iter n1 div2 p}

testbit_nat :: Prelude.Int -> Prelude.Int -> Prelude.Bool
testbit_nat p n0 =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      Prelude.True)
      (\n' ->
      testbit_nat p0 n')
      n0)
    (\p0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      Prelude.False)
      (\n' ->
      testbit_nat p0 n')
      n0)
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      Prelude.True)
      (\n1 ->
      Prelude.False)
      n0)
    p

testbit :: Prelude.Int -> N -> Prelude.Bool
testbit p n0 =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    case n0 of {
     N0 -> Prelude.True;
     Npos n1 -> testbit p0 (pred_N n1)})
    (\p0 ->
    case n0 of {
     N0 -> Prelude.False;
     Npos n1 -> testbit p0 (pred_N n1)})
    (\_ ->
    case n0 of {
     N0 -> Prelude.True;
     Npos p0 -> Prelude.False})
    p

iter_op :: (a1 -> a1 -> a1) -> Prelude.Int -> a1 -> a1
iter_op op p a =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    op a (iter_op op p0 (op a a)))
    (\p0 ->
    iter_op op p0 (op a a))
    (\_ ->
    a)
    p

to_nat :: Prelude.Int -> Prelude.Int
to_nat x =
  iter_op plus x ((Prelude.+ 1) 0)

of_nat :: Prelude.Int -> Prelude.Int
of_nat n0 =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    1)
    (\x ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      1)
      (\n1 ->
      succ (of_nat x))
      x)
    n0

of_succ_nat :: Prelude.Int -> Prelude.Int
of_succ_nat n0 =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    1)
    (\x ->
    succ (of_succ_nat x))
    n0

eq_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
eq_dec x y =
  positive_rec (\p h y0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Prelude.True p) (\_ -> Prelude.False)
        (h p0))
      (\p0 ->
      Prelude.False)
      (\_ ->
      Prelude.False)
      y0) (\p h y0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 ->
      Prelude.False)
      (\p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Prelude.True p) (\_ -> Prelude.False)
        (h p0))
      (\_ ->
      Prelude.False)
      y0) (\y0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p ->
      Prelude.False)
      (\p ->
      Prelude.False)
      (\_ ->
      Prelude.True)
      y0) x y

peano_rect :: a1 -> (Prelude.Int -> a1 -> a1) -> Prelude.Int -> a1
peano_rect a f p =
  let {
   f2 = peano_rect (f 1 a) (\p0 x ->
          f (succ ((Prelude.* 2) p0)) (f ((Prelude.* 2) p0) x))}
  in
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\q ->
    f ((Prelude.* 2) q) (f2 q))
    (\q ->
    f2 q)
    (\_ ->
    a)
    p

peano_rec :: a1 -> (Prelude.Int -> a1 -> a1) -> Prelude.Int -> a1
peano_rec =
  peano_rect

data PeanoView =
   PeanoOne
 | PeanoSucc Prelude.Int PeanoView

peanoView_rect :: a1 -> (Prelude.Int -> PeanoView -> a1 -> a1) -> Prelude.Int
                  -> PeanoView -> a1
peanoView_rect f f0 p p0 =
  case p0 of {
   PeanoOne -> f;
   PeanoSucc p1 p2 -> f0 p1 p2 (peanoView_rect f f0 p1 p2)}

peanoView_rec :: a1 -> (Prelude.Int -> PeanoView -> a1 -> a1) -> Prelude.Int
                 -> PeanoView -> a1
peanoView_rec =
  peanoView_rect

peanoView_xO :: Prelude.Int -> PeanoView -> PeanoView
peanoView_xO p q =
  case q of {
   PeanoOne -> PeanoSucc 1 PeanoOne;
   PeanoSucc p0 q0 -> PeanoSucc (succ ((Prelude.* 2) p0)) (PeanoSucc
    ((Prelude.* 2) p0) (peanoView_xO p0 q0))}

peanoView_xI :: Prelude.Int -> PeanoView -> PeanoView
peanoView_xI p q =
  case q of {
   PeanoOne -> PeanoSucc (succ 1) (PeanoSucc 1 PeanoOne);
   PeanoSucc p0 q0 -> PeanoSucc
    (succ (((Prelude..) (Prelude.+ 1) (Prelude.* 2)) p0)) (PeanoSucc
    (((Prelude..) (Prelude.+ 1) (Prelude.* 2)) p0) (peanoView_xI p0 q0))}

peanoView :: Prelude.Int -> PeanoView
peanoView p =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    peanoView_xI p0 (peanoView p0))
    (\p0 ->
    peanoView_xO p0 (peanoView p0))
    (\_ ->
    PeanoOne)
    p

peanoView_iter :: a1 -> (Prelude.Int -> a1 -> a1) -> Prelude.Int -> PeanoView
                  -> a1
peanoView_iter a f p q =
  case q of {
   PeanoOne -> a;
   PeanoSucc p0 q0 -> f p0 (peanoView_iter a f p0 q0)}

eqb_spec :: Prelude.Int -> Prelude.Int -> Reflect
eqb_spec x y =
  iff_reflect (eqb x y)

switch_Eq :: Prelude.Ordering -> Prelude.Ordering -> Prelude.Ordering
switch_Eq c c' =
  case c' of {
   Prelude.EQ -> c;
   x -> x}

mask2cmp :: Mask -> Prelude.Ordering
mask2cmp p =
  case p of {
   IsNul -> Prelude.EQ;
   IsPos p0 -> Prelude.GT;
   IsNeg -> Prelude.LT}

leb_spec0 :: Prelude.Int -> Prelude.Int -> Reflect
leb_spec0 x y =
  iff_reflect (leb x y)

ltb_spec0 :: Prelude.Int -> Prelude.Int -> Reflect
ltb_spec0 x y =
  iff_reflect (ltb x y)

max_case_strong :: Prelude.Int -> Prelude.Int -> (Prelude.Int -> Prelude.Int
                   -> () -> a1 -> a1) -> (() -> a1) -> (() -> a1) -> a1
max_case_strong n0 m compat hl hr =
  let {c = compSpec2Type n0 m (compare n0 m)} in
  case c of {
   Prelude.GT -> compat n0 (max n0 m) __ (hl __);
   _ -> compat m (max n0 m) __ (hr __)}

max_case :: Prelude.Int -> Prelude.Int -> (Prelude.Int -> Prelude.Int -> ()
            -> a1 -> a1) -> a1 -> a1 -> a1
max_case n0 m x x0 x1 =
  max_case_strong n0 m x (\_ -> x0) (\_ -> x1)

max_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
max_dec n0 m =
  max_case n0 m (\x y _ h0 -> h0) Prelude.True Prelude.False

min_case_strong :: Prelude.Int -> Prelude.Int -> (Prelude.Int -> Prelude.Int
                   -> () -> a1 -> a1) -> (() -> a1) -> (() -> a1) -> a1
min_case_strong n0 m compat hl hr =
  let {c = compSpec2Type n0 m (compare n0 m)} in
  case c of {
   Prelude.GT -> compat m (min n0 m) __ (hr __);
   _ -> compat n0 (min n0 m) __ (hl __)}

min_case :: Prelude.Int -> Prelude.Int -> (Prelude.Int -> Prelude.Int -> ()
            -> a1 -> a1) -> a1 -> a1 -> a1
min_case n0 m x x0 x1 =
  min_case_strong n0 m x (\_ -> x0) (\_ -> x1)

min_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
min_dec n0 m =
  min_case n0 m (\x y _ h0 -> h0) Prelude.True Prelude.False

max_case_strong0 :: Prelude.Int -> Prelude.Int -> (() -> a1) -> (() -> a1) ->
                    a1
max_case_strong0 n0 m x x0 =
  max_case_strong n0 m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

max_case0 :: Prelude.Int -> Prelude.Int -> a1 -> a1 -> a1
max_case0 n0 m x x0 =
  max_case_strong0 n0 m (\_ -> x) (\_ -> x0)

max_dec0 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
max_dec0 =
  max_dec

min_case_strong0 :: Prelude.Int -> Prelude.Int -> (() -> a1) -> (() -> a1) ->
                    a1
min_case_strong0 n0 m x x0 =
  min_case_strong n0 m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

min_case0 :: Prelude.Int -> Prelude.Int -> a1 -> a1 -> a1
min_case0 n0 m x x0 =
  min_case_strong0 n0 m (\_ -> x) (\_ -> x0)

min_dec0 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
min_dec0 =
  min_dec

type T0 = N

zero :: N
zero =
  N0

one :: N
one =
  Npos 1

two :: N
two =
  Npos ((Prelude.* 2) 1)

succ_double :: N -> N
succ_double x =
  case x of {
   N0 -> Npos 1;
   Npos p -> Npos (((Prelude..) (Prelude.+ 1) (Prelude.* 2)) p)}

double :: N -> N
double n0 =
  case n0 of {
   N0 -> N0;
   Npos p -> Npos ((Prelude.* 2) p)}

succ0 :: N -> N
succ0 n0 =
  case n0 of {
   N0 -> Npos 1;
   Npos p -> Npos (succ p)}

pred0 :: N -> N
pred0 n0 =
  case n0 of {
   N0 -> N0;
   Npos p -> pred_N p}

succ_pos :: N -> Prelude.Int
succ_pos n0 =
  case n0 of {
   N0 -> 1;
   Npos p -> succ p}

add0 :: N -> N -> N
add0 n0 m =
  case n0 of {
   N0 -> m;
   Npos p ->
    case m of {
     N0 -> n0;
     Npos q -> Npos (add p q)}}

sub0 :: N -> N -> N
sub0 n0 m =
  case n0 of {
   N0 -> N0;
   Npos n' ->
    case m of {
     N0 -> n0;
     Npos m' ->
      case sub_mask n' m' of {
       IsPos p -> Npos p;
       _ -> N0}}}

mul0 :: N -> N -> N
mul0 n0 m =
  case n0 of {
   N0 -> N0;
   Npos p ->
    case m of {
     N0 -> N0;
     Npos q -> Npos (mul p q)}}

compare0 :: N -> N -> Prelude.Ordering
compare0 n0 m =
  case n0 of {
   N0 ->
    case m of {
     N0 -> Prelude.EQ;
     Npos m' -> Prelude.LT};
   Npos n' ->
    case m of {
     N0 -> Prelude.GT;
     Npos m' -> compare n' m'}}

eqb0 :: N -> N -> Prelude.Bool
eqb0 n0 m =
  case n0 of {
   N0 ->
    case m of {
     N0 -> Prelude.True;
     Npos p -> Prelude.False};
   Npos p ->
    case m of {
     N0 -> Prelude.False;
     Npos q -> eqb p q}}

leb0 :: N -> N -> Prelude.Bool
leb0 x y =
  case compare0 x y of {
   Prelude.GT -> Prelude.False;
   _ -> Prelude.True}

ltb0 :: N -> N -> Prelude.Bool
ltb0 x y =
  case compare0 x y of {
   Prelude.LT -> Prelude.True;
   _ -> Prelude.False}

min0 :: N -> N -> N
min0 n0 n' =
  case compare0 n0 n' of {
   Prelude.GT -> n';
   _ -> n0}

max0 :: N -> N -> N
max0 n0 n' =
  case compare0 n0 n' of {
   Prelude.GT -> n0;
   _ -> n'}

div0 :: N -> N
div0 n0 =
  case n0 of {
   N0 -> N0;
   Npos p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p -> Npos
      p)
      (\p -> Npos
      p)
      (\_ ->
      N0)
      p0}

even :: N -> Prelude.Bool
even n0 =
  case n0 of {
   N0 -> Prelude.True;
   Npos p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 ->
      Prelude.False)
      (\p0 ->
      Prelude.True)
      (\_ ->
      Prelude.False)
      p}

odd :: N -> Prelude.Bool
odd n0 =
  negb (even n0)

pow0 :: N -> N -> N
pow0 n0 p =
  case p of {
   N0 -> Npos 1;
   Npos p0 ->
    case n0 of {
     N0 -> N0;
     Npos q -> Npos (pow q p0)}}

square0 :: N -> N
square0 n0 =
  case n0 of {
   N0 -> N0;
   Npos p -> Npos (square p)}

log2 :: N -> N
log2 n0 =
  case n0 of {
   N0 -> N0;
   Npos p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p -> Npos
      (size p))
      (\p -> Npos
      (size p))
      (\_ ->
      N0)
      p0}

size0 :: N -> N
size0 n0 =
  case n0 of {
   N0 -> N0;
   Npos p -> Npos (size p)}

size_nat0 :: N -> Prelude.Int
size_nat0 n0 =
  case n0 of {
   N0 -> 0;
   Npos p -> size_nat p}

pos_div_eucl :: Prelude.Int -> N -> (,) N N
pos_div_eucl a b =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {r' = succ_double r} in
      case leb0 b r' of {
       Prelude.True -> (,) (succ_double q) (sub0 r' b);
       Prelude.False -> (,) (double q) r'}})
    (\a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {r' = double r} in
      case leb0 b r' of {
       Prelude.True -> (,) (succ_double q) (sub0 r' b);
       Prelude.False -> (,) (double q) r'}})
    (\_ ->
    case b of {
     N0 -> (,) N0 (Npos 1);
     Npos p ->
      (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
        (\p0 -> (,) N0 (Npos
        1))
        (\p0 -> (,) N0 (Npos
        1))
        (\_ -> (,) (Npos 1)
        N0)
        p})
    a

div_eucl :: N -> N -> (,) N N
div_eucl a b =
  case a of {
   N0 -> (,) N0 N0;
   Npos na ->
    case b of {
     N0 -> (,) N0 a;
     Npos p -> pos_div_eucl na b}}

div :: N -> N -> N
div a b =
  fst (div_eucl a b)

modulo :: N -> N -> N
modulo a b =
  snd (div_eucl a b)

gcd0 :: N -> N -> N
gcd0 a b =
  case a of {
   N0 -> b;
   Npos p ->
    case b of {
     N0 -> a;
     Npos q -> Npos (gcd p q)}}

ggcd0 :: N -> N -> (,) N ((,) N N)
ggcd0 a b =
  case a of {
   N0 -> (,) b ((,) N0 (Npos 1));
   Npos p ->
    case b of {
     N0 -> (,) a ((,) (Npos 1) N0);
     Npos q ->
      case ggcd p q of {
       (,) g p0 ->
        case p0 of {
         (,) aa bb -> (,) (Npos g) ((,) (Npos aa) (Npos bb))}}}}

sqrtrem0 :: N -> (,) N N
sqrtrem0 n0 =
  case n0 of {
   N0 -> (,) N0 N0;
   Npos p ->
    case sqrtrem p of {
     (,) s m ->
      case m of {
       IsPos r -> (,) (Npos s) (Npos r);
       _ -> (,) (Npos s) N0}}}

sqrt0 :: N -> N
sqrt0 n0 =
  case n0 of {
   N0 -> N0;
   Npos p -> Npos (sqrt p)}

lor0 :: N -> N -> N
lor0 n0 m =
  case n0 of {
   N0 -> m;
   Npos p ->
    case m of {
     N0 -> n0;
     Npos q -> Npos (lor p q)}}

land0 :: N -> N -> N
land0 n0 m =
  case n0 of {
   N0 -> N0;
   Npos p ->
    case m of {
     N0 -> N0;
     Npos q -> land p q}}

ldiff0 :: N -> N -> N
ldiff0 n0 m =
  case n0 of {
   N0 -> N0;
   Npos p ->
    case m of {
     N0 -> n0;
     Npos q -> ldiff p q}}

lxor0 :: N -> N -> N
lxor0 n0 m =
  case n0 of {
   N0 -> m;
   Npos p ->
    case m of {
     N0 -> n0;
     Npos q -> lxor p q}}

shiftl_nat0 :: N -> Prelude.Int -> N
shiftl_nat0 a n0 =
  nat_iter n0 double a

shiftr_nat0 :: N -> Prelude.Int -> N
shiftr_nat0 a n0 =
  nat_iter n0 div0 a

shiftl0 :: N -> N -> N
shiftl0 a n0 =
  case a of {
   N0 -> N0;
   Npos a0 -> Npos (shiftl a0 n0)}

shiftr0 :: N -> N -> N
shiftr0 a n0 =
  case n0 of {
   N0 -> a;
   Npos p -> iter p div0 a}

testbit_nat0 :: N -> Prelude.Int -> Prelude.Bool
testbit_nat0 a =
  case a of {
   N0 -> (\x -> Prelude.False);
   Npos p -> testbit_nat p}

testbit0 :: N -> N -> Prelude.Bool
testbit0 a n0 =
  case a of {
   N0 -> Prelude.False;
   Npos p -> testbit p n0}

to_nat0 :: N -> Prelude.Int
to_nat0 a =
  case a of {
   N0 -> 0;
   Npos p -> to_nat p}

of_nat0 :: Prelude.Int -> N
of_nat0 n0 =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    N0)
    (\n' -> Npos
    (of_succ_nat n'))
    n0

iter0 :: N -> (a1 -> a1) -> a1 -> a1
iter0 n0 f x =
  case n0 of {
   N0 -> x;
   Npos p -> iter p f x}

eq_dec0 :: N -> N -> Prelude.Bool
eq_dec0 n0 m =
  n_rec (\m0 ->
    case m0 of {
     N0 -> Prelude.True;
     Npos p -> Prelude.False}) (\p m0 ->
    case m0 of {
     N0 -> Prelude.False;
     Npos p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Prelude.True p) (\_ -> Prelude.False)
        (eq_dec p p0)}) n0 m

discr :: N -> Prelude.Maybe Prelude.Int
discr n0 =
  case n0 of {
   N0 -> Prelude.Nothing;
   Npos p -> Prelude.Just p}

binary_rect :: a1 -> (N -> a1 -> a1) -> (N -> a1 -> a1) -> N -> a1
binary_rect f0 f2 fS2 n0 =
  let {f2' = \p -> f2 (Npos p)} in
  let {fS2' = \p -> fS2 (Npos p)} in
  case n0 of {
   N0 -> f0;
   Npos p -> positive_rect fS2' f2' (fS2 N0 f0) p}

binary_rec :: a1 -> (N -> a1 -> a1) -> (N -> a1 -> a1) -> N -> a1
binary_rec =
  binary_rect

peano_rect0 :: a1 -> (N -> a1 -> a1) -> N -> a1
peano_rect0 f0 f n0 =
  let {f' = \p -> f (Npos p)} in
  case n0 of {
   N0 -> f0;
   Npos p -> peano_rect (f N0 f0) f' p}

peano_rec0 :: a1 -> (N -> a1 -> a1) -> N -> a1
peano_rec0 =
  peano_rect0

leb_spec1 :: N -> N -> Reflect
leb_spec1 x y =
  iff_reflect (leb0 x y)

ltb_spec1 :: N -> N -> Reflect
ltb_spec1 x y =
  iff_reflect (ltb0 x y)

recursion :: a1 -> (N -> a1 -> a1) -> N -> a1
recursion =
  peano_rect0

sqrt_up :: N -> N
sqrt_up a =
  case compare0 N0 a of {
   Prelude.LT -> succ0 (sqrt0 (pred0 a));
   _ -> N0}

log2_up :: N -> N
log2_up a =
  case compare0 (Npos 1) a of {
   Prelude.LT -> succ0 (log2 (pred0 a));
   _ -> N0}

lcm :: N -> N -> N
lcm a b =
  mul0 a (div b (gcd0 a b))

eqb_spec0 :: N -> N -> Reflect
eqb_spec0 x y =
  iff_reflect (eqb0 x y)

b2n :: Prelude.Bool -> N
b2n b =
  case b of {
   Prelude.True -> Npos 1;
   Prelude.False -> N0}

setbit :: N -> N -> N
setbit a n0 =
  lor0 a (shiftl0 (Npos 1) n0)

clearbit :: N -> N -> N
clearbit a n0 =
  ldiff0 a (shiftl0 (Npos 1) n0)

ones :: N -> N
ones n0 =
  pred0 (shiftl0 (Npos 1) n0)

lnot :: N -> N -> N
lnot a n0 =
  lxor0 a (ones n0)

max_case_strong1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
max_case_strong1 n0 m compat hl hr =
  let {c = compSpec2Type n0 m (compare0 n0 m)} in
  case c of {
   Prelude.GT -> compat n0 (max0 n0 m) __ (hl __);
   _ -> compat m (max0 n0 m) __ (hr __)}

max_case1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> a1 -> a1 -> a1
max_case1 n0 m x x0 x1 =
  max_case_strong1 n0 m x (\_ -> x0) (\_ -> x1)

max_dec1 :: N -> N -> Prelude.Bool
max_dec1 n0 m =
  max_case1 n0 m (\x y _ h0 -> h0) Prelude.True Prelude.False

min_case_strong1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong1 n0 m compat hl hr =
  let {c = compSpec2Type n0 m (compare0 n0 m)} in
  case c of {
   Prelude.GT -> compat m (min0 n0 m) __ (hr __);
   _ -> compat n0 (min0 n0 m) __ (hl __)}

min_case1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> a1 -> a1 -> a1
min_case1 n0 m x x0 x1 =
  min_case_strong1 n0 m x (\_ -> x0) (\_ -> x1)

min_dec1 :: N -> N -> Prelude.Bool
min_dec1 n0 m =
  min_case1 n0 m (\x y _ h0 -> h0) Prelude.True Prelude.False

max_case_strong2 :: N -> N -> (() -> a1) -> (() -> a1) -> a1
max_case_strong2 n0 m x x0 =
  max_case_strong1 n0 m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

max_case2 :: N -> N -> a1 -> a1 -> a1
max_case2 n0 m x x0 =
  max_case_strong2 n0 m (\_ -> x) (\_ -> x0)

max_dec2 :: N -> N -> Prelude.Bool
max_dec2 =
  max_dec1

min_case_strong2 :: N -> N -> (() -> a1) -> (() -> a1) -> a1
min_case_strong2 n0 m x x0 =
  min_case_strong1 n0 m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

min_case2 :: N -> N -> a1 -> a1 -> a1
min_case2 n0 m x x0 =
  min_case_strong2 n0 m (\_ -> x) (\_ -> x0)

min_dec2 :: N -> N -> Prelude.Bool
min_dec2 =
  min_dec1

type T1 = Prelude.Int

zero0 :: Prelude.Int
zero0 =
  0

one0 :: Prelude.Int
one0 =
  (0 Prelude.+) 1

two0 :: Prelude.Int
two0 =
  (0 Prelude.+) ((Prelude.* 2) 1)

double0 :: Prelude.Int -> Prelude.Int
double0 x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\p -> (0 Prelude.+) ((Prelude.* 2)
    p))
    (\p -> Prelude.negate ((Prelude.* 2)
    p))
    x

succ_double0 :: Prelude.Int -> Prelude.Int
succ_double0 x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> (0 Prelude.+)
    1)
    (\p -> (0 Prelude.+) (((Prelude..) (Prelude.+ 1) (Prelude.* 2))
    p))
    (\p -> Prelude.negate
    (pred_double p))
    x

pred_double0 :: Prelude.Int -> Prelude.Int
pred_double0 x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> Prelude.negate
    1)
    (\p -> (0 Prelude.+)
    (pred_double p))
    (\p -> Prelude.negate (((Prelude..) (Prelude.+ 1) (Prelude.* 2))
    p))
    x

pos_sub :: Prelude.Int -> Prelude.Int -> Prelude.Int
pos_sub x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q ->
      double0 (pos_sub p q))
      (\q ->
      succ_double0 (pos_sub p q))
      (\_ -> (0 Prelude.+) ((Prelude.* 2)
      p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q ->
      pred_double0 (pos_sub p q))
      (\q ->
      double0 (pos_sub p q))
      (\_ -> (0 Prelude.+)
      (pred_double p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q -> Prelude.negate ((Prelude.* 2)
      q))
      (\q -> Prelude.negate
      (pred_double q))
      (\_ ->
      0)
      y)
    x

add1 :: Prelude.Int -> Prelude.Int -> Prelude.Int
add1 = (Prelude.+)

opp :: Prelude.Int -> Prelude.Int
opp x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\x0 -> Prelude.negate
    x0)
    (\x0 -> (0 Prelude.+)
    x0)
    x

succ1 :: Prelude.Int -> Prelude.Int
succ1 x =
  add1 x ((0 Prelude.+) 1)

pred1 :: Prelude.Int -> Prelude.Int
pred1 x =
  add1 x (Prelude.negate 1)

sub1 :: Prelude.Int -> Prelude.Int -> Prelude.Int
sub1 m n0 =
  add1 m (opp n0)

mul1 :: Prelude.Int -> Prelude.Int -> Prelude.Int
mul1 = (Prelude.*)

pow_pos :: Prelude.Int -> Prelude.Int -> Prelude.Int
pow_pos z n0 =
  iter n0 (mul1 z) ((0 Prelude.+) 1)

pow1 :: Prelude.Int -> Prelude.Int -> Prelude.Int
pow1 x y =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> (0 Prelude.+)
    1)
    (\p ->
    pow_pos x p)
    (\p ->
    0)
    y

square1 :: Prelude.Int -> Prelude.Int
square1 x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\p -> (0 Prelude.+)
    (square p))
    (\p -> (0 Prelude.+)
    (square p))
    x

compare1 :: Prelude.Int -> Prelude.Int -> Prelude.Ordering
compare1 x y =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      Prelude.EQ)
      (\y' ->
      Prelude.LT)
      (\y' ->
      Prelude.GT)
      y)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      Prelude.GT)
      (\y' ->
      compare x' y')
      (\y' ->
      Prelude.GT)
      y)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      Prelude.LT)
      (\y' ->
      Prelude.LT)
      (\y' ->
      compOpp (compare x' y'))
      y)
    x

sgn :: Prelude.Int -> Prelude.Int
sgn z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\p -> (0 Prelude.+)
    1)
    (\p -> Prelude.negate
    1)
    z

leb1 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
leb1 x y =
  case compare1 x y of {
   Prelude.GT -> Prelude.False;
   _ -> Prelude.True}

ltb1 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
ltb1 x y =
  case compare1 x y of {
   Prelude.LT -> Prelude.True;
   _ -> Prelude.False}

geb :: Prelude.Int -> Prelude.Int -> Prelude.Bool
geb x y =
  case compare1 x y of {
   Prelude.LT -> Prelude.False;
   _ -> Prelude.True}

gtb :: Prelude.Int -> Prelude.Int -> Prelude.Bool
gtb x y =
  case compare1 x y of {
   Prelude.GT -> Prelude.True;
   _ -> Prelude.False}

eqb1 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
eqb1 x y =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      Prelude.True)
      (\p ->
      Prelude.False)
      (\p ->
      Prelude.False)
      y)
    (\p ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      Prelude.False)
      (\q ->
      eqb p q)
      (\p0 ->
      Prelude.False)
      y)
    (\p ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      Prelude.False)
      (\p0 ->
      Prelude.False)
      (\q ->
      eqb p q)
      y)
    x

max1 :: Prelude.Int -> Prelude.Int -> Prelude.Int
max1 n0 m =
  case compare1 n0 m of {
   Prelude.LT -> m;
   _ -> n0}

min1 :: Prelude.Int -> Prelude.Int -> Prelude.Int
min1 n0 m =
  case compare1 n0 m of {
   Prelude.GT -> m;
   _ -> n0}

abs :: Prelude.Int -> Prelude.Int
abs z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\p -> (0 Prelude.+)
    p)
    (\p -> (0 Prelude.+)
    p)
    z

abs_nat :: Prelude.Int -> Prelude.Int
abs_nat z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\p ->
    to_nat p)
    (\p ->
    to_nat p)
    z

abs_N :: Prelude.Int -> N
abs_N z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    N0)
    (\p -> Npos
    p)
    (\p -> Npos
    p)
    z

to_nat1 :: Prelude.Int -> Prelude.Int
to_nat1 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\p ->
    to_nat p)
    (\p ->
    0)
    z

to_N :: Prelude.Int -> N
to_N z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    N0)
    (\p -> Npos
    p)
    (\p ->
    N0)
    z

of_nat1 :: Prelude.Int -> Prelude.Int
of_nat1 n0 =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    0)
    (\n1 -> (0 Prelude.+)
    (of_succ_nat n1))
    n0

of_N :: N -> Prelude.Int
of_N n0 =
  case n0 of {
   N0 -> 0;
   Npos p -> (0 Prelude.+) p}

to_pos :: Prelude.Int -> Prelude.Int
to_pos z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    1)
    (\p ->
    p)
    (\p ->
    1)
    z

iter1 :: Prelude.Int -> (a1 -> a1) -> a1 -> a1
iter1 n0 f x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    x)
    (\p ->
    iter p f x)
    (\p ->
    x)
    n0

pos_div_eucl0 :: Prelude.Int -> Prelude.Int -> (,) Prelude.Int Prelude.Int
pos_div_eucl0 a b =
  (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\a' ->
    case pos_div_eucl0 a' b of {
     (,) q r ->
      let {
       r' = add1 (mul1 ((0 Prelude.+) ((Prelude.* 2) 1)) r) ((0 Prelude.+) 1)}
      in
      case ltb1 r' b of {
       Prelude.True -> (,) (mul1 ((0 Prelude.+) ((Prelude.* 2) 1)) q) r';
       Prelude.False -> (,)
        (add1 (mul1 ((0 Prelude.+) ((Prelude.* 2) 1)) q) ((0 Prelude.+) 1))
        (sub1 r' b)}})
    (\a' ->
    case pos_div_eucl0 a' b of {
     (,) q r ->
      let {r' = mul1 ((0 Prelude.+) ((Prelude.* 2) 1)) r} in
      case ltb1 r' b of {
       Prelude.True -> (,) (mul1 ((0 Prelude.+) ((Prelude.* 2) 1)) q) r';
       Prelude.False -> (,)
        (add1 (mul1 ((0 Prelude.+) ((Prelude.* 2) 1)) q) ((0 Prelude.+) 1))
        (sub1 r' b)}})
    (\_ ->
    case leb1 ((0 Prelude.+) ((Prelude.* 2) 1)) b of {
     Prelude.True -> (,) 0 ((0 Prelude.+) 1);
     Prelude.False -> (,) ((0 Prelude.+) 1) 0})
    a

div_eucl0 :: Prelude.Int -> Prelude.Int -> (,) Prelude.Int Prelude.Int
div_eucl0 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> (,) 0
    0)
    (\a' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> (,) 0
      0)
      (\p ->
      pos_div_eucl0 a' b)
      (\b' ->
      case pos_div_eucl0 a' ((0 Prelude.+) b') of {
       (,) q r ->
        (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
          (\_ -> (,) (opp q)
          0)
          (\p -> (,) (opp (add1 q ((0 Prelude.+) 1)))
          (add1 b r))
          (\p -> (,) (opp (add1 q ((0 Prelude.+) 1)))
          (add1 b r))
          r})
      b)
    (\a' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> (,) 0
      0)
      (\p ->
      case pos_div_eucl0 a' b of {
       (,) q r ->
        (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
          (\_ -> (,) (opp q)
          0)
          (\p0 -> (,) (opp (add1 q ((0 Prelude.+) 1)))
          (sub1 b r))
          (\p0 -> (,) (opp (add1 q ((0 Prelude.+) 1)))
          (sub1 b r))
          r})
      (\b' ->
      case pos_div_eucl0 a' ((0 Prelude.+) b') of {
       (,) q r -> (,) q (opp r)})
      b)
    a

div1 :: Prelude.Int -> Prelude.Int -> Prelude.Int
div1 = Prelude.div

modulo0 :: Prelude.Int -> Prelude.Int -> Prelude.Int
modulo0 a b =
  case div_eucl0 a b of {
   (,) x r -> r}

quotrem :: Prelude.Int -> Prelude.Int -> (,) Prelude.Int Prelude.Int
quotrem a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> (,) 0
    0)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> (,) 0
      a)
      (\b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       (,) q r -> (,) (of_N q) (of_N r)})
      (\b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       (,) q r -> (,) (opp (of_N q)) (of_N r)})
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> (,) 0
      a)
      (\b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       (,) q r -> (,) (opp (of_N q)) (opp (of_N r))})
      (\b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       (,) q r -> (,) (of_N q) (opp (of_N r))})
      b)
    a

quot :: Prelude.Int -> Prelude.Int -> Prelude.Int
quot a b =
  fst (quotrem a b)

rem :: Prelude.Int -> Prelude.Int -> Prelude.Int
rem a b =
  snd (quotrem a b)

even0 :: Prelude.Int -> Prelude.Bool
even0 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    Prelude.True)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 ->
      Prelude.False)
      (\p0 ->
      Prelude.True)
      (\_ ->
      Prelude.False)
      p)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 ->
      Prelude.False)
      (\p0 ->
      Prelude.True)
      (\_ ->
      Prelude.False)
      p)
    z

odd0 :: Prelude.Int -> Prelude.Bool
odd0 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    Prelude.False)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 ->
      Prelude.True)
      (\p0 ->
      Prelude.False)
      (\_ ->
      Prelude.True)
      p)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 ->
      Prelude.True)
      (\p0 ->
      Prelude.False)
      (\_ ->
      Prelude.True)
      p)
    z

div3 :: Prelude.Int -> Prelude.Int
div3 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 -> (0 Prelude.+)
      (div2 p))
      (\p0 -> (0 Prelude.+)
      (div2 p))
      (\_ ->
      0)
      p)
    (\p -> Prelude.negate
    (div2_up p))
    z

quot2 :: Prelude.Int -> Prelude.Int
quot2 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 -> (0 Prelude.+)
      (div2 p))
      (\p0 -> (0 Prelude.+)
      (div2 p))
      (\_ ->
      0)
      p)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 -> Prelude.negate
      (div2 p))
      (\p0 -> Prelude.negate
      (div2 p))
      (\_ ->
      0)
      p)
    z

log0 :: Prelude.Int -> Prelude.Int
log0 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p -> (0 Prelude.+)
      (size p))
      (\p -> (0 Prelude.+)
      (size p))
      (\_ ->
      0)
      p0)
    (\p ->
    0)
    z

sqrtrem1 :: Prelude.Int -> (,) Prelude.Int Prelude.Int
sqrtrem1 n0 =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> (,) 0
    0)
    (\p ->
    case sqrtrem p of {
     (,) s m ->
      case m of {
       IsPos r -> (,) ((0 Prelude.+) s) ((0 Prelude.+) r);
       _ -> (,) ((0 Prelude.+) s) 0}})
    (\p -> (,) 0
    0)
    n0

sqrt1 :: Prelude.Int -> Prelude.Int
sqrt1 n0 =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\p -> (0 Prelude.+)
    (sqrt p))
    (\p ->
    0)
    n0

gcd1 :: Prelude.Int -> Prelude.Int -> Prelude.Int
gcd1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    abs b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      abs a)
      (\b0 -> (0 Prelude.+)
      (gcd a0 b0))
      (\b0 -> (0 Prelude.+)
      (gcd a0 b0))
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      abs a)
      (\b0 -> (0 Prelude.+)
      (gcd a0 b0))
      (\b0 -> (0 Prelude.+)
      (gcd a0 b0))
      b)
    a

ggcd1 :: Prelude.Int -> Prelude.Int -> (,) Prelude.Int
         ((,) Prelude.Int Prelude.Int)
ggcd1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> (,) (abs b) ((,) 0
    (sgn b)))
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> (,) (abs a) ((,) (sgn a)
      0))
      (\b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) ((0 Prelude.+) g) ((,) ((0 Prelude.+) aa)
          ((0 Prelude.+) bb))}})
      (\b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) ((0 Prelude.+) g) ((,) ((0 Prelude.+) aa)
          (Prelude.negate bb))}})
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> (,) (abs a) ((,) (sgn a)
      0))
      (\b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) ((0 Prelude.+) g) ((,) (Prelude.negate aa)
          ((0 Prelude.+) bb))}})
      (\b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) ((0 Prelude.+) g) ((,) (Prelude.negate aa)
          (Prelude.negate bb))}})
      b)
    a

testbit1 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
testbit1 a n0 =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    odd0 a)
    (\p ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      Prelude.False)
      (\a0 ->
      testbit a0 (Npos p))
      (\a0 ->
      negb (testbit0 (pred_N a0) (Npos p)))
      a)
    (\p ->
    Prelude.False)
    n0

shiftl1 :: Prelude.Int -> Prelude.Int -> Prelude.Int
shiftl1 a n0 =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    a)
    (\p ->
    iter p (mul1 ((0 Prelude.+) ((Prelude.* 2) 1))) a)
    (\p ->
    iter p div3 a)
    n0

shiftr1 :: Prelude.Int -> Prelude.Int -> Prelude.Int
shiftr1 a n0 =
  shiftl1 a (opp n0)

lor1 :: Prelude.Int -> Prelude.Int -> Prelude.Int
lor1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      a)
      (\b0 -> (0 Prelude.+)
      (lor a0 b0))
      (\b0 -> Prelude.negate
      (succ_pos (ldiff0 (pred_N b0) (Npos a0))))
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      a)
      (\b0 -> Prelude.negate
      (succ_pos (ldiff0 (pred_N a0) (Npos b0))))
      (\b0 -> Prelude.negate
      (succ_pos (land0 (pred_N a0) (pred_N b0))))
      b)
    a

land1 :: Prelude.Int -> Prelude.Int -> Prelude.Int
land1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      0)
      (\b0 ->
      of_N (land a0 b0))
      (\b0 ->
      of_N (ldiff0 (Npos a0) (pred_N b0)))
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      0)
      (\b0 ->
      of_N (ldiff0 (Npos b0) (pred_N a0)))
      (\b0 -> Prelude.negate
      (succ_pos (lor0 (pred_N a0) (pred_N b0))))
      b)
    a

ldiff1 :: Prelude.Int -> Prelude.Int -> Prelude.Int
ldiff1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      a)
      (\b0 ->
      of_N (ldiff a0 b0))
      (\b0 ->
      of_N (land0 (Npos a0) (pred_N b0)))
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      a)
      (\b0 -> Prelude.negate
      (succ_pos (lor0 (pred_N a0) (Npos b0))))
      (\b0 ->
      of_N (ldiff0 (pred_N b0) (pred_N a0)))
      b)
    a

lxor1 :: Prelude.Int -> Prelude.Int -> Prelude.Int
lxor1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      a)
      (\b0 ->
      of_N (lxor a0 b0))
      (\b0 -> Prelude.negate
      (succ_pos (lxor0 (Npos a0) (pred_N b0))))
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      a)
      (\b0 -> Prelude.negate
      (succ_pos (lxor0 (pred_N a0) (Npos b0))))
      (\b0 ->
      of_N (lxor0 (pred_N a0) (pred_N b0)))
      b)
    a

eq_dec1 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
eq_dec1 x y =
  z_rec (\y0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      Prelude.True)
      (\p ->
      Prelude.False)
      (\p ->
      Prelude.False)
      y0) (\p y0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      Prelude.False)
      (\p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Prelude.True p) (\_ -> Prelude.False)
        (eq_dec p p0))
      (\p0 ->
      Prelude.False)
      y0) (\p y0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      Prelude.False)
      (\p0 ->
      Prelude.False)
      (\p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Prelude.True p) (\_ -> Prelude.False)
        (eq_dec p p0))
      y0) x y

leb_spec2 :: Prelude.Int -> Prelude.Int -> Reflect
leb_spec2 x y =
  iff_reflect (leb1 x y)

ltb_spec2 :: Prelude.Int -> Prelude.Int -> Reflect
ltb_spec2 x y =
  iff_reflect (ltb1 x y)

sqrt_up0 :: Prelude.Int -> Prelude.Int
sqrt_up0 a =
  case compare1 0 a of {
   Prelude.LT -> succ1 (sqrt1 (pred1 a));
   _ -> 0}

log2_up0 :: Prelude.Int -> Prelude.Int
log2_up0 a =
  case compare1 ((0 Prelude.+) 1) a of {
   Prelude.LT -> succ1 (log0 (pred1 a));
   _ -> 0}

div4 :: Prelude.Int -> Prelude.Int -> Prelude.Int
div4 =
  quot

modulo1 :: Prelude.Int -> Prelude.Int -> Prelude.Int
modulo1 =
  rem

lcm0 :: Prelude.Int -> Prelude.Int -> Prelude.Int
lcm0 a b =
  abs (mul1 a (div1 b (gcd1 a b)))

eqb_spec1 :: Prelude.Int -> Prelude.Int -> Reflect
eqb_spec1 x y =
  iff_reflect (eqb1 x y)

b2z :: Prelude.Bool -> Prelude.Int
b2z b =
  case b of {
   Prelude.True -> (0 Prelude.+) 1;
   Prelude.False -> 0}

setbit0 :: Prelude.Int -> Prelude.Int -> Prelude.Int
setbit0 a n0 =
  lor1 a (shiftl1 ((0 Prelude.+) 1) n0)

clearbit0 :: Prelude.Int -> Prelude.Int -> Prelude.Int
clearbit0 a n0 =
  ldiff1 a (shiftl1 ((0 Prelude.+) 1) n0)

lnot0 :: Prelude.Int -> Prelude.Int
lnot0 a =
  pred1 (opp a)

ones0 :: Prelude.Int -> Prelude.Int
ones0 n0 =
  pred1 (shiftl1 ((0 Prelude.+) 1) n0)

max_case_strong3 :: Prelude.Int -> Prelude.Int -> (Prelude.Int -> Prelude.Int
                    -> () -> a1 -> a1) -> (() -> a1) -> (() -> a1) -> a1
max_case_strong3 n0 m compat hl hr =
  let {c = compSpec2Type n0 m (compare1 n0 m)} in
  case c of {
   Prelude.GT -> compat n0 (max1 n0 m) __ (hl __);
   _ -> compat m (max1 n0 m) __ (hr __)}

max_case3 :: Prelude.Int -> Prelude.Int -> (Prelude.Int -> Prelude.Int -> ()
             -> a1 -> a1) -> a1 -> a1 -> a1
max_case3 n0 m x x0 x1 =
  max_case_strong3 n0 m x (\_ -> x0) (\_ -> x1)

max_dec3 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
max_dec3 n0 m =
  max_case3 n0 m (\x y _ h0 -> h0) Prelude.True Prelude.False

min_case_strong3 :: Prelude.Int -> Prelude.Int -> (Prelude.Int -> Prelude.Int
                    -> () -> a1 -> a1) -> (() -> a1) -> (() -> a1) -> a1
min_case_strong3 n0 m compat hl hr =
  let {c = compSpec2Type n0 m (compare1 n0 m)} in
  case c of {
   Prelude.GT -> compat m (min1 n0 m) __ (hr __);
   _ -> compat n0 (min1 n0 m) __ (hl __)}

min_case3 :: Prelude.Int -> Prelude.Int -> (Prelude.Int -> Prelude.Int -> ()
             -> a1 -> a1) -> a1 -> a1 -> a1
min_case3 n0 m x x0 x1 =
  min_case_strong3 n0 m x (\_ -> x0) (\_ -> x1)

min_dec3 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
min_dec3 n0 m =
  min_case3 n0 m (\x y _ h0 -> h0) Prelude.True Prelude.False

max_case_strong4 :: Prelude.Int -> Prelude.Int -> (() -> a1) -> (() -> a1) ->
                    a1
max_case_strong4 n0 m x x0 =
  max_case_strong3 n0 m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

max_case4 :: Prelude.Int -> Prelude.Int -> a1 -> a1 -> a1
max_case4 n0 m x x0 =
  max_case_strong4 n0 m (\_ -> x) (\_ -> x0)

max_dec4 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
max_dec4 =
  max_dec3

min_case_strong4 :: Prelude.Int -> Prelude.Int -> (() -> a1) -> (() -> a1) ->
                    a1
min_case_strong4 n0 m x x0 =
  min_case_strong3 n0 m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

min_case4 :: Prelude.Int -> Prelude.Int -> a1 -> a1 -> a1
min_case4 n0 m x x0 =
  min_case_strong4 n0 m (\_ -> x) (\_ -> x0)

min_dec4 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
min_dec4 =
  min_dec3

map :: (a1 -> a2) -> ([] a1) -> [] a2
map f l =
  case l of {
   [] -> [];
   (:) a t -> (:) (f a) (map f t)}

fold_right :: (a2 -> a1 -> a1) -> a1 -> ([] a2) -> a1
fold_right f a0 l =
  case l of {
   [] -> a0;
   (:) b t -> f b (fold_right f a0 t)}

type VC v = (,) Prelude.Int v

type Linear v = (,) ([] (VC v)) Prelude.Int

data C v =
   Le (Linear v) (Linear v)

const :: Prelude.Int -> Linear a1
const n0 =
  (,) [] n0

var :: Prelude.Int -> a1 -> Linear a1
var n0 v =
  (,) ((:) ((,) n0 v) []) 0

var1 :: a1 -> Linear a1
var1 =
  var ((0 Prelude.+) 1)

plus0 :: (Linear a1) -> (Linear a1) -> (,) ([] (VC a1)) Prelude.Int
plus0 a b =
  case a of {
   (,) vs1 n1 ->
    case b of {
     (,) vs2 n2 -> (,) (app vs1 vs2) (add1 n1 n2)}}

negate :: (Linear a1) -> (,) ([] ((,) Prelude.Int a1)) Prelude.Int
negate a =
  case a of {
   (,) vs1 n1 -> (,)
    (map (\x ->
      case x of {
       (,) n0 v -> (,) (opp n0) v}) vs1) (opp n1)}

constrs :: ([] ([] (C a1))) -> [] (C a1)
constrs a =
  fold_right (\x y -> app x y) [] a

selfcross_go :: a1 -> ([] a1) -> [] ((,) a1 a1)
selfcross_go x ys =
  case ys of {
   [] -> [];
   (:) y ys' -> (:) ((,) x y) (selfcross_go x ys')}

selfcross :: ([] a1) -> [] ((,) a1 a1)
selfcross xs =
  case xs of {
   [] -> [];
   (:) x xs' -> app (selfcross_go x xs') (selfcross xs')}

data EdgeType =
   Fusible
 | Nonfusible

data Var v =
   SameCluster ((,) v v)
 | Pi v

pairs :: ([] a1) -> [] ((,) a1 a1)
pairs vs =
  selfcross vs

n :: ([] a1) -> Prelude.Int
n vs =
  of_nat1 (length vs)

objectives :: ([] ((,) a1 a1)) -> Linear (Var a1)
objectives ps =
  let {clusters = map (\p -> var1 (SameCluster p)) ps} in
  fold_right (\x y -> plus0 x y) (const 0) clusters

objective :: ([] a1) -> Linear (Var a1)
objective vs =
  objectives (pairs vs)

constraintOfPair :: (((,) a1 a1) -> Prelude.Maybe EdgeType) -> ([] a1) ->
                    ((,) a1 a1) -> [] (C (Var a1))
constraintOfPair e vs vv =
  let {sc = SameCluster vv} in
  let {
   scR = case vv of {
          (,) i j -> SameCluster ((,) j i)}}
  in
  let {
   scReq = (:) (Le (var1 sc) (var1 scR)) ((:) (Le (var1 scR) (var1 sc)) [])}
  in
  let {
   bounds = app ((:) (Le (const 0) (var1 sc)) []) ((:) (Le (var1 sc)
              (const ((0 Prelude.+) 1))) [])}
  in
  let {
   selfs = case vv of {
            (,) i j ->
             constrs ((:) ((:) (Le (var1 (SameCluster ((,) i i))) (const 0))
               ((:) (Le (const 0) (var1 (SameCluster ((,) i i)))) [])) ((:)
               ((:) (Le (var1 (SameCluster ((,) j j))) (const 0)) ((:) (Le
               (const 0) (var1 (SameCluster ((,) j j)))) [])) []))}}
  in
  let {o = e vv} in
  case vv of {
   (,) i j ->
    case o of {
     Prelude.Just e0 ->
      case e0 of {
       Fusible ->
        constrs ((:)
          (app ((:) (Le (var1 sc)
            (plus0 (var1 (Pi j)) (negate (var1 (Pi i))))) []) ((:) (Le
            (plus0 (var1 (Pi j)) (negate (var1 (Pi i)))) (var (n vs) sc))
            [])) ((:) bounds ((:) scReq ((:) selfs []))));
       Nonfusible ->
        constrs ((:) ((:) (Le (var1 (Pi i))
          (plus0 (var1 (Pi j)) (const (Prelude.negate 1)))) []) ((:) ((:) (Le
          (var1 sc) (const ((0 Prelude.+) 1))) ((:) (Le
          (const ((0 Prelude.+) 1)) (var1 sc)) [])) ((:) scReq ((:) selfs
          []))))};
     Prelude.Nothing ->
      constrs ((:)
        (app ((:) (Le (var (opp (n vs)) sc)
          (plus0 (var1 (Pi j)) (negate (var1 (Pi i))))) []) ((:) (Le
          (plus0 (var1 (Pi j)) (negate (var1 (Pi i)))) (var (n vs) sc)) []))
        ((:) bounds ((:) scReq ((:) selfs []))))}}

constraints :: (((,) a1 a1) -> Prelude.Maybe EdgeType) -> ([] a1) -> []
               (C (Var a1))
constraints e vs =
  constrs (map (constraintOfPair e vs) (pairs vs))

