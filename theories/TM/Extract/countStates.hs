{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Main where


import Prelude hiding (seq, return, Left, Right, repeat, map, elem, concat, length, const, null, id, lookup)

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

and_rect :: (() -> () -> a1) -> a1
and_rect f =
  f __ __

and_rec :: (() -> () -> a1) -> a1
and_rec =
  and_rect

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

type Empty_set = () -- empty inductive

empty_set_rect :: Empty_set -> a1
empty_set_rect _ =
  Prelude.error "absurd case"

empty_set_rec :: Empty_set -> a1
empty_set_rec =
  empty_set_rect

data Unit =
   Tt

unit_rect :: a1 -> Unit -> a1
unit_rect f _ =
  f

unit_rec :: a1 -> Unit -> a1
unit_rec =
  unit_rect

bool_rect :: a1 -> a1 -> Prelude.Bool -> a1
bool_rect f f0 b =
  case b of {
   Prelude.True -> f;
   Prelude.False -> f0}

bool_rec :: a1 -> a1 -> Prelude.Bool -> a1
bool_rec =
  bool_rect

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

nat_rect :: a1 -> (Prelude.Int -> a1 -> a1) -> Prelude.Int -> a1
nat_rect f f0 n =
  (\fO fS n -> if n==0 then fO () else fS (pred n))
    (\_ -> f)
    (\n0 -> f0 n0 (nat_rect f f0 n0))
    n

option_rect :: (a1 -> a2) -> a2 -> (Prelude.Maybe a1) -> a2
option_rect f f0 o =
  case o of {
   Prelude.Just x -> f x;
   Prelude.Nothing -> f0}

data Sum a b =
   Inl a
 | Inr b

sum_rect :: (a1 -> a3) -> (a2 -> a3) -> (Sum a1 a2) -> a3
sum_rect f f0 s =
  case s of {
   Inl x -> f x;
   Inr x -> f0 x}

list_rect :: a2 -> (a1 -> (([]) a1) -> a2 -> a2) -> (([]) a1) -> a2
list_rect f f0 l =
  case l of {
   [] -> f;
   (:) y l0 -> f0 y l0 (list_rect f f0 l0)}

list_rec :: a2 -> (a1 -> (([]) a1) -> a2 -> a2) -> (([]) a1) -> a2
list_rec =
  list_rect

length :: (([]) a1) -> Prelude.Int
length l =
  case l of {
   [] -> 0;
   (:) _ l' -> Prelude.succ (length l')}

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   [] -> m;
   (:) a l1 -> (:) a (app l1 m)}

id :: a1 -> a1
id x =
  x

data SigT a p =
   ExistT a p

projT1 :: (SigT a1 a2) -> a1
projT1 x =
  case x of {
   ExistT a _ -> a}

projT2 :: (SigT a1 a2) -> a2
projT2 x =
  case x of {
   ExistT _ h -> h}

data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

in_dec :: (a1 -> a1 -> Sumbool) -> a1 -> (([]) a1) -> Sumbool
in_dec h a l =
  list_rec Right (\a0 _ iHl -> let {s = h a0 a} in case s of {
                                                    Left -> Left;
                                                    Right -> iHl}) l

rev :: (([]) a1) -> ([]) a1
rev l =
  case l of {
   [] -> [];
   (:) x l' -> app (rev l') ((:) x [])}

concat :: (([]) (([]) a1)) -> ([]) a1
concat l =
  case l of {
   [] -> [];
   (:) x l0 -> app x (concat l0)}

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map f l =
  case l of {
   [] -> [];
   (:) a t -> (:) (f a) (map f t)}

repeat :: a1 -> Prelude.Int -> ([]) a1
repeat x n =
  (\fO fS n -> if n==0 then fO () else fS (pred n))
    (\_ -> [])
    (\k -> (:) x (repeat x k))
    n

type Dec = Sumbool

dec :: Dec -> Dec
dec d =
  d

dec_transfer :: Dec -> Dec
dec_transfer h0 =
  and_rec (\_ _ -> sumbool_rec (\_ -> Left) (\_ -> Right) h0)

type EqType = Any -> Any -> Dec
  -- singleton inductive, whose constructor was EqType
  
type EqType_X = Any

eqType_dec :: EqType -> EqType_X -> EqType_X -> Dec
eqType_dec e =
  e

eqType_CS :: (a1 -> a1 -> Dec) -> EqType
eqType_CS a =
  unsafeCoerce a

unit_eq_dec :: Unit -> Unit -> Dec
unit_eq_dec x y =
  unit_rec (\_ -> Left) x y

bool_eq_dec :: Prelude.Bool -> Prelude.Bool -> Dec
bool_eq_dec x y =
  bool_rec (\x0 -> case x0 of {
                    Prelude.True -> Left;
                    Prelude.False -> Right}) (\x0 -> case x0 of {
                                                      Prelude.True -> Right;
                                                      Prelude.False -> Left}) x y

sum_eq_dec :: (a1 -> a1 -> Dec) -> (a2 -> a2 -> Dec) -> (Sum a1 a2) -> (Sum a1 a2) -> Dec
sum_eq_dec x0 x1 x y =
  sum_rect (\a x2 -> case x2 of {
                      Inl x3 -> sumbool_rec (\_ -> Left) (\_ -> Right) (x0 a x3);
                      Inr _ -> Right}) (\b x2 -> case x2 of {
                                                  Inl _ -> Right;
                                                  Inr y0 -> sumbool_rec (\_ -> Left) (\_ -> Right) (x1 b y0)}) x y

option_eq_dec :: (a1 -> a1 -> Dec) -> (Prelude.Maybe a1) -> (Prelude.Maybe a1) -> Dec
option_eq_dec x0 x y =
  option_rect (\a x1 -> case x1 of {
                         Prelude.Just x2 -> sumbool_rec (\_ -> Left) (\_ -> Right) (x0 a x2);
                         Prelude.Nothing -> Right}) (\x1 -> case x1 of {
                                                             Prelude.Just _ -> Right;
                                                             Prelude.Nothing -> Left}) x y

empty_set_eq_dec :: Empty_set -> Empty_set -> Dec
empty_set_eq_dec =
  empty_set_rec

list_in_dec :: a1 -> (([]) a1) -> (a1 -> a1 -> Dec) -> Dec
list_in_dec x a d =
  in_dec d x a

undup :: EqType -> (([]) EqType_X) -> ([]) EqType_X
undup x a =
  case a of {
   [] -> [];
   (:) x0 a' -> case dec (list_in_dec x0 a' (eqType_dec x)) of {
                 Left -> undup x a';
                 Right -> (:) x0 (undup x a')}}

toOptionList :: (([]) a1) -> ([]) (Prelude.Maybe a1)
toOptionList a =
  (:) Prelude.Nothing (map (\x -> Prelude.Just x) a)

toSumList1 :: (([]) a1) -> ([]) (Sum a1 a2)
toSumList1 a =
  map (\x -> Inl x) a

toSumList2 :: (([]) a1) -> ([]) (Sum a2 a1)
toSumList2 a =
  map (\x -> Inr x) a

type FinTypeC = ([]) EqType_X
  -- singleton inductive, whose constructor was FinTypeC
  
enum :: EqType -> FinTypeC -> ([]) EqType_X
enum _ finTypeC =
  finTypeC

data FinType0 =
   FinType EqType FinTypeC

type0 :: FinType0 -> EqType
type0 f =
  case f of {
   FinType type1 _ -> type1}

class0 :: FinType0 -> FinTypeC
class0 f =
  case f of {
   FinType _ class1 -> class1}

finType_CS :: (a1 -> a1 -> Dec) -> FinTypeC -> FinType0
finType_CS p class1 =
  FinType (unsafeCoerce p) class1

elem :: FinType0 -> ([]) EqType_X
elem f =
  enum (type0 f) (class0 f)

finTypeC_Empty_set :: FinTypeC
finTypeC_Empty_set =
  []

finTypeC_bool :: FinTypeC
finTypeC_bool =
  (:) (unsafeCoerce Prelude.True) ((:) (unsafeCoerce Prelude.False) [])

finTypeC_unit :: FinTypeC
finTypeC_unit =
  (:) (unsafeCoerce Tt) []

finTypeC_Option :: FinType0 -> FinTypeC
finTypeC_Option f =
  unsafeCoerce toOptionList (elem f)

finTypeC_sum :: FinType0 -> FinType0 -> FinTypeC
finTypeC_sum x y =
  app (unsafeCoerce toSumList1 (elem x)) (unsafeCoerce toSumList2 (elem y))

data T =
   F1 Prelude.Int
 | FS Prelude.Int T

data T0 a =
   Nil
 | Cons a Prelude.Int (T0 a)

caseS :: (a1 -> Prelude.Int -> (T0 a1) -> a2) -> Prelude.Int -> (T0 a1) -> a2
caseS h _ v =
  case v of {
   Nil -> __;
   Cons h0 n t -> h h0 n t}

caseS' :: Prelude.Int -> (T0 a1) -> (a1 -> (T0 a1) -> a2) -> a2
caseS' _ v h =
  case v of {
   Nil -> __;
   Cons h0 _ t -> h h0 t}

hd :: Prelude.Int -> (T0 a1) -> a1
hd =
  caseS (\h _ _ -> h)

const :: a1 -> Prelude.Int -> T0 a1
const a =
  nat_rect Nil (\n x -> Cons a n x)

nth :: Prelude.Int -> (T0 a1) -> T -> a1
nth _ v' p =
  case p of {
   F1 n -> caseS (\h _ _ -> h) n v';
   FS n p' -> caseS (\_ -> nth) n v' p'}

replace :: Prelude.Int -> (T0 a1) -> T -> a1 -> T0 a1
replace _ v p a =
  case p of {
   F1 k -> caseS' k v (\_ t -> Cons a k t);
   FS k p' -> caseS' k v (\h t -> Cons h k (replace k t p' a))}

tl :: Prelude.Int -> (T0 a1) -> T0 a1
tl =
  caseS (\_ _ t -> t)

map0 :: (a1 -> a2) -> Prelude.Int -> (T0 a1) -> T0 a2
map0 f _ v =
  case v of {
   Nil -> Nil;
   Cons a n v' -> Cons (f a) n (map0 f n v')}

data Retract x y =
   Build_Retract (x -> y) (y -> Prelude.Maybe x)

retr_f :: (Retract a1 a2) -> a1 -> a2
retr_f retract =
  case retract of {
   Build_Retract retr_f0 _ -> retr_f0}

retr_g :: (Retract a1 a2) -> a2 -> Prelude.Maybe a1
retr_g retract =
  case retract of {
   Build_Retract _ retr_g0 -> retr_g0}

retr_comp_f :: (a2 -> a3) -> (a1 -> a2) -> a1 -> a3
retr_comp_f f1 f2 a =
  f1 (f2 a)

retr_comp_g :: (a3 -> Prelude.Maybe a2) -> (a2 -> Prelude.Maybe a1) -> a3 -> Prelude.Maybe a1
retr_comp_g g1 g2 c =
  case g1 c of {
   Prelude.Just b -> g2 b;
   Prelude.Nothing -> Prelude.Nothing}

composeRetract :: (Retract a2 a3) -> (Retract a1 a2) -> Retract a1 a3
composeRetract retr1 retr2 =
  Build_Retract (retr_comp_f (retr_f retr1) (retr_f retr2)) (retr_comp_g (retr_g retr1) (retr_g retr2))

retract_id :: Retract a1 a1
retract_id =
  Build_Retract (\a -> a) (\b -> Prelude.Just b)

retract_inl_f :: (a1 -> a2) -> a1 -> Sum a2 a3
retract_inl_f f a =
  Inl (f a)

retract_inl_g :: (a2 -> Prelude.Maybe a1) -> (Sum a2 a3) -> Prelude.Maybe a1
retract_inl_g g x =
  case x of {
   Inl b -> g b;
   Inr _ -> Prelude.Nothing}

retract_inl :: (Retract a1 a2) -> Retract a1 (Sum a2 a3)
retract_inl retrAB =
  Build_Retract (retract_inl_f (retr_f retrAB)) (retract_inl_g (retr_g retrAB))

retract_inr_f :: (a1 -> a2) -> a1 -> Sum a3 a2
retract_inr_f f a =
  Inr (f a)

retract_inr_g :: (a2 -> Prelude.Maybe a1) -> (Sum a3 a2) -> Prelude.Maybe a1
retract_inr_g g x =
  case x of {
   Inl _ -> Prelude.Nothing;
   Inr b -> g b}

retract_inr :: (Retract a1 a2) -> Retract a1 (Sum a3 a2)
retract_inr retrAB =
  Build_Retract (retract_inr_f (retr_f retrAB)) (retract_inr_g (retr_g retrAB))

retract_sum_f :: (a1 -> a3) -> (a2 -> a4) -> (Sum a1 a2) -> Sum a3 a4
retract_sum_f f1 f2 x =
  case x of {
   Inl a -> Inl (f1 a);
   Inr b -> Inr (f2 b)}

retract_sum_g :: (a3 -> Prelude.Maybe a1) -> (a4 -> Prelude.Maybe a2) -> (Sum a3 a4) -> Prelude.Maybe (Sum a1 a2)
retract_sum_g g1 g2 y =
  case y of {
   Inl c -> case g1 c of {
             Prelude.Just a -> Prelude.Just (Inl a);
             Prelude.Nothing -> Prelude.Nothing};
   Inr d -> case g2 d of {
             Prelude.Just b -> Prelude.Just (Inr b);
             Prelude.Nothing -> Prelude.Nothing}}

retract_sum :: (Retract a1 a3) -> (Retract a2 a4) -> Retract (Sum a1 a2) (Sum a3 a4)
retract_sum retr1 retr2 =
  Build_Retract (retract_sum_f (retr_f retr1) (retr_f retr2)) (retract_sum_g (retr_g retr1) (retr_g retr2))

type InhabitedC x = x
  -- singleton inductive, whose constructor was Build_inhabitedC
  
default0 :: (InhabitedC a1) -> a1
default0 inhabitedC =
  inhabitedC

inhabited_unit :: InhabitedC Unit
inhabited_unit =
  Tt

inhabited_bool :: InhabitedC Prelude.Bool
inhabited_bool =
  Prelude.True

map_opt :: (a1 -> a2) -> (Prelude.Maybe a1) -> Prelude.Maybe a2
map_opt f a =
  case a of {
   Prelude.Just x -> Prelude.Just (f x);
   Prelude.Nothing -> Prelude.Nothing}

map_fst :: (a1 -> a3) -> ((,) a1 a2) -> (,) a3 a2
map_fst f pat =
  case pat of {
   (,) x y -> (,) (f x) y}

map_snd :: (a2 -> a3) -> ((,) a1 a2) -> (,) a1 a3
map_snd f pat =
  case pat of {
   (,) x y -> (,) x (f y)}

eqType_depPair :: EqType -> (EqType_X -> EqType) -> (SigT EqType_X EqType_X) -> (SigT EqType_X EqType_X) -> Dec
eqType_depPair f a x0 y0 =
  case x0 of {
   ExistT x fx ->
    case y0 of {
     ExistT y fy ->
      dec_transfer
        (let {d = dec (eqType_dec f x y)} in
         case d of {
          Left -> eq_rect x (\fy0 -> let {d0 = dec (eqType_dec (a x) fx fy0)} in case d0 of {
                                                                                  Left -> eq_rect fx Left fy0;
                                                                                  Right -> Right}) y fy;
          Right -> Right})}}

finType_depPair :: FinType0 -> (EqType_X -> FinType0) -> FinTypeC
finType_depPair f a =
  undup (eqType_CS (eqType_depPair (type0 f) (\f0 -> type0 (a f0)))) (concat (map (\f0 -> map (\x -> unsafeCoerce (ExistT f0 x)) (elem (a f0))) (elem f)))

data Move =
   L
 | R
 | N

nop_action :: Prelude.Int -> FinType0 -> T0 ((,) (Prelude.Maybe EqType_X) Move)
nop_action n _ =
  const ((,) Prelude.Nothing N) n

mirror_move :: Move -> Move
mirror_move d =
  case d of {
   L -> R;
   R -> L;
   N -> N}

data MTM =
   Build_mTM FinType0 (((,) EqType_X (T0 (Prelude.Maybe EqType_X))) -> (,) EqType_X (T0 ((,) (Prelude.Maybe EqType_X) Move))) EqType_X (EqType_X -> Prelude.Bool)

states :: FinType0 -> Prelude.Int -> MTM -> FinType0
states _ _ m =
  case m of {
   Build_mTM states0 _ _ _ -> states0}

trans :: FinType0 -> Prelude.Int -> MTM -> ((,) EqType_X (T0 (Prelude.Maybe EqType_X))) -> (,) EqType_X (T0 ((,) (Prelude.Maybe EqType_X) Move))
trans _ _ m =
  case m of {
   Build_mTM _ trans0 _ _ -> trans0}

start :: FinType0 -> Prelude.Int -> MTM -> EqType_X
start _ _ m =
  case m of {
   Build_mTM _ _ start0 _ -> start0}

halt :: FinType0 -> Prelude.Int -> MTM -> EqType_X -> Prelude.Bool
halt _ _ m =
  case m of {
   Build_mTM _ _ _ halt0 -> halt0}

type PTM f = SigT MTM (EqType_X -> f)

type Codable sig x = x -> ([]) sig
  -- singleton inductive, whose constructor was Build_codable
  
encode :: (Codable a1 a2) -> a2 -> ([]) a1
encode codable =
  codable

encode_Finite :: FinType0 -> Codable EqType_X EqType_X
encode_Finite _ x =
  (:) x []

encode_map :: (Codable a2 a1) -> (Retract a2 a3) -> Codable a3 a1
encode_map cX inj x =
  map (retr_f inj) (encode cX x)

data SigSum sigX sigY =
   SigSum_X sigX
 | SigSum_Y sigY
 | SigSum_inl
 | SigSum_inr

sigSum_rect :: (a1 -> a3) -> (a2 -> a3) -> a3 -> a3 -> (SigSum a1 a2) -> a3
sigSum_rect f f0 f1 f2 s =
  case s of {
   SigSum_X x -> f x;
   SigSum_Y x -> f0 x;
   SigSum_inl -> f1;
   SigSum_inr -> f2}

retract_sigSum_X :: (Retract a1 a3) -> Retract a1 (SigSum a3 a2)
retract_sigSum_X f =
  Build_Retract (\x -> SigSum_X (retr_f f x)) (\x0 -> case x0 of {
                                                       SigSum_X s -> retr_g f s;
                                                       _ -> Prelude.Nothing})

retract_sigSum_Y :: (Retract a2 a3) -> Retract a2 (SigSum a1 a3)
retract_sigSum_Y f =
  Build_Retract (\x -> SigSum_Y (retr_f f x)) (\x0 -> case x0 of {
                                                       SigSum_Y s -> retr_g f s;
                                                       _ -> Prelude.Nothing})

sigSum_dec :: (a1 -> a1 -> Dec) -> (a2 -> a2 -> Dec) -> (SigSum a1 a2) -> (SigSum a1 a2) -> Dec
sigSum_dec decX decY x y =
  sigSum_rect (\s x0 -> case x0 of {
                         SigSum_X s0 -> sumbool_rec (\_ -> Left) (\_ -> Right) (dec (decX s s0));
                         _ -> Right}) (\s x0 -> case x0 of {
                                                 SigSum_Y s0 -> sumbool_rec (\_ -> Left) (\_ -> Right) (dec (decY s s0));
                                                 _ -> Right}) (\x0 -> case x0 of {
                                                                       SigSum_inl -> Left;
                                                                       _ -> Right}) (\x0 -> case x0 of {
                                                                                             SigSum_inr -> Left;
                                                                                             _ -> Right}) x y

sigSum_fin :: FinType0 -> FinType0 -> FinTypeC
sigSum_fin sigX sigY =
  (:) (unsafeCoerce SigSum_inl) ((:) (unsafeCoerce SigSum_inr)
    (app (map (unsafeCoerce (\x -> SigSum_X x)) (enum (type0 sigX) (class0 sigX))) (map (unsafeCoerce (\x -> SigSum_Y x)) (enum (type0 sigY) (class0 sigY)))))

encode_sum :: (Codable a3 a1) -> (Codable a4 a2) -> Codable (SigSum a3 a4) (Sum a1 a2)
encode_sum cX cY s =
  case s of {
   Inl x -> (:) SigSum_inl (encode (encode_map cX (retract_sigSum_X retract_id)) x);
   Inr y -> (:) SigSum_inr (encode (encode_map cY (retract_sigSum_Y retract_id)) y)}

data SigPair sigX sigY =
   SigPair_X sigX
 | SigPair_Y sigY

sigPair_rect :: (a1 -> a3) -> (a2 -> a3) -> (SigPair a1 a2) -> a3
sigPair_rect f f0 s =
  case s of {
   SigPair_X x -> f x;
   SigPair_Y x -> f0 x}

retract_sigPair_X :: (Retract a1 a3) -> Retract a1 (SigPair a3 a2)
retract_sigPair_X f =
  Build_Retract (\x -> SigPair_X (retr_f f x)) (\x0 -> case x0 of {
                                                        SigPair_X s -> retr_g f s;
                                                        SigPair_Y _ -> Prelude.Nothing})

retract_sigPair_Y :: (Retract a2 a3) -> Retract a2 (SigPair a1 a3)
retract_sigPair_Y f =
  Build_Retract (\x -> SigPair_Y (retr_f f x)) (\x0 -> case x0 of {
                                                        SigPair_X _ -> Prelude.Nothing;
                                                        SigPair_Y s -> retr_g f s})

sigPair_dec :: (a1 -> a1 -> Dec) -> (a2 -> a2 -> Dec) -> (SigPair a1 a2) -> (SigPair a1 a2) -> Dec
sigPair_dec decX decY x y =
  sigPair_rect (\s x0 -> case x0 of {
                          SigPair_X s0 -> sumbool_rec (\_ -> Left) (\_ -> Right) (dec (decX s s0));
                          SigPair_Y _ -> Right}) (\s x0 -> case x0 of {
                                                            SigPair_X _ -> Right;
                                                            SigPair_Y s0 -> sumbool_rec (\_ -> Left) (\_ -> Right) (dec (decY s s0))}) x y

sigPair_fin :: FinType0 -> FinType0 -> FinTypeC
sigPair_fin sigX sigY =
  app (map (unsafeCoerce (\x -> SigPair_X x)) (enum (type0 sigX) (class0 sigX))) (map (unsafeCoerce (\x -> SigPair_Y x)) (enum (type0 sigY) (class0 sigY)))

data SigOption sigX =
   SigOption_X sigX
 | SigOption_None
 | SigOption_Some

sigOption_rect :: (a1 -> a2) -> a2 -> a2 -> (SigOption a1) -> a2
sigOption_rect f f0 f1 s =
  case s of {
   SigOption_X x -> f x;
   SigOption_None -> f0;
   SigOption_Some -> f1}

retract_sigOption_X :: (Retract a1 a2) -> Retract a1 (SigOption a2)
retract_sigOption_X retr =
  Build_Retract (\x -> SigOption_X (retr_f retr x)) (\x0 -> case x0 of {
                                                             SigOption_X s -> retr_g retr s;
                                                             _ -> Prelude.Nothing})

sigOption_dec :: (a1 -> a1 -> Dec) -> (SigOption a1) -> (SigOption a1) -> Dec
sigOption_dec decX x y =
  sigOption_rect (\s x0 -> case x0 of {
                            SigOption_X s0 -> sumbool_rec (\_ -> Left) (\_ -> Right) (dec (decX s s0));
                            _ -> Right}) (\x0 -> case x0 of {
                                                  SigOption_None -> Left;
                                                  _ -> Right}) (\x0 -> case x0 of {
                                                                        SigOption_Some -> Left;
                                                                        _ -> Right}) x y

sigOption_fin :: FinType0 -> FinTypeC
sigOption_fin sigX =
  (:) (unsafeCoerce SigOption_Some) ((:) (unsafeCoerce SigOption_None) (map (unsafeCoerce (\x -> SigOption_X x)) (enum (type0 sigX) (class0 sigX))))

data SigList sigX =
   SigList_X sigX
 | SigList_nil
 | SigList_cons

sigList_rect :: (a1 -> a2) -> a2 -> a2 -> (SigList a1) -> a2
sigList_rect f f0 f1 s =
  case s of {
   SigList_X x -> f x;
   SigList_nil -> f0;
   SigList_cons -> f1}

retract_sigList_X :: (Retract a1 a2) -> Retract a1 (SigList a2)
retract_sigList_X retr =
  Build_Retract (\x -> SigList_X (retr_f retr x)) (\x0 -> case x0 of {
                                                           SigList_X s -> retr_g retr s;
                                                           _ -> Prelude.Nothing})

sigList_dec :: (a1 -> a1 -> Dec) -> (SigList a1) -> (SigList a1) -> Dec
sigList_dec decX x y =
  sigList_rect (\s x0 -> case x0 of {
                          SigList_X s0 -> sumbool_rec (\_ -> Left) (\_ -> Right) (dec (decX s s0));
                          _ -> Right}) (\x0 -> case x0 of {
                                                SigList_nil -> Left;
                                                _ -> Right}) (\x0 -> case x0 of {
                                                                      SigList_cons -> Left;
                                                                      _ -> Right}) x y

sigList_fin :: FinType0 -> FinTypeC
sigList_fin sigX =
  (:) (unsafeCoerce SigList_nil) ((:) (unsafeCoerce SigList_cons) (map (unsafeCoerce (\x -> SigList_X x)) (enum (type0 sigX) (class0 sigX))))

encode_list :: (Codable a1 a2) -> (([]) a2) -> ([]) (SigList a1)
encode_list cX xs =
  case xs of {
   [] -> (:) SigList_nil [];
   (:) x xs' -> (:) SigList_cons (app (encode (encode_map cX (retract_sigList_X retract_id)) x) (encode_list cX xs'))}

encode_list0 :: (Codable a1 a2) -> Codable (SigList a1) (([]) a2)
encode_list0 =
  encode_list

data SigNat =
   SigNat_O
 | SigNat_S

sigNat_rect :: a1 -> a1 -> SigNat -> a1
sigNat_rect f f0 s =
  case s of {
   SigNat_O -> f;
   SigNat_S -> f0}

sigNat_rec :: a1 -> a1 -> SigNat -> a1
sigNat_rec =
  sigNat_rect

sigNat_eq :: SigNat -> SigNat -> Dec
sigNat_eq x y =
  sigNat_rec (\x0 -> case x0 of {
                      SigNat_O -> Left;
                      SigNat_S -> Right}) (\x0 -> case x0 of {
                                                   SigNat_O -> Right;
                                                   SigNat_S -> Left}) x y

sigNat_fin :: FinTypeC
sigNat_fin =
  (:) (unsafeCoerce SigNat_O) ((:) (unsafeCoerce SigNat_S) [])

encode_nat :: Codable SigNat Prelude.Int
encode_nat n =
  app (repeat SigNat_S n) ((:) SigNat_O [])

select :: Prelude.Int -> Prelude.Int -> (T0 T) -> (T0 a1) -> T0 a1
select m n i v =
  map0 (nth n v) m i

fill :: Prelude.Int -> Prelude.Int -> (T0 T) -> (T0 a1) -> (T0 a1) -> T0 a1
fill _ n i init v =
  case i of {
   Nil -> init;
   Cons i0 m' i' -> replace n (fill m' n i' init (tl m' v)) i0 (hd m' v)}

fill_default :: Prelude.Int -> Prelude.Int -> (T0 T) -> a1 -> (T0 a1) -> T0 a1
fill_default m n i def v =
  fill m n i (const def n) v

liftTapes_trans :: FinType0 -> Prelude.Int -> Prelude.Int -> FinType0 -> (PTM EqType_X) -> (T0 T) -> ((,) EqType_X (T0 (Prelude.Maybe EqType_X))) -> (,) EqType_X
                   (T0 ((,) (Prelude.Maybe EqType_X) Move))
liftTapes_trans sig m n _ pM i pat =
  case pat of {
   (,) q sym -> case trans sig m (projT1 pM) ((,) q (select m n i sym)) of {
                 (,) q' act -> (,) q' (fill_default m n i ((,) Prelude.Nothing N) act)}}

liftTapes_TM :: FinType0 -> Prelude.Int -> Prelude.Int -> FinType0 -> (PTM EqType_X) -> (T0 T) -> MTM
liftTapes_TM sig m n f pM i =
  Build_mTM (states sig m (projT1 pM)) (liftTapes_trans sig m n f pM i) (start sig m (projT1 pM)) (halt sig m (projT1 pM))

liftTapes :: FinType0 -> Prelude.Int -> Prelude.Int -> FinType0 -> (PTM EqType_X) -> (T0 T) -> PTM EqType_X
liftTapes sig m n f pM i =
  ExistT (liftTapes_TM sig m n f pM i) (projT2 pM)

surject :: (a2 -> Prelude.Maybe a1) -> a1 -> a2 -> a1
surject g def t =
  case g t of {
   Prelude.Just s -> s;
   Prelude.Nothing -> def}

map_act :: (a1 -> a2) -> ((,) (Prelude.Maybe a1) Move) -> (,) (Prelude.Maybe a2) Move
map_act f =
  map_fst (map_opt f)

surjectReadSymbols :: FinType0 -> FinType0 -> Prelude.Int -> (Retract EqType_X EqType_X) -> EqType_X -> (T0 (Prelude.Maybe EqType_X)) -> T0 (Prelude.Maybe EqType_X)
surjectReadSymbols _ _ n inj def =
  map0 (map_opt (surject (retr_g inj) def)) n

lift_trans :: FinType0 -> FinType0 -> Prelude.Int -> FinType0 -> (PTM EqType_X) -> (Retract EqType_X EqType_X) -> EqType_X -> ((,) EqType_X
              (T0 (Prelude.Maybe EqType_X))) -> (,) EqType_X (T0 ((,) (Prelude.Maybe EqType_X) Move))
lift_trans sig tau n _ pMSig inj def pat =
  case pat of {
   (,) q sym -> case trans sig n (projT1 pMSig) ((,) q (surjectReadSymbols sig tau n inj def sym)) of {
                 (,) q' act -> (,) q' (map0 (map_act (retr_f inj)) n act)}}

liftAlphabet_TM :: FinType0 -> FinType0 -> Prelude.Int -> FinType0 -> (PTM EqType_X) -> (Retract EqType_X EqType_X) -> EqType_X -> MTM
liftAlphabet_TM sig tau n f pMSig inj def =
  Build_mTM (states sig n (projT1 pMSig)) (lift_trans sig tau n f pMSig inj def) (start sig n (projT1 pMSig)) (halt sig n (projT1 pMSig))

liftAlphabet :: FinType0 -> FinType0 -> Prelude.Int -> FinType0 -> (PTM EqType_X) -> (Retract EqType_X EqType_X) -> EqType_X -> PTM EqType_X
liftAlphabet sig tau n f pMSig inj def =
  ExistT (liftAlphabet_TM sig tau n f pMSig inj def) (projT2 pMSig)

switch_trans :: Prelude.Int -> FinType0 -> FinType0 -> (PTM EqType_X) -> FinType0 -> (EqType_X -> PTM EqType_X) -> ((,) (Sum EqType_X (SigT EqType_X EqType_X))
                (T0 (Prelude.Maybe EqType_X))) -> (,) (Sum EqType_X (SigT EqType_X EqType_X)) (T0 ((,) (Prelude.Maybe EqType_X) Move))
switch_trans n sig _ pM1 _ pMf pat =
  case pat of {
   (,) q s ->
    case q of {
     Inl q0 ->
      case halt sig n (projT1 pM1) q0 of {
       Prelude.True -> (,) (Inr (ExistT (projT2 pM1 q0) (start sig n (projT1 (pMf (projT2 pM1 q0)))))) (nop_action n sig);
       Prelude.False -> case trans sig n (projT1 pM1) ((,) q0 s) of {
                         (,) q' a -> (,) (Inl q') a}};
     Inr q0 -> case trans sig n (projT1 (pMf (projT1 q0))) ((,) (projT2 q0) s) of {
                (,) q' a -> (,) (Inr (ExistT (projT1 q0) q')) a}}}

switch_halt :: Prelude.Int -> FinType0 -> FinType0 -> (PTM EqType_X) -> FinType0 -> (EqType_X -> PTM EqType_X) -> (Sum EqType_X (SigT EqType_X EqType_X)) -> Prelude.Bool
switch_halt n sig _ _ _ pMf q =
  case q of {
   Inl _ -> Prelude.False;
   Inr q0 -> halt sig n (projT1 (pMf (projT1 q0))) (projT2 q0)}

switchTM :: Prelude.Int -> FinType0 -> FinType0 -> (PTM EqType_X) -> FinType0 -> (EqType_X -> PTM EqType_X) -> MTM
switchTM n sig f pM1 f' pMf =
  Build_mTM
    (finType_CS (sum_eq_dec (eqType_dec (type0 (states sig n (projT1 pM1)))) (eqType_depPair (type0 f) (\f0 -> type0 (states sig n (projT1 (pMf f0))))))
      (finTypeC_sum (states sig n (projT1 pM1))
        (finType_CS (eqType_depPair (type0 f) (\f0 -> type0 (states sig n (projT1 (pMf f0))))) (finType_depPair f (\f0 -> states sig n (projT1 (pMf f0)))))))
    (unsafeCoerce switch_trans n sig f pM1 f' pMf) (unsafeCoerce (Inl (start sig n (projT1 pM1)))) (unsafeCoerce switch_halt n sig f pM1 f' pMf)

switch_p :: Prelude.Int -> FinType0 -> FinType0 -> (PTM EqType_X) -> FinType0 -> (EqType_X -> PTM EqType_X) -> EqType_X -> EqType_X
switch_p n sig _ pM1 _ pMf q =
  case unsafeCoerce q of {
   Inl q0 -> projT2 (pMf (projT2 pM1 q0)) (start sig n (projT1 (pMf (projT2 pM1 q0))));
   Inr q0 -> projT2 (pMf (projT1 q0)) (projT2 q0)}

switch :: Prelude.Int -> FinType0 -> FinType0 -> (PTM EqType_X) -> FinType0 -> (EqType_X -> PTM EqType_X) -> PTM EqType_X
switch n sig f pM1 f' pMf =
  ExistT (switchTM n sig f pM1 f' pMf) (switch_p n sig f pM1 f' pMf)

if0 :: Prelude.Int -> FinType0 -> (PTM Prelude.Bool) -> FinType0 -> (PTM EqType_X) -> (PTM EqType_X) -> PTM EqType_X
if0 n sig pM1 f pM2 pM3 =
  switch n sig (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce pM1) f (\b -> case unsafeCoerce b of {
                                                                                   Prelude.True -> pM2;
                                                                                   Prelude.False -> pM3})

seq :: Prelude.Int -> FinType0 -> FinType0 -> (PTM EqType_X) -> FinType0 -> (PTM EqType_X) -> PTM EqType_X
seq n sig f1 pM1 f2 pM2 =
  switch n sig f1 pM1 f2 (\_ -> pM2)

while_trans :: Prelude.Int -> FinType0 -> FinType0 -> (PTM (Prelude.Maybe EqType_X)) -> ((,) EqType_X (T0 (Prelude.Maybe EqType_X))) -> (,) EqType_X
               (T0 ((,) (Prelude.Maybe EqType_X) Move))
while_trans n sig _ pM pat =
  case pat of {
   (,) q s -> case halt sig n (projT1 pM) q of {
               Prelude.True -> (,) (start sig n (projT1 pM)) (nop_action n sig);
               Prelude.False -> trans sig n (projT1 pM) ((,) q s)}}

whileTM :: Prelude.Int -> FinType0 -> FinType0 -> (PTM (Prelude.Maybe EqType_X)) -> MTM
whileTM n sig f pM =
  Build_mTM (states sig n (projT1 pM)) (while_trans n sig f pM) (start sig n (projT1 pM)) (\q ->
    andb (halt sig n (projT1 pM) q) (case projT2 pM q of {
                                      Prelude.Just _ -> Prelude.True;
                                      Prelude.Nothing -> Prelude.False}))

while_part :: Prelude.Int -> FinType0 -> FinType0 -> (PTM (Prelude.Maybe EqType_X)) -> (InhabitedC EqType_X) -> EqType_X -> EqType_X
while_part _ _ _ pM defF q =
  case projT2 pM q of {
   Prelude.Just y -> y;
   Prelude.Nothing -> default0 defF}

while :: Prelude.Int -> FinType0 -> FinType0 -> (PTM (Prelude.Maybe EqType_X)) -> (InhabitedC EqType_X) -> PTM EqType_X
while n sig f pM defF =
  ExistT (whileTM n sig f pM) (while_part n sig f pM defF)

mirror_act :: FinType0 -> ((,) (Prelude.Maybe EqType_X) Move) -> (,) (Prelude.Maybe EqType_X) Move
mirror_act _ =
  map_snd mirror_move

mirror_acts :: Prelude.Int -> FinType0 -> (T0 ((,) (Prelude.Maybe EqType_X) Move)) -> T0 ((,) (Prelude.Maybe EqType_X) Move)
mirror_acts n sig =
  map0 (mirror_act sig) n

mirror_trans :: Prelude.Int -> FinType0 -> FinType0 -> (PTM EqType_X) -> ((,) EqType_X (T0 (Prelude.Maybe EqType_X))) -> (,) EqType_X
                (T0 ((,) (Prelude.Maybe EqType_X) Move))
mirror_trans n sig _ pM qsym =
  case trans sig n (projT1 pM) qsym of {
   (,) q' act -> (,) q' (mirror_acts n sig act)}

mirrorTM :: Prelude.Int -> FinType0 -> FinType0 -> (PTM EqType_X) -> MTM
mirrorTM n sig f pM =
  Build_mTM (states sig n (projT1 pM)) (mirror_trans n sig f pM) (start sig n (projT1 pM)) (halt sig n (projT1 pM))

mirror :: Prelude.Int -> FinType0 -> FinType0 -> (PTM EqType_X) -> PTM EqType_X
mirror n sig f pM =
  ExistT (mirrorTM n sig f pM) (projT2 pM)

relabel :: FinType0 -> Prelude.Int -> FinType0 -> FinType0 -> (SigT MTM (EqType_X -> EqType_X)) -> (EqType_X -> EqType_X) -> PTM EqType_X
relabel _ _ _ _ pM p =
  ExistT (projT1 pM) (\q -> p (projT2 pM q))

return :: FinType0 -> Prelude.Int -> FinType0 -> (SigT MTM (EqType_X -> EqType_X)) -> FinType0 -> EqType_X -> PTM EqType_X
return sig n f pM f' p =
  relabel sig n f f' pM (\_ -> p)

data Boundary =
   START
 | STOP
 | UNKNOWN

boundary_rect :: a1 -> a1 -> a1 -> Boundary -> a1
boundary_rect f f0 f1 b =
  case b of {
   START -> f;
   STOP -> f0;
   UNKNOWN -> f1}

boundary_rec :: a1 -> a1 -> a1 -> Boundary -> a1
boundary_rec =
  boundary_rect

boundary_eq :: Boundary -> Boundary -> Dec
boundary_eq x y =
  boundary_rec (\x0 -> case x0 of {
                        START -> Left;
                        _ -> Right}) (\x0 -> case x0 of {
                                              STOP -> Left;
                                              _ -> Right}) (\x0 -> case x0 of {
                                                                    UNKNOWN -> Left;
                                                                    _ -> Right}) x y

boundary_fin :: FinTypeC
boundary_fin =
  (:) (unsafeCoerce START) ((:) (unsafeCoerce STOP) ((:) (unsafeCoerce UNKNOWN) []))

doAct_TM :: FinType0 -> ((,) (Prelude.Maybe EqType_X) Move) -> MTM
doAct_TM _ act =
  Build_mTM (finType_CS bool_eq_dec finTypeC_bool) (\_ -> (,) (unsafeCoerce Prelude.True) (Cons act 0 Nil)) (unsafeCoerce Prelude.False) (\x -> unsafeCoerce x)

doAct :: FinType0 -> ((,) (Prelude.Maybe EqType_X) Move) -> PTM Unit
doAct sig act =
  ExistT (doAct_TM sig act) (\_ -> Tt)

write :: FinType0 -> EqType_X -> PTM Unit
write sig c =
  doAct sig ((,) (Prelude.Just c) N)

move :: FinType0 -> Move -> PTM Unit
move sig d =
  doAct sig ((,) Prelude.Nothing d)

writeMove :: FinType0 -> EqType_X -> Move -> PTM Unit
writeMove sig c d =
  doAct sig ((,) (Prelude.Just c) d)

readChar_TM :: FinType0 -> MTM
readChar_TM sig =
  Build_mTM (finType_CS (sum_eq_dec bool_eq_dec (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS bool_eq_dec finTypeC_bool) sig)) (\pat ->
    case pat of {
     (,) _ sym ->
      case nth (Prelude.succ 0) sym (F1 0) of {
       Prelude.Just c -> (,) (unsafeCoerce (Inr c)) (Cons ((,) Prelude.Nothing N) 0 Nil);
       Prelude.Nothing -> (,) (unsafeCoerce (Inl Prelude.True)) (Cons ((,) Prelude.Nothing N) 0 Nil)}}) (unsafeCoerce (Inl Prelude.False)) (\s ->
    case unsafeCoerce s of {
     Inl b -> b;
     Inr _ -> Prelude.True})

readChar :: FinType0 -> SigT MTM (EqType_X -> Prelude.Maybe EqType_X)
readChar sig =
  ExistT (readChar_TM sig) (\s -> case unsafeCoerce s of {
                                   Inl _ -> Prelude.Nothing;
                                   Inr s0 -> Prelude.Just s0})

nullTM :: FinType0 -> MTM
nullTM _ =
  Build_mTM (finType_CS unit_eq_dec finTypeC_unit) (\pat -> case pat of {
                                                             (,) q _ -> (,) q Nil}) (unsafeCoerce Tt) (\_ -> Prelude.True)

null :: FinType0 -> PTM Unit
null sig =
  ExistT (nullTM sig) (\_ -> Tt)

nop :: FinType0 -> Prelude.Int -> PTM Unit
nop sig n =
  unsafeCoerce liftTapes sig 0 n (finType_CS unit_eq_dec finTypeC_unit) (null sig) Nil

movePar :: FinType0 -> Move -> Move -> PTM Unit
movePar sig d1 d2 =
  unsafeCoerce seq (Prelude.succ (Prelude.succ 0)) sig (finType_CS unit_eq_dec finTypeC_unit)
    (liftTapes sig (Prelude.succ 0) (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce move sig d1) (Cons (F1 (Prelude.succ 0)) 0 Nil))
    (finType_CS unit_eq_dec finTypeC_unit)
    (liftTapes sig (Prelude.succ 0) (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce move sig d2) (Cons (FS (Prelude.succ 0) (F1 0))
      0 Nil))

readChar_at :: FinType0 -> Prelude.Int -> T -> PTM (Prelude.Maybe EqType_X)
readChar_at sig n k =
  unsafeCoerce liftTapes sig (Prelude.succ 0) n (finType_CS (option_eq_dec (eqType_dec (type0 sig))) (finTypeC_Option sig)) (readChar sig) (Cons k 0 Nil)

copySymbols_Step :: FinType0 -> (EqType_X -> Prelude.Bool) -> PTM (Prelude.Maybe Unit)
copySymbols_Step sig f =
  unsafeCoerce switch (Prelude.succ (Prelude.succ 0)) sig (finType_CS (option_eq_dec (eqType_dec (type0 sig))) (finTypeC_Option sig))
    (readChar_at sig (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0)))
    (finType_CS (option_eq_dec unit_eq_dec) (finTypeC_Option (finType_CS unit_eq_dec finTypeC_unit))) (\b ->
    case unsafeCoerce b of {
     Prelude.Just x ->
      case f x of {
       Prelude.True ->
        return sig (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit)
          (liftTapes sig (Prelude.succ 0) (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce write sig x) (Cons (FS (Prelude.succ 0)
            (F1 0)) 0 Nil)) (finType_CS (option_eq_dec unit_eq_dec) (finTypeC_Option (finType_CS unit_eq_dec finTypeC_unit))) (unsafeCoerce (Prelude.Just Tt));
       Prelude.False ->
        return sig (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit)
          (seq (Prelude.succ (Prelude.succ 0)) sig (finType_CS unit_eq_dec finTypeC_unit)
            (liftTapes sig (Prelude.succ 0) (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce write sig x) (Cons (FS (Prelude.succ 0)
              (F1 0)) 0 Nil)) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce movePar sig R R))
          (finType_CS (option_eq_dec unit_eq_dec) (finTypeC_Option (finType_CS unit_eq_dec finTypeC_unit))) (unsafeCoerce Prelude.Nothing)};
     Prelude.Nothing ->
      return sig (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce nop sig (Prelude.succ (Prelude.succ 0)))
        (finType_CS (option_eq_dec unit_eq_dec) (finTypeC_Option (finType_CS unit_eq_dec finTypeC_unit))) (unsafeCoerce (Prelude.Just Tt))})

copySymbols :: FinType0 -> (EqType_X -> Prelude.Bool) -> PTM Unit
copySymbols sig f =
  unsafeCoerce while (Prelude.succ (Prelude.succ 0)) sig (finType_CS unit_eq_dec finTypeC_unit) (copySymbols_Step sig f) inhabited_unit

copySymbols_L :: FinType0 -> (EqType_X -> Prelude.Bool) -> PTM EqType_X
copySymbols_L sig f =
  mirror (Prelude.succ (Prelude.succ 0)) sig (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce copySymbols sig f)

moveToSymbol_Step :: FinType0 -> (EqType_X -> Prelude.Bool) -> (EqType_X -> EqType_X) -> PTM (Prelude.Maybe Unit)
moveToSymbol_Step sig f g =
  unsafeCoerce switch (Prelude.succ 0) sig (finType_CS (option_eq_dec (eqType_dec (type0 sig))) (finTypeC_Option sig)) (readChar sig)
    (finType_CS (option_eq_dec unit_eq_dec) (finTypeC_Option (finType_CS unit_eq_dec finTypeC_unit))) (\b ->
    case unsafeCoerce b of {
     Prelude.Just x ->
      case f x of {
       Prelude.True ->
        return sig (Prelude.succ 0) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce write sig (g x))
          (finType_CS (option_eq_dec unit_eq_dec) (finTypeC_Option (finType_CS unit_eq_dec finTypeC_unit))) (unsafeCoerce (Prelude.Just Tt));
       Prelude.False ->
        return sig (Prelude.succ 0) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce writeMove sig (g x) R)
          (finType_CS (option_eq_dec unit_eq_dec) (finTypeC_Option (finType_CS unit_eq_dec finTypeC_unit))) (unsafeCoerce Prelude.Nothing)};
     Prelude.Nothing ->
      return sig (Prelude.succ 0) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce nop sig (Prelude.succ 0))
        (finType_CS (option_eq_dec unit_eq_dec) (finTypeC_Option (finType_CS unit_eq_dec finTypeC_unit))) (unsafeCoerce (Prelude.Just Tt))})

moveToSymbol :: FinType0 -> (EqType_X -> Prelude.Bool) -> (EqType_X -> EqType_X) -> PTM Unit
moveToSymbol sig f g =
  unsafeCoerce while (Prelude.succ 0) sig (finType_CS unit_eq_dec finTypeC_unit) (moveToSymbol_Step sig f g) inhabited_unit

moveToSymbol_L :: FinType0 -> (EqType_X -> Prelude.Bool) -> (EqType_X -> EqType_X) -> PTM EqType_X
moveToSymbol_L sig f g =
  mirror (Prelude.succ 0) sig (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce moveToSymbol sig f g)

isStop :: FinType0 -> EqType_X -> Prelude.Bool
isStop _ s =
  case unsafeCoerce s of {
   Inl b -> case b of {
             STOP -> Prelude.True;
             _ -> Prelude.False};
   Inr _ -> Prelude.False}

isStart :: FinType0 -> EqType_X -> Prelude.Bool
isStart _ s =
  case unsafeCoerce s of {
   Inl b -> case b of {
             START -> Prelude.True;
             _ -> Prelude.False};
   Inr _ -> Prelude.False}

moveRight :: FinType0 -> PTM EqType_X
moveRight sig =
  return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ 0)
    (finType_CS unit_eq_dec finTypeC_unit)
    (unsafeCoerce moveToSymbol (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig))
      (isStop sig) id) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce Tt)

moveLeft :: FinType0 -> PTM EqType_X
moveLeft sig =
  return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ 0)
    (finType_CS unit_eq_dec finTypeC_unit)
    (moveToSymbol_L (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (isStart sig) id)
    (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce Tt)

reset :: FinType0 -> PTM EqType_X
reset =
  moveRight

resetEmpty :: FinType0 -> PTM Unit
resetEmpty sig =
  move (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) R

resetEmpty1 :: FinType0 -> PTM EqType_X
resetEmpty1 sig =
  seq (Prelude.succ 0) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig))
    (finType_CS unit_eq_dec finTypeC_unit)
    (unsafeCoerce move (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) R)
    (finType_CS unit_eq_dec finTypeC_unit)
    (unsafeCoerce move (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) R)

copyValue :: FinType0 -> PTM EqType_X
copyValue sig =
  seq (Prelude.succ (Prelude.succ 0)) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig))
    (finType_CS unit_eq_dec finTypeC_unit)
    (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ 0)
      (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit) (moveRight sig) (Cons (F1 (Prelude.succ 0)) 0 Nil)) (finType_CS unit_eq_dec finTypeC_unit)
    (copySymbols_L (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (isStart sig))

moveValue :: FinType0 -> PTM Unit
moveValue sig =
  unsafeCoerce seq (Prelude.succ (Prelude.succ 0)) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig)))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (finType_CS unit_eq_dec finTypeC_unit)
    (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ 0)
      (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit) (reset sig) (Cons (FS (Prelude.succ 0) (F1 0)) 0 Nil))
    (finType_CS unit_eq_dec finTypeC_unit)
    (seq (Prelude.succ (Prelude.succ 0)) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig)))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (finType_CS unit_eq_dec finTypeC_unit) (copyValue sig) (finType_CS unit_eq_dec finTypeC_unit)
      (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ 0)
        (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit) (reset sig) (Cons (F1 (Prelude.succ 0)) 0 Nil)))

translate :: FinType0 -> FinType0 -> (Retract EqType_X EqType_X) -> (Retract EqType_X EqType_X) -> EqType_X -> EqType_X
translate _ _ retr1 retr2 t =
  case unsafeCoerce t of {
   Inl _ -> t;
   Inr x -> case retr_g retr1 x of {
             Prelude.Just y -> unsafeCoerce (Inr (retr_f retr2 y));
             Prelude.Nothing -> unsafeCoerce (Inl UNKNOWN)}}

translate' :: FinType0 -> FinType0 -> (Retract EqType_X EqType_X) -> (Retract EqType_X EqType_X) -> PTM Unit
translate' tau sig retr1 retr2 =
  moveToSymbol (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 tau))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) tau)) (isStop tau)
    (translate tau sig retr1 retr2)

translate0 :: FinType0 -> FinType0 -> (Retract EqType_X EqType_X) -> (Retract EqType_X EqType_X) -> PTM EqType_X
translate0 tau sig retr1 retr2 =
  seq (Prelude.succ 0) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 tau))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) tau))
    (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce translate' tau sig retr1 retr2) (finType_CS unit_eq_dec finTypeC_unit) (moveLeft tau)

retract_plus :: FinType0 -> FinType0 -> (Retract EqType_X EqType_X) -> Retract EqType_X EqType_X
retract_plus _ _ retr =
  unsafeCoerce retract_sum retract_id retr

changeAlphabet :: FinType0 -> FinType0 -> Prelude.Int -> FinType0 -> (PTM EqType_X) -> (Retract EqType_X EqType_X) -> PTM EqType_X
changeAlphabet sig tau n f pM retr =
  liftAlphabet (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (FinType
    (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 tau))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) tau)) n f pM (retract_plus sig tau retr)
    (unsafeCoerce (Inl UNKNOWN))

writeString :: FinType0 -> Move -> (([]) EqType_X) -> PTM Unit
writeString sig d l =
  case l of {
   [] -> nop sig (Prelude.succ 0);
   (:) x xs ->
    case xs of {
     [] -> write sig x;
     (:) _ _ ->
      unsafeCoerce seq (Prelude.succ 0) sig (finType_CS unit_eq_dec finTypeC_unit) (writeMove sig x d) (finType_CS unit_eq_dec finTypeC_unit)
        (unsafeCoerce writeString sig d xs)}}

writeValue :: FinType0 -> (([]) EqType_X) -> PTM Unit
writeValue sig str =
  writeString (finType_CS (sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) L
    (rev ((:) (unsafeCoerce (Inl START)) (app (map (unsafeCoerce (\x -> Inr x)) str) ((:) (unsafeCoerce (Inl STOP)) []))))

type Var = Prelude.Int

data Com =
   VarT Var
 | AppT
 | LamT
 | RetT

type Pro = ([]) Com

data ACom =
   RetAT
 | LamAT
 | AppAT

aCom_rect :: a1 -> a1 -> a1 -> ACom -> a1
aCom_rect f f0 f1 a =
  case a of {
   RetAT -> f;
   LamAT -> f0;
   AppAT -> f1}

aCom_rec :: a1 -> a1 -> a1 -> ACom -> a1
aCom_rec =
  aCom_rect

aCom2Com :: ACom -> Com
aCom2Com a =
  case a of {
   RetAT -> RetT;
   LamAT -> LamT;
   AppAT -> AppT}

aCom_eq_dec :: ACom -> ACom -> Dec
aCom_eq_dec x y =
  aCom_rec (\x0 -> case x0 of {
                    RetAT -> Left;
                    _ -> Right}) (\x0 -> case x0 of {
                                          LamAT -> Left;
                                          _ -> Right}) (\x0 -> case x0 of {
                                                                AppAT -> Left;
                                                                _ -> Right}) x y

aCom_finType :: FinTypeC
aCom_finType =
  (:) (unsafeCoerce RetAT) ((:) (unsafeCoerce LamAT) ((:) (unsafeCoerce AppAT) []))

aCom_inhab :: InhabitedC ACom
aCom_inhab =
  RetAT

encode_ACom :: Codable ACom ACom
encode_ACom =
  unsafeCoerce encode_Finite (FinType (unsafeCoerce aCom_eq_dec) aCom_finType)

com_to_sum :: Com -> Sum Prelude.Int ACom
com_to_sum t =
  case t of {
   VarT x -> Inl x;
   AppT -> Inr AppAT;
   LamT -> Inr LamAT;
   RetT -> Inr RetAT}

type SigCom = SigSum SigNat ACom

sigCom_fin :: FinType0
sigCom_fin =
  FinType (unsafeCoerce sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))

encode_Com :: Codable SigCom Com
encode_Com x =
  encode (encode_sum encode_nat encode_ACom) (com_to_sum x)

type SigHAdd = SigNat

sigHAdd_fin :: FinType0
sigHAdd_fin =
  FinType (unsafeCoerce sigNat_eq) sigNat_fin

type SigPro = SigList SigCom

encode_Prog :: Codable SigPro Pro
encode_Prog =
  encode_list0 encode_Com

sigPro_fin :: FinType0
sigPro_fin =
  FinType (unsafeCoerce sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
    (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))

type SigHClos = SigPair SigHAdd SigPro

sigHClos_fin :: FinType0
sigHClos_fin =
  FinType (unsafeCoerce sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
    (sigPair_fin (finType_CS sigNat_eq sigNat_fin)
      (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
        (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))

type SigHEntr' = SigPair SigHClos SigHAdd

sigHEntr'_fin :: FinType0
sigHEntr'_fin =
  FinType (unsafeCoerce sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq)
    (sigPair_fin
      (finType_CS (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
        (sigPair_fin (finType_CS sigNat_eq sigNat_fin)
          (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
            (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
      (finType_CS sigNat_eq sigNat_fin))

type SigHEntr = SigOption SigHEntr'

sigHEntr_fin :: FinType0
sigHEntr_fin =
  FinType (unsafeCoerce sigOption_dec (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq))
    (sigOption_fin
      (finType_CS (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq)
        (sigPair_fin
          (finType_CS (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
            (sigPair_fin (finType_CS sigNat_eq sigNat_fin)
              (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
          (finType_CS sigNat_eq sigNat_fin))))

type SigHeap = SigList SigHEntr

caseNat :: PTM Prelude.Bool
caseNat =
  unsafeCoerce seq (Prelude.succ 0)
    (finType_CS (sum_eq_dec boundary_eq sigNat_eq) (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS sigNat_eq sigNat_fin)))
    (finType_CS unit_eq_dec finTypeC_unit)
    (move (finType_CS (sum_eq_dec boundary_eq sigNat_eq) (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS sigNat_eq sigNat_fin))) R)
    (finType_CS bool_eq_dec finTypeC_bool)
    (switch (Prelude.succ 0) (finType_CS (sum_eq_dec boundary_eq sigNat_eq) (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS sigNat_eq sigNat_fin)))
      (finType_CS
        (option_eq_dec
          (eqType_dec (type0 (finType_CS (sum_eq_dec boundary_eq sigNat_eq) (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS sigNat_eq sigNat_fin))))))
        (finTypeC_Option (finType_CS (sum_eq_dec boundary_eq sigNat_eq) (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS sigNat_eq sigNat_fin)))))
      (unsafeCoerce readChar (finType_CS (sum_eq_dec boundary_eq sigNat_eq) (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS sigNat_eq sigNat_fin))))
      (finType_CS bool_eq_dec finTypeC_bool) (\o ->
      case unsafeCoerce o of {
       Prelude.Just e ->
        case e of {
         Inl _ ->
          return (finType_CS (sum_eq_dec boundary_eq sigNat_eq) (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS sigNat_eq sigNat_fin))) (Prelude.succ 0)
            (finType_CS unit_eq_dec finTypeC_unit)
            (unsafeCoerce nop (finType_CS (sum_eq_dec boundary_eq sigNat_eq) (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS sigNat_eq sigNat_fin)))
              (Prelude.succ 0)) (finType_CS bool_eq_dec finTypeC_bool) (default0 (unsafeCoerce inhabited_bool));
         Inr y ->
          case y of {
           SigNat_O ->
            return (finType_CS (sum_eq_dec boundary_eq sigNat_eq) (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS sigNat_eq sigNat_fin))) (Prelude.succ
              0) (finType_CS unit_eq_dec finTypeC_unit)
              (unsafeCoerce move (finType_CS (sum_eq_dec boundary_eq sigNat_eq) (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS sigNat_eq sigNat_fin)))
                L) (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.False);
           SigNat_S ->
            return (finType_CS (sum_eq_dec boundary_eq sigNat_eq) (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS sigNat_eq sigNat_fin))) (Prelude.succ
              0) (finType_CS unit_eq_dec finTypeC_unit)
              (unsafeCoerce write (finType_CS (sum_eq_dec boundary_eq sigNat_eq) (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS sigNat_eq sigNat_fin)))
                (Inl START)) (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.True)}};
       Prelude.Nothing ->
        return (finType_CS (sum_eq_dec boundary_eq sigNat_eq) (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS sigNat_eq sigNat_fin))) (Prelude.succ 0)
          (finType_CS unit_eq_dec finTypeC_unit)
          (unsafeCoerce nop (finType_CS (sum_eq_dec boundary_eq sigNat_eq) (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS sigNat_eq sigNat_fin)))
            (Prelude.succ 0)) (finType_CS bool_eq_dec finTypeC_bool) (default0 (unsafeCoerce inhabited_bool))}))

constr_S :: SigT MTM (EqType_X -> Unit)
constr_S =
  unsafeCoerce seq (Prelude.succ 0)
    (finType_CS (sum_eq_dec boundary_eq sigNat_eq) (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS sigNat_eq sigNat_fin)))
    (finType_CS unit_eq_dec finTypeC_unit)
    (writeMove (finType_CS (sum_eq_dec boundary_eq sigNat_eq) (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS sigNat_eq sigNat_fin)))
      (unsafeCoerce (Inr SigNat_S)) L) (finType_CS unit_eq_dec finTypeC_unit)
    (write (finType_CS (sum_eq_dec boundary_eq sigNat_eq) (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS sigNat_eq sigNat_fin)))
      (unsafeCoerce (Inl START)))

constr_O :: PTM Unit
constr_O =
  writeValue (finType_CS sigNat_eq sigNat_fin) ((:) (unsafeCoerce SigNat_O) [])

caseSum :: FinType0 -> FinType0 -> PTM Prelude.Bool
caseSum sigX sigY =
  unsafeCoerce seq (Prelude.succ 0)
    (finType_CS (sum_eq_dec boundary_eq (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigSum_fin sigX sigY))))
    (finType_CS unit_eq_dec finTypeC_unit)
    (move
      (finType_CS (sum_eq_dec boundary_eq (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigSum_fin sigX sigY)))) R)
    (finType_CS bool_eq_dec finTypeC_bool)
    (switch (Prelude.succ 0)
      (finType_CS (sum_eq_dec boundary_eq (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigSum_fin sigX sigY))))
      (finType_CS
        (option_eq_dec
          (eqType_dec
            (type0
              (finType_CS (sum_eq_dec boundary_eq (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
                (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigSum_fin sigX sigY)))))))
        (finTypeC_Option
          (finType_CS (sum_eq_dec boundary_eq (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
            (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigSum_fin sigX sigY))))))
      (unsafeCoerce readChar
        (finType_CS (sum_eq_dec boundary_eq (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
          (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigSum_fin sigX sigY)))))
      (finType_CS bool_eq_dec finTypeC_bool) (\o ->
      case unsafeCoerce o of {
       Prelude.Just e ->
        case e of {
         Inl _ ->
          return
            (finType_CS (sum_eq_dec boundary_eq (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
              (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigSum_fin sigX sigY))))
            (Prelude.succ 0) (finType_CS unit_eq_dec finTypeC_unit)
            (unsafeCoerce nop
              (finType_CS (sum_eq_dec boundary_eq (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
                (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigSum_fin sigX sigY))))
              (Prelude.succ 0)) (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.True);
         Inr y ->
          case y of {
           SigSum_inl ->
            return
              (finType_CS (sum_eq_dec boundary_eq (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
                (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigSum_fin sigX sigY))))
              (Prelude.succ 0) (finType_CS unit_eq_dec finTypeC_unit)
              (unsafeCoerce write
                (finType_CS (sum_eq_dec boundary_eq (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
                  (finTypeC_sum (finType_CS boundary_eq boundary_fin)
                    (finType_CS (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigSum_fin sigX sigY)))) (Inl START))
              (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.True);
           SigSum_inr ->
            return
              (finType_CS (sum_eq_dec boundary_eq (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
                (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigSum_fin sigX sigY))))
              (Prelude.succ 0) (finType_CS unit_eq_dec finTypeC_unit)
              (unsafeCoerce write
                (finType_CS (sum_eq_dec boundary_eq (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
                  (finTypeC_sum (finType_CS boundary_eq boundary_fin)
                    (finType_CS (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigSum_fin sigX sigY)))) (Inl START))
              (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.False);
           _ ->
            return
              (finType_CS (sum_eq_dec boundary_eq (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
                (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigSum_fin sigX sigY))))
              (Prelude.succ 0) (finType_CS unit_eq_dec finTypeC_unit)
              (unsafeCoerce nop
                (finType_CS (sum_eq_dec boundary_eq (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
                  (finTypeC_sum (finType_CS boundary_eq boundary_fin)
                    (finType_CS (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigSum_fin sigX sigY)))) (Prelude.succ 0))
              (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.True)}};
       Prelude.Nothing ->
        return
          (finType_CS (sum_eq_dec boundary_eq (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
            (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigSum_fin sigX sigY))))
          (Prelude.succ 0) (finType_CS unit_eq_dec finTypeC_unit)
          (unsafeCoerce nop
            (finType_CS (sum_eq_dec boundary_eq (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
              (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigSum_fin sigX sigY))))
            (Prelude.succ 0)) (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.True)}))

constr_inl :: FinType0 -> FinType0 -> PTM Unit
constr_inl sigX sigY =
  unsafeCoerce seq (Prelude.succ 0)
    (finType_CS (sum_eq_dec boundary_eq (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigSum_fin sigX sigY))))
    (finType_CS unit_eq_dec finTypeC_unit)
    (writeMove
      (finType_CS (sum_eq_dec boundary_eq (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigSum_fin sigX sigY))))
      (unsafeCoerce (Inr SigSum_inl)) L) (finType_CS unit_eq_dec finTypeC_unit)
    (write
      (finType_CS (sum_eq_dec boundary_eq (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigSum_fin sigX sigY))))
      (unsafeCoerce (Inl START)))

retract_sigOption_sigSum :: FinType0 -> Retract (SigSum EqType_X Empty_set) (SigOption EqType_X)
retract_sigOption_sigSum _ =
  Build_Retract (\x -> case x of {
                        SigSum_X a -> SigOption_X a;
                        SigSum_Y _ -> Prelude.error "absurd case";
                        SigSum_inl -> SigOption_Some;
                        SigSum_inr -> SigOption_None}) (\y ->
    case y of {
     SigOption_X a -> Prelude.Just (SigSum_X a);
     SigOption_None -> Prelude.Just SigSum_inr;
     SigOption_Some -> Prelude.Just SigSum_inl})

caseOption :: FinType0 -> PTM Prelude.Bool
caseOption sigX =
  unsafeCoerce if0 (Prelude.succ 0) (FinType
    (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 (finType_CS (sigOption_dec (eqType_dec (type0 sigX))) (sigOption_fin sigX)))))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigOption_dec (eqType_dec (type0 sigX))) (sigOption_fin sigX))))
    (changeAlphabet
      (finType_CS (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 (FinType (unsafeCoerce empty_set_eq_dec) finTypeC_Empty_set))))
        (sigSum_fin sigX (FinType (unsafeCoerce empty_set_eq_dec) finTypeC_Empty_set))) (finType_CS (sigOption_dec (eqType_dec (type0 sigX))) (sigOption_fin sigX))
      (Prelude.succ 0) (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce caseSum sigX (FinType (unsafeCoerce empty_set_eq_dec) finTypeC_Empty_set))
      (unsafeCoerce retract_sigOption_sigSum sigX)) (finType_CS bool_eq_dec finTypeC_bool)
    (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 (finType_CS (sigOption_dec (eqType_dec (type0 sigX))) (sigOption_fin sigX)))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigOption_dec (eqType_dec (type0 sigX))) (sigOption_fin sigX)))) (Prelude.succ 0)
      (finType_CS unit_eq_dec finTypeC_unit)
      (unsafeCoerce nop (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 (finType_CS (sigOption_dec (eqType_dec (type0 sigX))) (sigOption_fin sigX)))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigOption_dec (eqType_dec (type0 sigX))) (sigOption_fin sigX)))) (Prelude.succ 0))
      (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.True))
    (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 (finType_CS (sigOption_dec (eqType_dec (type0 sigX))) (sigOption_fin sigX)))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigOption_dec (eqType_dec (type0 sigX))) (sigOption_fin sigX)))) (Prelude.succ 0)
      (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce resetEmpty (finType_CS (sigOption_dec (eqType_dec (type0 sigX))) (sigOption_fin sigX)))
      (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.False))

constr_Some :: FinType0 -> PTM Unit
constr_Some sigX =
  unsafeCoerce changeAlphabet
    (finType_CS (sigSum_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 (FinType (unsafeCoerce empty_set_eq_dec) finTypeC_Empty_set))))
      (sigSum_fin sigX (FinType (unsafeCoerce empty_set_eq_dec) finTypeC_Empty_set))) (finType_CS (sigOption_dec (eqType_dec (type0 sigX))) (sigOption_fin sigX))
    (Prelude.succ 0) (finType_CS unit_eq_dec finTypeC_unit) (constr_inl sigX (FinType (unsafeCoerce empty_set_eq_dec) finTypeC_Empty_set))
    (retract_sigOption_sigSum sigX)

caseFin :: FinType0 -> (InhabitedC EqType_X) -> PTM EqType_X
caseFin sig defSig =
  seq (Prelude.succ 0) (finType_CS (sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig))
    (finType_CS unit_eq_dec finTypeC_unit)
    (unsafeCoerce move (finType_CS (sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) R) sig
    (switch (Prelude.succ 0) (finType_CS (sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig))
      (finType_CS
        (option_eq_dec (eqType_dec (type0 (finType_CS (sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)))))
        (finTypeC_Option (finType_CS (sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig))))
      (unsafeCoerce readChar (finType_CS (sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig))) sig (\s ->
      case unsafeCoerce s of {
       Prelude.Just e ->
        case e of {
         Inl _ ->
          return (finType_CS (sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ 0)
            (finType_CS unit_eq_dec finTypeC_unit)
            (unsafeCoerce nop (finType_CS (sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ 0))
            sig (default0 defSig);
         Inr x ->
          return (finType_CS (sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ 0)
            (finType_CS unit_eq_dec finTypeC_unit)
            (unsafeCoerce move (finType_CS (sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) R) sig x};
       Prelude.Nothing ->
        return (finType_CS (sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ 0)
          (finType_CS unit_eq_dec finTypeC_unit)
          (unsafeCoerce nop (finType_CS (sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ 0)) sig
          (default0 defSig)}))

caseCom :: PTM (Prelude.Maybe ACom)
caseCom =
  unsafeCoerce if0 (Prelude.succ 0) (FinType
    (unsafeCoerce sum_eq_dec boundary_eq (sigSum_dec (eqType_dec (type0 (finType_CS sigNat_eq sigNat_fin))) (eqType_dec (type0 (finType_CS aCom_eq_dec aCom_finType)))))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin)
      (finType_CS (sigSum_dec (eqType_dec (type0 (finType_CS sigNat_eq sigNat_fin))) (eqType_dec (type0 (finType_CS aCom_eq_dec aCom_finType))))
        (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))
    (caseSum (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))
    (finType_CS (option_eq_dec aCom_eq_dec) (finTypeC_Option (finType_CS aCom_eq_dec aCom_finType)))
    (return (FinType
      (unsafeCoerce sum_eq_dec boundary_eq
        (sigSum_dec (eqType_dec (type0 (finType_CS sigNat_eq sigNat_fin))) (eqType_dec (type0 (finType_CS aCom_eq_dec aCom_finType)))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin)
        (finType_CS (sigSum_dec (eqType_dec (type0 (finType_CS sigNat_eq sigNat_fin))) (eqType_dec (type0 (finType_CS aCom_eq_dec aCom_finType))))
          (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))) (Prelude.succ 0) (finType_CS unit_eq_dec finTypeC_unit)
      (unsafeCoerce nop (FinType
        (unsafeCoerce sum_eq_dec boundary_eq
          (sigSum_dec (eqType_dec (type0 (finType_CS sigNat_eq sigNat_fin))) (eqType_dec (type0 (finType_CS aCom_eq_dec aCom_finType)))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin)
          (finType_CS (sigSum_dec (eqType_dec (type0 (finType_CS sigNat_eq sigNat_fin))) (eqType_dec (type0 (finType_CS aCom_eq_dec aCom_finType))))
            (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))) (Prelude.succ 0))
      (finType_CS (option_eq_dec aCom_eq_dec) (finTypeC_Option (finType_CS aCom_eq_dec aCom_finType))) (unsafeCoerce Prelude.Nothing))
    (relabel (FinType
      (unsafeCoerce sum_eq_dec boundary_eq
        (eqType_dec
          (type0
            (finType_CS (sigSum_dec (eqType_dec (type0 (finType_CS sigNat_eq sigNat_fin))) (eqType_dec (type0 (finType_CS aCom_eq_dec aCom_finType))))
              (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin)
        (finType_CS (sigSum_dec (eqType_dec (type0 (finType_CS sigNat_eq sigNat_fin))) (eqType_dec (type0 (finType_CS aCom_eq_dec aCom_finType))))
          (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))) (Prelude.succ 0) (FinType (unsafeCoerce aCom_eq_dec) aCom_finType)
      (finType_CS (option_eq_dec aCom_eq_dec) (finTypeC_Option (finType_CS aCom_eq_dec aCom_finType)))
      (changeAlphabet (FinType (unsafeCoerce aCom_eq_dec) aCom_finType)
        (finType_CS (sigSum_dec (eqType_dec (type0 (finType_CS sigNat_eq sigNat_fin))) (eqType_dec (type0 (finType_CS aCom_eq_dec aCom_finType))))
          (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))) (Prelude.succ 0) (FinType (unsafeCoerce aCom_eq_dec) aCom_finType)
        (caseFin (FinType (unsafeCoerce aCom_eq_dec) aCom_finType) (unsafeCoerce aCom_inhab)) (unsafeCoerce retract_sigSum_Y retract_id))
      (unsafeCoerce (\x -> Prelude.Just x)))

constr_varT :: PTM Unit
constr_varT =
  constr_inl (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)

stop :: FinType0 -> EqType_X -> Prelude.Bool
stop _ s =
  case unsafeCoerce s of {
   Inl _ -> Prelude.True;
   Inr s0 -> case s0 of {
              SigList_X _ -> Prelude.False;
              _ -> Prelude.True}}

skip_cons :: FinType0 -> PTM Unit
skip_cons sigX =
  unsafeCoerce seq (Prelude.succ 0) (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (finType_CS unit_eq_dec finTypeC_unit)
    (move (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) R)
    (finType_CS unit_eq_dec finTypeC_unit)
    (moveToSymbol (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (stop sigX) id)

m1 :: FinType0 -> PTM Unit
m1 sigX =
  unsafeCoerce seq (Prelude.succ (Prelude.succ 0)) (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (finType_CS unit_eq_dec finTypeC_unit)
    (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ 0) (Prelude.succ
      (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce skip_cons sigX) (Cons (F1 (Prelude.succ 0)) 0 Nil)) (finType_CS unit_eq_dec finTypeC_unit)
    (seq (Prelude.succ (Prelude.succ 0))
      (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX))))
      (finType_CS unit_eq_dec finTypeC_unit)
      (liftTapes
        (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
          (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ 0) (Prelude.succ
        (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit)
        (unsafeCoerce write
          (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
            (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Inl STOP)) (Cons (FS
        (Prelude.succ 0) (F1 0)) 0 Nil)) (finType_CS unit_eq_dec finTypeC_unit)
      (seq (Prelude.succ (Prelude.succ 0)) (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX))))
        (finType_CS unit_eq_dec finTypeC_unit)
        (unsafeCoerce movePar (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
          (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) L L)
        (finType_CS unit_eq_dec finTypeC_unit)
        (seq (Prelude.succ (Prelude.succ 0)) (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
          (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX))))
          (finType_CS unit_eq_dec finTypeC_unit)
          (copySymbols_L (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
            (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (stop sigX))
          (finType_CS unit_eq_dec finTypeC_unit)
          (liftTapes
            (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
              (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ 0)
            (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit)
            (unsafeCoerce write
              (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
                (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Inl START)) (Cons (FS
            (Prelude.succ 0) (F1 0)) 0 Nil)))))

caseList :: FinType0 -> PTM Prelude.Bool
caseList sigX =
  unsafeCoerce seq (Prelude.succ (Prelude.succ 0))
    (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX))))
    (finType_CS unit_eq_dec finTypeC_unit)
    (liftTapes
      (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ 0) (Prelude.succ
      (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit)
      (unsafeCoerce move
        (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
          (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) R) (Cons (F1 (Prelude.succ 0)) 0
      Nil)) (finType_CS bool_eq_dec finTypeC_bool)
    (switch (Prelude.succ (Prelude.succ 0))
      (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX))))
      (finType_CS
        (option_eq_dec
          (eqType_dec
            (type0
              (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
                (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))))))
        (finTypeC_Option
          (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
            (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX))))))
      (liftTapes
        (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
          (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ 0) (Prelude.succ
        (Prelude.succ 0))
        (finType_CS
          (option_eq_dec
            (eqType_dec
              (type0
                (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
                  (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))))))
          (finTypeC_Option
            (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
              (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX))))))
        (unsafeCoerce readChar
          (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
            (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX))))) (Cons (F1 (Prelude.succ 0)) 0
        Nil)) (finType_CS bool_eq_dec finTypeC_bool) (\s ->
      case unsafeCoerce s of {
       Prelude.Just e ->
        case e of {
         Inl _ ->
          return
            (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
              (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ (Prelude.succ
            0)) (finType_CS unit_eq_dec finTypeC_unit)
            (unsafeCoerce nop
              (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
                (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ (Prelude.succ
              0))) (finType_CS bool_eq_dec finTypeC_bool) (default0 (unsafeCoerce inhabited_bool));
         Inr y ->
          case y of {
           SigList_X _ ->
            return
              (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
                (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ (Prelude.succ
              0)) (finType_CS unit_eq_dec finTypeC_unit)
              (unsafeCoerce nop
                (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
                  (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ
                (Prelude.succ 0))) (finType_CS bool_eq_dec finTypeC_bool) (default0 (unsafeCoerce inhabited_bool));
           SigList_nil ->
            return
              (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
                (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ (Prelude.succ
              0)) (finType_CS unit_eq_dec finTypeC_unit)
              (liftTapes
                (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
                  (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ 0)
                (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit)
                (unsafeCoerce move
                  (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
                    (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) L) (Cons (F1
                (Prelude.succ 0)) 0 Nil)) (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.False);
           SigList_cons ->
            seq (Prelude.succ (Prelude.succ 0)) (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
              (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX))))
              (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce m1 sigX) (finType_CS bool_eq_dec finTypeC_bool)
              (seq (Prelude.succ (Prelude.succ 0)) (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
                (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX))))
                (finType_CS unit_eq_dec finTypeC_unit)
                (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
                  (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ 0)
                  (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce skip_cons sigX) (Cons (F1 (Prelude.succ 0)) 0 Nil))
                (finType_CS bool_eq_dec finTypeC_bool)
                (return
                  (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
                    (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ
                  (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit)
                  (liftTapes
                    (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
                      (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ 0)
                    (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit)
                    (seq (Prelude.succ 0)
                      (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
                        (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX))))
                      (finType_CS unit_eq_dec finTypeC_unit)
                      (unsafeCoerce move
                        (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
                          (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) L)
                      (finType_CS unit_eq_dec finTypeC_unit)
                      (unsafeCoerce write
                        (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
                          (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Inl START)))
                    (Cons (F1 (Prelude.succ 0)) 0 Nil)) (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.True)))}};
       Prelude.Nothing ->
        return
          (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
            (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ (Prelude.succ 0))
          (finType_CS unit_eq_dec finTypeC_unit)
          (unsafeCoerce nop
            (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
              (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ (Prelude.succ
            0))) (finType_CS bool_eq_dec finTypeC_bool) (default0 (unsafeCoerce inhabited_bool))}))

isNil :: FinType0 -> PTM Prelude.Bool
isNil sigX =
  unsafeCoerce seq (Prelude.succ 0)
    (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX))))
    (finType_CS unit_eq_dec finTypeC_unit)
    (move
      (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) R)
    (finType_CS bool_eq_dec finTypeC_bool)
    (switch (Prelude.succ 0)
      (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX))))
      (finType_CS
        (option_eq_dec
          (eqType_dec
            (type0
              (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
                (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))))))
        (finTypeC_Option
          (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
            (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX))))))
      (unsafeCoerce readChar
        (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
          (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))))
      (finType_CS bool_eq_dec finTypeC_bool) (\s ->
      case unsafeCoerce s of {
       Prelude.Just e ->
        case e of {
         Inl _ ->
          return
            (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
              (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ 0)
            (finType_CS unit_eq_dec finTypeC_unit)
            (unsafeCoerce move
              (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
                (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) L)
            (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.False);
         Inr y ->
          case y of {
           SigList_nil ->
            return
              (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
                (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ 0)
              (finType_CS unit_eq_dec finTypeC_unit)
              (unsafeCoerce move
                (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
                  (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) L)
              (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.True);
           _ ->
            return
              (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
                (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ 0)
              (finType_CS unit_eq_dec finTypeC_unit)
              (unsafeCoerce move
                (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
                  (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) L)
              (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.False)}};
       Prelude.Nothing ->
        return
          (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
            (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ 0)
          (finType_CS unit_eq_dec finTypeC_unit)
          (unsafeCoerce move
            (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
              (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) L)
          (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.False)}))

constr_nil :: FinType0 -> PTM Unit
constr_nil sigX =
  writeValue (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)) ((:) (unsafeCoerce SigList_nil) [])

constr_cons :: FinType0 -> PTM Unit
constr_cons sigX =
  unsafeCoerce seq (Prelude.succ (Prelude.succ 0)) (FinType
    (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (finType_CS unit_eq_dec finTypeC_unit)
    (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ 0) (Prelude.succ
      (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit)
      (seq (Prelude.succ 0) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX))))
        (finType_CS unit_eq_dec finTypeC_unit) (moveRight (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX))) (finType_CS unit_eq_dec finTypeC_unit)
        (unsafeCoerce move (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))))
          (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) L)) (Cons (FS (Prelude.succ 0)
      (F1 0)) 0 Nil)) (finType_CS unit_eq_dec finTypeC_unit)
    (seq (Prelude.succ (Prelude.succ 0)) (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX))))
      (finType_CS unit_eq_dec finTypeC_unit)
      (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ (Prelude.succ 0))
        (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit)
        (copySymbols_L (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
          (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (stop sigX)) (Cons (FS
        (Prelude.succ 0) (F1 0)) (Prelude.succ 0) (Cons (F1 (Prelude.succ 0)) 0 Nil))) (finType_CS unit_eq_dec finTypeC_unit)
      (liftTapes
        (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
          (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ 0) (Prelude.succ
        (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit)
        (seq (Prelude.succ 0)
          (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
            (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX))))
          (finType_CS unit_eq_dec finTypeC_unit)
          (unsafeCoerce writeMove
            (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
              (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Inr SigList_cons) L)
          (finType_CS unit_eq_dec finTypeC_unit)
          (unsafeCoerce write
            (finType_CS (sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigX))))
              (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Inl START))) (Cons (F1
        (Prelude.succ 0)) 0 Nil)))

nth'_Step :: FinType0 -> FinType0 -> (Retract (SigList EqType_X) EqType_X) -> (Retract SigNat EqType_X) -> SigT MTM (EqType_X -> Prelude.Maybe Prelude.Bool)
nth'_Step sig sigX retr1 retr2 =
  unsafeCoerce if0 (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig)))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig))
    (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ 0)
      (Prelude.succ (Prelude.succ (Prelude.succ 0))) (finType_CS bool_eq_dec finTypeC_bool)
      (changeAlphabet (finType_CS sigNat_eq sigNat_fin) sig (Prelude.succ 0) (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce caseNat) (unsafeCoerce retr2)) (Cons
      (FS (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0))) 0 Nil))
    (finType_CS (option_eq_dec bool_eq_dec) (finTypeC_Option (finType_CS bool_eq_dec finTypeC_bool)))
    (if0 (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig)))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig))
      (unsafeCoerce liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig))
        (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ 0))) (finType_CS bool_eq_dec finTypeC_bool)
        (changeAlphabet (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)) sig (Prelude.succ (Prelude.succ 0))
          (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce caseList sigX) (unsafeCoerce retr1)) (Cons (F1 (Prelude.succ (Prelude.succ 0))) (Prelude.succ 0) (Cons (FS
        (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0))) 0 Nil)))
      (finType_CS (option_eq_dec bool_eq_dec) (finTypeC_Option (finType_CS bool_eq_dec finTypeC_bool)))
      (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ
        (Prelude.succ (Prelude.succ 0))) (finType_CS unit_eq_dec finTypeC_unit)
        (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ 0)
          (Prelude.succ (Prelude.succ (Prelude.succ 0))) (finType_CS unit_eq_dec finTypeC_unit) (reset sig) (Cons (FS (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ
          0) (F1 0))) 0 Nil)) (finType_CS (option_eq_dec bool_eq_dec) (finTypeC_Option (finType_CS bool_eq_dec finTypeC_bool))) (unsafeCoerce Prelude.Nothing))
      (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ
        (Prelude.succ (Prelude.succ 0))) (finType_CS unit_eq_dec finTypeC_unit)
        (unsafeCoerce nop (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ
          (Prelude.succ (Prelude.succ 0)))) (finType_CS (option_eq_dec bool_eq_dec) (finTypeC_Option (finType_CS bool_eq_dec finTypeC_bool)))
        (unsafeCoerce (Prelude.Just Prelude.False))))
    (relabel (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ
      (Prelude.succ (Prelude.succ 0))) (finType_CS bool_eq_dec finTypeC_bool)
      (finType_CS (option_eq_dec bool_eq_dec) (finTypeC_Option (finType_CS bool_eq_dec finTypeC_bool)))
      (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ
        (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ 0))) (finType_CS bool_eq_dec finTypeC_bool)
        (changeAlphabet (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)) sig (Prelude.succ (Prelude.succ 0))
          (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce caseList sigX) (unsafeCoerce retr1)) (Cons (F1 (Prelude.succ (Prelude.succ 0))) (Prelude.succ 0) (Cons (FS
        (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0))) 0 Nil))) (unsafeCoerce (\x -> Prelude.Just x)))

nth'_Loop :: FinType0 -> FinType0 -> (Retract (SigList EqType_X) EqType_X) -> (Retract SigNat EqType_X) -> PTM EqType_X
nth'_Loop sig sigX retr1 retr2 =
  while (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig)))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce nth'_Step sig sigX retr1 retr2)
    (unsafeCoerce inhabited_bool)

nth' :: FinType0 -> FinType0 -> (Retract (SigList EqType_X) EqType_X) -> (Retract SigNat EqType_X) -> SigT MTM (EqType_X -> Prelude.Bool)
nth' sig sigX retr1 retr2 =
  unsafeCoerce seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig)))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (finType_CS unit_eq_dec finTypeC_unit)
    (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ
      (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (finType_CS unit_eq_dec finTypeC_unit) (copyValue sig) (Cons (F1 (Prelude.succ
      (Prelude.succ (Prelude.succ 0)))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ
      0) (F1 0)))) 0 Nil))) (finType_CS bool_eq_dec finTypeC_bool)
    (if0 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig)))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig))
      (unsafeCoerce liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig))
        (Prelude.succ (Prelude.succ (Prelude.succ 0))) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (finType_CS bool_eq_dec finTypeC_bool)
        (nth'_Loop sig sigX retr1 retr2) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0))))
        (Prelude.succ (Prelude.succ 0)) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (F1 (Prelude.succ (Prelude.succ 0)))) (Prelude.succ 0) (Cons (FS
        (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0)))) 0 Nil)))) (finType_CS bool_eq_dec finTypeC_bool)
      (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (finType_CS unit_eq_dec finTypeC_unit)
        (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig)))
          (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (finType_CS unit_eq_dec finTypeC_unit)
          (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ 0)
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (finType_CS unit_eq_dec finTypeC_unit) (reset sig) (Cons (FS (Prelude.succ (Prelude.succ
            (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0)))) 0 Nil)) (finType_CS unit_eq_dec finTypeC_unit)
          (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ 0)
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (finType_CS unit_eq_dec finTypeC_unit) (reset sig) (Cons (FS (Prelude.succ (Prelude.succ
            (Prelude.succ 0))) (F1 (Prelude.succ (Prelude.succ 0)))) 0 Nil))) (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.True))
      (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (finType_CS unit_eq_dec finTypeC_unit)
        (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig)))
          (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (finType_CS unit_eq_dec finTypeC_unit)
          (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ 0)
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (finType_CS unit_eq_dec finTypeC_unit) (reset sig) (Cons (FS (Prelude.succ (Prelude.succ
            (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0)))) 0 Nil)) (finType_CS unit_eq_dec finTypeC_unit)
          (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ 0)
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (finType_CS unit_eq_dec finTypeC_unit) (reset sig) (Cons (FS (Prelude.succ (Prelude.succ
            (Prelude.succ 0))) (F1 (Prelude.succ (Prelude.succ 0)))) 0 Nil))) (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.False)))

app' :: FinType0 -> SigT MTM (EqType_X -> Unit)
app' sigX =
  let {stop0 = \x -> case x of {
                      Inl b -> case b of {
                                START -> Prelude.True;
                                _ -> Prelude.False};
                      Inr _ -> Prelude.False}} in
  unsafeCoerce seq (Prelude.succ (Prelude.succ 0)) (FinType
    (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 (FinType (unsafeCoerce sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin) (FinType (unsafeCoerce sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX))))
    (finType_CS unit_eq_dec finTypeC_unit)
    (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 (FinType (unsafeCoerce sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) (FinType (unsafeCoerce sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (Prelude.succ 0)
      (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit)
      (seq (Prelude.succ 0) (FinType
        (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 (FinType (unsafeCoerce sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) (FinType (unsafeCoerce sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX))))
        (finType_CS unit_eq_dec finTypeC_unit) (moveRight (FinType (unsafeCoerce sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))
        (finType_CS unit_eq_dec finTypeC_unit)
        (seq (Prelude.succ 0) (FinType
          (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 (FinType (unsafeCoerce sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))))
          (finTypeC_sum (finType_CS boundary_eq boundary_fin) (FinType (unsafeCoerce sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX))))
          (finType_CS unit_eq_dec finTypeC_unit)
          (unsafeCoerce move (FinType
            (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 (FinType (unsafeCoerce sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))))
            (finTypeC_sum (finType_CS boundary_eq boundary_fin) (FinType (unsafeCoerce sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) L)
          (finType_CS unit_eq_dec finTypeC_unit)
          (unsafeCoerce move (FinType
            (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 (FinType (unsafeCoerce sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))))
            (finTypeC_sum (finType_CS boundary_eq boundary_fin) (FinType (unsafeCoerce sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) L))) (Cons (F1
      (Prelude.succ 0)) 0 Nil)) (finType_CS unit_eq_dec finTypeC_unit)
    (copySymbols_L (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 (FinType (unsafeCoerce sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) (FinType (unsafeCoerce sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)))) (unsafeCoerce stop0))

length_Step :: FinType0 -> FinType0 -> (Retract (SigList EqType_X) EqType_X) -> (Retract SigNat EqType_X) -> PTM (Prelude.Maybe Unit)
length_Step sig sigX retr1 retr2 =
  unsafeCoerce if0 (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig)))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig))
    (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ
      (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ 0))) (finType_CS bool_eq_dec finTypeC_bool)
      (changeAlphabet (finType_CS (sigList_dec (eqType_dec (type0 sigX))) (sigList_fin sigX)) sig (Prelude.succ (Prelude.succ 0)) (finType_CS bool_eq_dec finTypeC_bool)
        (unsafeCoerce caseList sigX) (unsafeCoerce retr1)) (Cons (F1 (Prelude.succ (Prelude.succ 0))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ 0)) (FS
      (Prelude.succ 0) (F1 0))) 0 Nil))) (finType_CS (option_eq_dec unit_eq_dec) (finTypeC_Option (finType_CS unit_eq_dec finTypeC_unit)))
    (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ (Prelude.succ
      (Prelude.succ 0))) (finType_CS unit_eq_dec finTypeC_unit)
      (seq (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig)))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (finType_CS unit_eq_dec finTypeC_unit)
        (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ 0)
          (Prelude.succ (Prelude.succ (Prelude.succ 0))) (finType_CS unit_eq_dec finTypeC_unit) (reset sig) (Cons (FS (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ
          0) (F1 0))) 0 Nil)) (finType_CS unit_eq_dec finTypeC_unit)
        (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ 0)
          (Prelude.succ (Prelude.succ (Prelude.succ 0))) (finType_CS unit_eq_dec finTypeC_unit)
          (changeAlphabet (finType_CS sigNat_eq sigNat_fin) sig (Prelude.succ 0) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce constr_S) (unsafeCoerce retr2))
          (Cons (FS (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0))) 0 Nil)))
      (finType_CS (option_eq_dec unit_eq_dec) (finTypeC_Option (finType_CS unit_eq_dec finTypeC_unit))) (unsafeCoerce Prelude.Nothing))
    (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ (Prelude.succ
      (Prelude.succ 0))) (finType_CS unit_eq_dec finTypeC_unit)
      (unsafeCoerce nop (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ
        (Prelude.succ (Prelude.succ 0)))) (finType_CS (option_eq_dec unit_eq_dec) (finTypeC_Option (finType_CS unit_eq_dec finTypeC_unit)))
      (unsafeCoerce (Prelude.Just Tt)))

length_Loop :: FinType0 -> FinType0 -> (Retract (SigList EqType_X) EqType_X) -> (Retract SigNat EqType_X) -> PTM EqType_X
length_Loop sig sigX retr1 retr2 =
  while (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig)))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce length_Step sig sigX retr1 retr2)
    (unsafeCoerce inhabited_unit)

length0 :: FinType0 -> FinType0 -> (Retract (SigList EqType_X) EqType_X) -> (Retract SigNat EqType_X) -> PTM Unit
length0 sig sigX retr1 retr2 =
  unsafeCoerce seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig)))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (finType_CS unit_eq_dec finTypeC_unit)
    (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ
      (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (finType_CS unit_eq_dec finTypeC_unit) (copyValue sig) (Cons (F1 (Prelude.succ
      (Prelude.succ (Prelude.succ 0)))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ
      0) (F1 0)))) 0 Nil))) (FinType (unsafeCoerce unit_eq_dec) finTypeC_unit)
    (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig)))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (finType_CS unit_eq_dec finTypeC_unit)
      (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ 0)
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (finType_CS unit_eq_dec finTypeC_unit)
        (changeAlphabet (finType_CS sigNat_eq sigNat_fin) sig (Prelude.succ 0) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce constr_O) (unsafeCoerce retr2)) (Cons
        (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (F1 (Prelude.succ (Prelude.succ 0)))) 0 Nil)) (FinType (unsafeCoerce unit_eq_dec) finTypeC_unit)
      (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig)))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (finType_CS unit_eq_dec finTypeC_unit)
        (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ
          (Prelude.succ (Prelude.succ 0))) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (finType_CS unit_eq_dec finTypeC_unit)
          (length_Loop sig sigX retr1 retr2) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0))))
          (Prelude.succ (Prelude.succ 0)) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (F1 (Prelude.succ (Prelude.succ 0)))) (Prelude.succ 0) (Cons (FS
          (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0)))) 0 Nil)))) (FinType (unsafeCoerce unit_eq_dec)
        finTypeC_unit)
        (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sig))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sig)) (Prelude.succ 0)
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FinType (unsafeCoerce unit_eq_dec) finTypeC_unit) (resetEmpty1 sig) (Cons (FS (Prelude.succ
          (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0)))) 0 Nil))))

stopAfterFirst :: FinType0 -> FinType0 -> EqType_X -> Prelude.Bool
stopAfterFirst _ _ x =
  case unsafeCoerce x of {
   Inl b -> case b of {
             STOP -> Prelude.True;
             _ -> Prelude.False};
   Inr s -> case s of {
             SigPair_X _ -> Prelude.False;
             SigPair_Y _ -> Prelude.True}}

stopAtStart :: FinType0 -> FinType0 -> EqType_X -> Prelude.Bool
stopAtStart _ _ x =
  case unsafeCoerce x of {
   Inl b -> case b of {
             START -> Prelude.True;
             _ -> Prelude.False};
   Inr _ -> Prelude.False}

casePair :: FinType0 -> FinType0 -> PTM Unit
casePair sigX sigY =
  unsafeCoerce seq (Prelude.succ (Prelude.succ 0))
    (finType_CS (sum_eq_dec boundary_eq (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY))))
    (finType_CS unit_eq_dec finTypeC_unit)
    (liftTapes
      (finType_CS (sum_eq_dec boundary_eq (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY))))
      (Prelude.succ 0) (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit)
      (unsafeCoerce writeMove
        (finType_CS (sum_eq_dec boundary_eq (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
          (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY))))
        (Inl STOP) L) (Cons (FS (Prelude.succ 0) (F1 0)) 0 Nil)) (finType_CS unit_eq_dec finTypeC_unit)
    (seq (Prelude.succ (Prelude.succ 0)) (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY))))
      (finType_CS unit_eq_dec finTypeC_unit)
      (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY))))
        (Prelude.succ 0) (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit)
        (seq (Prelude.succ 0) (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
          (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY))))
          (finType_CS unit_eq_dec finTypeC_unit)
          (unsafeCoerce moveToSymbol (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
            (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY))))
            (stopAfterFirst sigX sigY) id) (finType_CS unit_eq_dec finTypeC_unit)
          (unsafeCoerce move (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
            (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY))))
            L)) (Cons (F1 (Prelude.succ 0)) 0 Nil)) (finType_CS unit_eq_dec finTypeC_unit)
      (seq (Prelude.succ (Prelude.succ 0)) (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY))))
        (finType_CS unit_eq_dec finTypeC_unit)
        (copySymbols_L (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
          (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY))))
          (stopAtStart sigX sigY)) (finType_CS unit_eq_dec finTypeC_unit)
        (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
          (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY))))
          (Prelude.succ 0) (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit)
          (seq (Prelude.succ 0) (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
            (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY))))
            (finType_CS unit_eq_dec finTypeC_unit)
            (unsafeCoerce moveToSymbol (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
              (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY))))
              (stopAfterFirst sigX sigY) id) (finType_CS unit_eq_dec finTypeC_unit)
            (seq (Prelude.succ 0)
              (finType_CS (sum_eq_dec boundary_eq (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
                (finTypeC_sum (finType_CS boundary_eq boundary_fin)
                  (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY)))) (finType_CS unit_eq_dec finTypeC_unit)
              (unsafeCoerce move
                (finType_CS (sum_eq_dec boundary_eq (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
                  (finTypeC_sum (finType_CS boundary_eq boundary_fin)
                    (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY)))) L) (finType_CS unit_eq_dec finTypeC_unit)
              (unsafeCoerce write
                (finType_CS (sum_eq_dec boundary_eq (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
                  (finTypeC_sum (finType_CS boundary_eq boundary_fin)
                    (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY)))) (Inl START)))) (Cons (F1 (Prelude.succ 0)) 0
          Nil))))

constr_pair :: FinType0 -> FinType0 -> PTM Unit
constr_pair sigX sigY =
  unsafeCoerce seq (Prelude.succ (Prelude.succ 0)) (FinType
    (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY)))))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY))))
    (finType_CS unit_eq_dec finTypeC_unit)
    (liftTapes (FinType
      (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY)))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY))))
      (Prelude.succ 0) (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit)
      (seq (Prelude.succ 0) (FinType
        (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY)))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY))))
        (finType_CS unit_eq_dec finTypeC_unit) (moveRight (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY)))
        (finType_CS unit_eq_dec finTypeC_unit)
        (unsafeCoerce move (FinType
          (unsafeCoerce sum_eq_dec boundary_eq
            (eqType_dec (type0 (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY)))))
          (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY)))) L))
      (Cons (F1 (Prelude.succ 0)) 0 Nil)) (finType_CS unit_eq_dec finTypeC_unit)
    (copySymbols_L (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigPair_dec (eqType_dec (type0 sigX)) (eqType_dec (type0 sigY))) (sigPair_fin sigX sigY))))
      (stopAtStart sigX sigY))

retr_nat_clos_ad :: Retract SigNat SigHClos
retr_nat_clos_ad =
  retract_sigPair_X retract_id

retr_nat_lookup_clos_ad :: FinType0 -> (Retract SigHClos EqType_X) -> Retract SigNat EqType_X
retr_nat_lookup_clos_ad _ retr_clos_lookup =
  composeRetract retr_clos_lookup retr_nat_clos_ad

retr_nat_clos_var :: Retract SigNat SigHClos
retr_nat_clos_var =
  retract_sigPair_Y (retract_sigList_X (retract_sigSum_X retract_id))

retr_nat_lookup_clos_var :: FinType0 -> (Retract SigHClos EqType_X) -> Retract SigNat EqType_X
retr_nat_lookup_clos_var _ retr_clos_lookup =
  composeRetract retr_clos_lookup retr_nat_clos_var

retr_nat_heap_entry :: Retract SigNat SigHeap
retr_nat_heap_entry =
  retract_sigList_X (retract_sigOption_X (retract_sigPair_Y retract_id))

retr_nat_lookup_entry :: FinType0 -> (Retract SigHeap EqType_X) -> Retract SigNat EqType_X
retr_nat_lookup_entry _ retr_heap_lookup =
  composeRetract retr_heap_lookup retr_nat_heap_entry

retr_clos_heap :: Retract SigHClos SigHeap
retr_clos_heap =
  retract_sigList_X (retract_sigOption_X (retract_sigPair_X retract_id))

retr_clos_lookup_heap :: FinType0 -> (Retract SigHeap EqType_X) -> Retract SigHClos EqType_X
retr_clos_lookup_heap _ retr_heap_lookup =
  composeRetract retr_heap_lookup retr_clos_heap

retr_hent_heap :: Retract SigHEntr SigHeap
retr_hent_heap =
  retract_sigList_X retract_id

retr_hent_lookup :: FinType0 -> (Retract SigHeap EqType_X) -> Retract SigHEntr EqType_X
retr_hent_lookup _ retr_heap_lookup =
  composeRetract retr_heap_lookup retr_hent_heap

retr_hent'_heap :: Retract SigHEntr' SigHeap
retr_hent'_heap =
  retract_sigList_X (retract_sigOption_X retract_id)

retr_hent'_lookup :: FinType0 -> (Retract SigHeap EqType_X) -> Retract SigHEntr' EqType_X
retr_hent'_lookup _ retr_heap_lookup =
  composeRetract retr_heap_lookup retr_hent'_heap

lookup_Step :: FinType0 -> (Retract SigHClos EqType_X) -> (Retract SigHeap EqType_X) -> PTM (Prelude.Maybe Prelude.Bool)
lookup_Step sigLookup retr_clos_lookup retr_heap_lookup =
  unsafeCoerce if0 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FinType
    (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup))
    (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup))
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))
      (finType_CS bool_eq_dec finTypeC_bool)
      (unsafeCoerce nth' sigLookup
        (finType_CS (sigOption_dec (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq))
          (sigOption_fin
            (finType_CS (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq)
              (sigPair_fin
                (finType_CS (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
                  (sigPair_fin (finType_CS sigNat_eq sigNat_fin)
                    (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                      (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
                (finType_CS sigNat_eq sigNat_fin))))) retr_heap_lookup (retr_nat_lookup_clos_ad sigLookup retr_clos_lookup)) (Cons (F1 (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ 0))))) (Prelude.succ (Prelude.succ (Prelude.succ 0))) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (F1
      (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (Prelude.succ (Prelude.succ 0)) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS
      (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0))))) (Prelude.succ 0) (Cons (FS (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0))))) 0
      Nil))))) (finType_CS (option_eq_dec bool_eq_dec) (finTypeC_Option (finType_CS bool_eq_dec finTypeC_bool)))
    (if0 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup)))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup))
      (unsafeCoerce liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup)))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup)) (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))
        (finType_CS bool_eq_dec finTypeC_bool)
        (changeAlphabet (finType_CS (sigOption_dec (eqType_dec (type0 sigHEntr'_fin))) (sigOption_fin sigHEntr'_fin)) sigLookup (Prelude.succ 0)
          (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce caseOption sigHEntr'_fin) (unsafeCoerce retr_hent_lookup sigLookup retr_heap_lookup)) (Cons (FS
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (FS
        (Prelude.succ 0) (F1 0))))) 0 Nil)) (finType_CS (option_eq_dec bool_eq_dec) (finTypeC_Option (finType_CS bool_eq_dec finTypeC_bool)))
      (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup)))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup)) (finType_CS unit_eq_dec finTypeC_unit)
        (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup))
          (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit)
          (changeAlphabet (finType_CS (sigPair_dec (eqType_dec (type0 sigHClos_fin)) (eqType_dec (type0 sigHAdd_fin))) (sigPair_fin sigHClos_fin sigHAdd_fin)) sigLookup
            (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce casePair sigHClos_fin sigHAdd_fin)
            (unsafeCoerce retr_hent'_lookup sigLookup retr_heap_lookup)) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ
          (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0))))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0))))) 0 Nil)))
        (finType_CS (option_eq_dec bool_eq_dec) (finTypeC_Option (finType_CS bool_eq_dec finTypeC_bool)))
        (if0 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup)))
          (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup))
          (unsafeCoerce liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup)))
            (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup)) (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))
            (finType_CS bool_eq_dec finTypeC_bool)
            (changeAlphabet (finType_CS sigNat_eq sigNat_fin) sigLookup (Prelude.succ 0) (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce caseNat)
              (unsafeCoerce retr_nat_lookup_clos_var sigLookup retr_clos_lookup)) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS
            (Prelude.succ (Prelude.succ (Prelude.succ 0))) (F1 (Prelude.succ (Prelude.succ 0))))) 0 Nil))
          (finType_CS (option_eq_dec bool_eq_dec) (finTypeC_Option (finType_CS bool_eq_dec finTypeC_bool)))
          (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup))
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit)
            (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FinType
              (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup))
              (finType_CS unit_eq_dec finTypeC_unit)
              (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup))
                (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit)
                (copyValue sigLookup) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS
                (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0))))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))
                (F1 (Prelude.succ (Prelude.succ (Prelude.succ 0))))) 0 Nil))) (finType_CS unit_eq_dec finTypeC_unit)
              (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FinType
                (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup))
                (finType_CS unit_eq_dec finTypeC_unit)
                (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup))
                  (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit)
                  (translate0 sigLookup (finType_CS sigNat_eq sigNat_fin) (unsafeCoerce retr_nat_lookup_entry sigLookup retr_heap_lookup)
                    (unsafeCoerce retr_nat_lookup_clos_ad sigLookup retr_clos_lookup)) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (F1
                  (Prelude.succ (Prelude.succ (Prelude.succ 0))))) 0 Nil)) (finType_CS unit_eq_dec finTypeC_unit)
                (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FinType
                  (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup))
                  (finType_CS unit_eq_dec finTypeC_unit)
                  (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup)))
                    (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup)) (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                    (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit) (reset sigLookup) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))
                    (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0))))) 0 Nil))
                  (finType_CS unit_eq_dec finTypeC_unit)
                  (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup)))
                    (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup)) (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                    (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit) (reset sigLookup) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))
                    (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0))))) 0 Nil)))))
            (finType_CS (option_eq_dec bool_eq_dec) (finTypeC_Option (finType_CS bool_eq_dec finTypeC_bool))) (unsafeCoerce Prelude.Nothing))
          (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup))
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit)
            (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FinType
              (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup))
              (finType_CS unit_eq_dec finTypeC_unit)
              (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup))
                (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit) (reset sigLookup)
                (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ
                (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0))))) 0 Nil)) (finType_CS unit_eq_dec finTypeC_unit)
              (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FinType
                (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup))
                (finType_CS unit_eq_dec finTypeC_unit)
                (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup))
                  (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit) (reset sigLookup)
                  (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (F1 (Prelude.succ
                  (Prelude.succ 0))))) 0 Nil)) (finType_CS unit_eq_dec finTypeC_unit)
                (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup))
                  (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit)
                  (translate0 sigLookup
                    (finType_CS (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
                      (sigPair_fin (finType_CS sigNat_eq sigNat_fin)
                        (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                          (sigList_fin
                            (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
                    (unsafeCoerce retr_clos_lookup_heap sigLookup retr_heap_lookup) (unsafeCoerce retr_clos_lookup)) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0))))) 0 Nil))))
            (finType_CS (option_eq_dec bool_eq_dec) (finTypeC_Option (finType_CS bool_eq_dec finTypeC_bool))) (unsafeCoerce (Prelude.Just Prelude.True)))))
      (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup)) (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit)
        (unsafeCoerce nop (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup))
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))
        (finType_CS (option_eq_dec bool_eq_dec) (finTypeC_Option (finType_CS bool_eq_dec finTypeC_bool))) (unsafeCoerce (Prelude.Just Prelude.False))))
    (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup)) (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit)
      (unsafeCoerce nop (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup))
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))
      (finType_CS (option_eq_dec bool_eq_dec) (finTypeC_Option (finType_CS bool_eq_dec finTypeC_bool))) (unsafeCoerce (Prelude.Just Prelude.False)))

lookup :: FinType0 -> (Retract SigHClos EqType_X) -> (Retract SigHeap EqType_X) -> PTM EqType_X
lookup sigLookup retr_clos_lookup retr_heap_lookup =
  while (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigLookup)))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigLookup)) (finType_CS bool_eq_dec finTypeC_bool)
    (unsafeCoerce lookup_Step sigLookup retr_clos_lookup retr_heap_lookup) (unsafeCoerce inhabited_bool)

retr_nat_prog :: Retract SigNat SigPro
retr_nat_prog =
  retract_sigList_X (retract_sigSum_X retract_id)

app_Comens :: PTM EqType_X
app_Comens =
  seq (Prelude.succ (Prelude.succ 0)) (FinType
    (unsafeCoerce sum_eq_dec boundary_eq
      (eqType_dec
        (type0 (FinType
          (unsafeCoerce sigList_dec
            (eqType_dec (type0 (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))
          (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin) (FinType
      (unsafeCoerce sigList_dec
        (eqType_dec (type0 (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))
      (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
    (finType_CS unit_eq_dec finTypeC_unit)
    (liftTapes (FinType
      (unsafeCoerce sum_eq_dec boundary_eq
        (eqType_dec
          (type0 (FinType
            (unsafeCoerce sigList_dec
              (eqType_dec (type0 (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))
            (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) (FinType
        (unsafeCoerce sigList_dec
          (eqType_dec (type0 (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))
        (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
      (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit)
      (unsafeCoerce app' (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))) (Cons (F1
      (Prelude.succ 0)) (Prelude.succ 0) (Cons (FS (Prelude.succ 0) (F1 0)) 0 Nil))) (finType_CS unit_eq_dec finTypeC_unit)
    (liftTapes (FinType
      (unsafeCoerce sum_eq_dec boundary_eq
        (eqType_dec
          (type0 (FinType
            (unsafeCoerce sigList_dec
              (eqType_dec (type0 (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))
            (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) (FinType
        (unsafeCoerce sigList_dec
          (eqType_dec (type0 (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))
        (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
      (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit)
      (unsafeCoerce moveValue (FinType
        (unsafeCoerce sigList_dec
          (eqType_dec (type0 (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))
        (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))) (Cons (FS
      (Prelude.succ 0) (F1 0)) (Prelude.succ 0) (Cons (F1 (Prelude.succ 0)) 0 Nil)))

app_ACom :: ACom -> PTM Unit
app_ACom t =
  unsafeCoerce seq (Prelude.succ (Prelude.succ 0)) (FinType
    (unsafeCoerce sum_eq_dec boundary_eq
      (eqType_dec
        (type0
          (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
            (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin)
      (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
        (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
    (finType_CS unit_eq_dec finTypeC_unit)
    (liftTapes (FinType
      (unsafeCoerce sum_eq_dec boundary_eq
        (eqType_dec
          (type0
            (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
              (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin)
        (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
          (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
      (Prelude.succ 0) (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit)
      (unsafeCoerce writeValue
        (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
          (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))
        (encode (unsafeCoerce encode_Prog) ((:) (aCom2Com t) []))) (Cons (FS (Prelude.succ 0) (F1 0)) 0 Nil)) (FinType (unsafeCoerce unit_eq_dec) finTypeC_unit)
    app_Comens

app_Com :: PTM EqType_X
app_Com =
  seq (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FinType
    (unsafeCoerce sum_eq_dec boundary_eq
      (sigList_dec
        (eqType_dec (type0 (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin)
      (finType_CS
        (sigList_dec
          (eqType_dec (type0 (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))
        (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
    (finType_CS unit_eq_dec finTypeC_unit)
    (liftTapes (FinType
      (unsafeCoerce sum_eq_dec boundary_eq
        (sigList_dec
          (eqType_dec (type0 (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin)
        (finType_CS
          (sigList_dec
            (eqType_dec (type0 (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))
          (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
      (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ 0))) (finType_CS unit_eq_dec finTypeC_unit)
      (unsafeCoerce constr_nil (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))
      (Cons (FS (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0))) 0 Nil)) (finType_CS unit_eq_dec finTypeC_unit)
    (seq (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FinType
      (unsafeCoerce sum_eq_dec boundary_eq
        (sigList_dec
          (eqType_dec (type0 (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin)
        (finType_CS
          (sigList_dec
            (eqType_dec (type0 (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))
          (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
      (finType_CS unit_eq_dec finTypeC_unit)
      (liftTapes (FinType
        (unsafeCoerce sum_eq_dec boundary_eq
          (sigList_dec
            (eqType_dec (type0 (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin)
          (finType_CS
            (sigList_dec
              (eqType_dec (type0 (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))
            (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
        (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ 0))) (finType_CS unit_eq_dec finTypeC_unit)
        (unsafeCoerce constr_cons (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))
        (Cons (FS (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0))) 0
        Nil))) (finType_CS unit_eq_dec finTypeC_unit)
      (seq (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin)
          (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
            (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
        (FinType (unsafeCoerce unit_eq_dec) finTypeC_unit)
        (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
          (finTypeC_sum (finType_CS boundary_eq boundary_fin)
            (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
              (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
          (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FinType (unsafeCoerce unit_eq_dec) finTypeC_unit) app_Comens (Cons (F1
          (Prelude.succ (Prelude.succ 0))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0))) 0 Nil)))
        (finType_CS unit_eq_dec finTypeC_unit)
        (liftTapes (FinType
          (unsafeCoerce sum_eq_dec boundary_eq
            (eqType_dec
              (type0
                (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                  (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))))
          (finTypeC_sum (finType_CS boundary_eq boundary_fin)
            (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
              (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
          (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ 0))) (finType_CS unit_eq_dec finTypeC_unit)
          (reset
            (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
              (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))) (Cons
          (FS (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0))) 0 Nil))))

jumpTarget_Step :: PTM (Prelude.Maybe Prelude.Bool)
jumpTarget_Step =
  unsafeCoerce if0 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FinType
    (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigCom_fin))))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigCom_fin))) (sigList_fin sigCom_fin))))
    (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigCom_fin))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigCom_fin))) (sigList_fin sigCom_fin)))) (Prelude.succ
      (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS bool_eq_dec finTypeC_bool)
      (unsafeCoerce caseList sigCom_fin) (Cons (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0))))) 0 Nil)))
    (finType_CS (option_eq_dec bool_eq_dec) (finTypeC_Option (finType_CS bool_eq_dec finTypeC_bool)))
    (switch (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FinType
      (unsafeCoerce sum_eq_dec boundary_eq
        (eqType_dec
          (type0
            (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
              (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin)
        (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
          (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
      (finType_CS (option_eq_dec aCom_eq_dec) (finTypeC_Option (finType_CS aCom_eq_dec aCom_finType)))
      (liftTapes (FinType
        (unsafeCoerce sum_eq_dec boundary_eq
          (eqType_dec
            (type0
              (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin)
          (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
            (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
        (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))
        (finType_CS (option_eq_dec aCom_eq_dec) (finTypeC_Option (finType_CS aCom_eq_dec aCom_finType)))
        (changeAlphabet (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))
          (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
            (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))
          (Prelude.succ 0) (finType_CS (option_eq_dec aCom_eq_dec) (finTypeC_Option (finType_CS aCom_eq_dec aCom_finType))) (unsafeCoerce caseCom)
          (unsafeCoerce retract_sigList_X retract_id)) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ
        (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0))))) 0 Nil))
      (finType_CS (option_eq_dec bool_eq_dec) (finTypeC_Option (finType_CS bool_eq_dec finTypeC_bool))) (\t ->
      case unsafeCoerce t of {
       Prelude.Just a ->
        case a of {
         RetAT ->
          if0 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FinType
            (unsafeCoerce sum_eq_dec boundary_eq
              (eqType_dec
                (type0
                  (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                    (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))))
            (finTypeC_sum (finType_CS boundary_eq boundary_fin)
              (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
            (unsafeCoerce liftTapes (FinType
              (unsafeCoerce sum_eq_dec boundary_eq
                (eqType_dec
                  (type0
                    (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                      (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))))
              (finTypeC_sum (finType_CS boundary_eq boundary_fin)
                (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                  (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
              (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS bool_eq_dec finTypeC_bool)
              (changeAlphabet (finType_CS sigNat_eq sigNat_fin)
                (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                  (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))
                (Prelude.succ 0) (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce caseNat) (unsafeCoerce retr_nat_prog)) (Cons (FS (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (F1 (Prelude.succ (Prelude.succ 0))))) 0 Nil))
            (finType_CS (option_eq_dec bool_eq_dec) (finTypeC_Option (finType_CS bool_eq_dec finTypeC_bool)))
            (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
              (finTypeC_sum (finType_CS boundary_eq boundary_fin)
                (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                  (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit)
              (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
                (finTypeC_sum (finType_CS boundary_eq boundary_fin)
                  (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                    (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
                (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit)
                (unsafeCoerce app_ACom RetAT) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ
                0))))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS
                (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0))))) 0 Nil)))
              (finType_CS (option_eq_dec bool_eq_dec) (finTypeC_Option (finType_CS bool_eq_dec finTypeC_bool))) (unsafeCoerce Prelude.Nothing))
            (return (FinType
              (unsafeCoerce sum_eq_dec boundary_eq
                (eqType_dec
                  (type0
                    (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                      (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))))
              (finTypeC_sum (finType_CS boundary_eq boundary_fin)
                (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                  (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FinType (unsafeCoerce unit_eq_dec) finTypeC_unit)
              (liftTapes (FinType
                (unsafeCoerce sum_eq_dec boundary_eq
                  (eqType_dec
                    (type0
                      (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                        (sigList_fin
                          (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))))
                (finTypeC_sum (finType_CS boundary_eq boundary_fin)
                  (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                    (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
                (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FinType (unsafeCoerce unit_eq_dec) finTypeC_unit)
                (resetEmpty1
                  (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                    (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))
                (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (F1 (Prelude.succ
                (Prelude.succ 0))))) 0 Nil)) (finType_CS (option_eq_dec bool_eq_dec) (finTypeC_Option (finType_CS bool_eq_dec finTypeC_bool)))
              (unsafeCoerce (Prelude.Just Prelude.True)));
         LamAT ->
          return (FinType
            (unsafeCoerce sum_eq_dec boundary_eq
              (eqType_dec
                (type0
                  (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                    (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))))
            (finTypeC_sum (finType_CS boundary_eq boundary_fin)
              (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit)
            (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FinType
              (unsafeCoerce sum_eq_dec boundary_eq
                (eqType_dec
                  (type0
                    (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                      (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))))
              (finTypeC_sum (finType_CS boundary_eq boundary_fin)
                (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                  (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
              (finType_CS unit_eq_dec finTypeC_unit)
              (liftTapes (FinType
                (unsafeCoerce sum_eq_dec boundary_eq
                  (eqType_dec
                    (type0
                      (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                        (sigList_fin
                          (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))))
                (finTypeC_sum (finType_CS boundary_eq boundary_fin)
                  (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                    (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
                (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit)
                (changeAlphabet (finType_CS sigNat_eq sigNat_fin)
                  (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                    (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))
                  (Prelude.succ 0) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce constr_S) (unsafeCoerce retr_nat_prog)) (Cons (FS (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (F1 (Prelude.succ (Prelude.succ 0))))) 0 Nil))
              (finType_CS unit_eq_dec finTypeC_unit)
              (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
                (finTypeC_sum (finType_CS boundary_eq boundary_fin)
                  (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                    (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
                (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit)
                (unsafeCoerce app_ACom LamAT) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ
                0))))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS
                (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0))))) 0 Nil))))
            (finType_CS (option_eq_dec bool_eq_dec) (finTypeC_Option (finType_CS bool_eq_dec finTypeC_bool))) (unsafeCoerce Prelude.Nothing);
         AppAT ->
          return (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
            (finTypeC_sum (finType_CS boundary_eq boundary_fin)
              (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit)
            (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
              (finTypeC_sum (finType_CS boundary_eq boundary_fin)
                (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                  (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
              (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit)
              (unsafeCoerce app_ACom AppAT) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ 0)))))
              (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS
              (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0))))) 0 Nil)))
            (finType_CS (option_eq_dec bool_eq_dec) (finTypeC_Option (finType_CS bool_eq_dec finTypeC_bool))) (unsafeCoerce Prelude.Nothing)};
       Prelude.Nothing ->
        return (FinType
          (unsafeCoerce sum_eq_dec boundary_eq
            (eqType_dec
              (type0
                (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                  (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))))
          (finTypeC_sum (finType_CS boundary_eq boundary_fin)
            (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
              (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FinType (unsafeCoerce unit_eq_dec) finTypeC_unit)
          (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FinType
            (unsafeCoerce sum_eq_dec boundary_eq
              (eqType_dec
                (type0
                  (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                    (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))))
            (finTypeC_sum (finType_CS boundary_eq boundary_fin)
              (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
            (finType_CS unit_eq_dec finTypeC_unit)
            (liftTapes (FinType
              (unsafeCoerce sum_eq_dec boundary_eq
                (eqType_dec
                  (type0
                    (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                      (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))))
              (finTypeC_sum (finType_CS boundary_eq boundary_fin)
                (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                  (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
              (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit)
              (changeAlphabet (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))
                (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                  (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))
                (Prelude.succ 0) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce constr_varT) (unsafeCoerce retract_sigList_X retract_id)) (Cons (FS (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ
              0))))) 0 Nil)) (FinType (unsafeCoerce unit_eq_dec) finTypeC_unit)
            (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
              (finTypeC_sum (finType_CS boundary_eq boundary_fin)
                (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                  (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
              (Prelude.succ (Prelude.succ (Prelude.succ 0))) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FinType
              (unsafeCoerce unit_eq_dec) finTypeC_unit) app_Com (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (F1 (Prelude.succ (Prelude.succ
              (Prelude.succ 0))))) (Prelude.succ (Prelude.succ 0)) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ
              (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0))))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0))))) 0
              Nil))))) (finType_CS (option_eq_dec bool_eq_dec) (finTypeC_Option (finType_CS bool_eq_dec finTypeC_bool))) (unsafeCoerce Prelude.Nothing)}))
    (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigCom_fin))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigCom_fin))) (sigList_fin sigCom_fin)))) (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit)
      (unsafeCoerce nop (FinType (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (eqType_dec (type0 sigCom_fin))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) (finType_CS (sigList_dec (eqType_dec (type0 sigCom_fin))) (sigList_fin sigCom_fin)))) (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (finType_CS (option_eq_dec bool_eq_dec) (finTypeC_Option (finType_CS bool_eq_dec finTypeC_bool)))
      (unsafeCoerce (Prelude.Just Prelude.False)))

jumpTarget_Loop :: PTM EqType_X
jumpTarget_Loop =
  while (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FinType
    (unsafeCoerce sum_eq_dec boundary_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin)
      (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
        (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
    (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce jumpTarget_Step) (unsafeCoerce inhabited_bool)

jumpTarget :: PTM Prelude.Bool
jumpTarget =
  unsafeCoerce seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FinType
    (unsafeCoerce sum_eq_dec boundary_eq
      (sigList_dec
        (eqType_dec (type0 (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin)
      (finType_CS
        (sigList_dec
          (eqType_dec (type0 (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))
        (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
    (finType_CS unit_eq_dec finTypeC_unit)
    (liftTapes (FinType
      (unsafeCoerce sum_eq_dec boundary_eq
        (sigList_dec
          (eqType_dec (type0 (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin)
        (finType_CS
          (sigList_dec
            (eqType_dec (type0 (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))
          (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
      (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit)
      (unsafeCoerce constr_nil (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))
      (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ 0))))) 0 Nil))
    (finType_CS bool_eq_dec finTypeC_bool)
    (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FinType
      (unsafeCoerce sum_eq_dec boundary_eq
        (eqType_dec
          (type0
            (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
              (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin)
        (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
          (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
      (finType_CS unit_eq_dec finTypeC_unit)
      (liftTapes (FinType
        (unsafeCoerce sum_eq_dec boundary_eq
          (eqType_dec
            (type0
              (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))))))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin)
          (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
            (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
        (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS unit_eq_dec finTypeC_unit)
        (changeAlphabet (finType_CS sigNat_eq sigNat_fin)
          (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
            (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))
          (Prelude.succ 0) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce constr_O) (unsafeCoerce retract_sigList_X (retract_sigSum_X retract_id))) (Cons (FS
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (F1 (Prelude.succ (Prelude.succ 0))))) 0 Nil))
      (finType_CS bool_eq_dec finTypeC_bool) jumpTarget_Loop)

retr_clos_step :: FinType0 -> (Retract (SigList SigHClos) EqType_X) -> Retract SigHClos EqType_X
retr_clos_step _ retr_closures_step0 =
  composeRetract retr_closures_step0 (retract_sigList_X retract_id)

retr_pro_clos :: Retract SigPro SigHClos
retr_pro_clos =
  retract_sigPair_Y retract_id

retr_pro_step :: FinType0 -> (Retract (SigList SigHClos) EqType_X) -> Retract SigPro EqType_X
retr_pro_step sigStep retr_closures_step0 =
  composeRetract (retr_clos_step sigStep retr_closures_step0) retr_pro_clos

retr_tok_step :: FinType0 -> (Retract (SigList SigHClos) EqType_X) -> Retract SigCom EqType_X
retr_tok_step sigStep retr_closures_step0 =
  composeRetract (retr_pro_step sigStep retr_closures_step0) (retract_sigList_X retract_id)

retr_nat_clos_ad0 :: Retract SigNat SigHClos
retr_nat_clos_ad0 =
  retract_sigPair_X retract_id

retr_nat_step_clos_ad :: FinType0 -> (Retract (SigList SigHClos) EqType_X) -> Retract SigNat EqType_X
retr_nat_step_clos_ad sigStep retr_closures_step0 =
  composeRetract (retr_clos_step sigStep retr_closures_step0) retr_nat_clos_ad0

step_Lookup :: FinType0 -> (Retract (SigList SigHClos) EqType_X) -> (Retract SigHeap EqType_X) -> PTM EqType_X
step_Lookup sigStep retr_closures_step0 retr_heap_step0 =
  lookup sigStep (retr_clos_step sigStep retr_closures_step0) retr_heap_step0

tailRec :: FinType0 -> (Retract (SigList SigHClos) EqType_X) -> PTM Unit
tailRec sigStep retr_closures_step0 =
  unsafeCoerce if0 (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep)))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
    (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ 0)
      (Prelude.succ (Prelude.succ (Prelude.succ 0))) (finType_CS bool_eq_dec finTypeC_bool)
      (changeAlphabet (finType_CS (sigList_dec (eqType_dec (type0 sigCom_fin))) (sigList_fin sigCom_fin)) sigStep (Prelude.succ 0) (finType_CS bool_eq_dec finTypeC_bool)
        (unsafeCoerce isNil sigCom_fin) (unsafeCoerce retr_pro_step sigStep retr_closures_step0)) (Cons (FS (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0))) 0
      Nil)) (finType_CS unit_eq_dec finTypeC_unit)
    (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ 0)
      (Prelude.succ (Prelude.succ (Prelude.succ 0))) (finType_CS unit_eq_dec finTypeC_unit) (reset sigStep) (Cons (FS (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ
      0))) 0 Nil))
    (seq (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep)))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (finType_CS unit_eq_dec finTypeC_unit)
      (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ
        (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ 0))) (finType_CS unit_eq_dec finTypeC_unit)
        (changeAlphabet (finType_CS (sigPair_dec (eqType_dec (type0 sigHAdd_fin)) (eqType_dec (type0 sigPro_fin))) (sigPair_fin sigHAdd_fin sigPro_fin)) sigStep
          (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce constr_pair sigHAdd_fin sigPro_fin)
          (unsafeCoerce retr_clos_step sigStep retr_closures_step0)) (Cons (FS (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0))) (Prelude.succ 0) (Cons (FS
        (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0))) 0 Nil))) (finType_CS unit_eq_dec finTypeC_unit)
      (seq (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep)))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (finType_CS unit_eq_dec finTypeC_unit)
        (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
          (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ 0))) (finType_CS unit_eq_dec finTypeC_unit)
          (changeAlphabet (finType_CS (sigList_dec (eqType_dec (type0 sigHClos_fin))) (sigList_fin sigHClos_fin)) sigStep (Prelude.succ (Prelude.succ 0))
            (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce constr_cons sigHClos_fin) (unsafeCoerce retr_closures_step0)) (Cons (F1 (Prelude.succ (Prelude.succ 0)))
          (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0))) 0 Nil))) (finType_CS unit_eq_dec finTypeC_unit)
        (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
          (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ 0))) (finType_CS unit_eq_dec finTypeC_unit) (reset sigStep) (Cons (FS (Prelude.succ (Prelude.succ
          0)) (F1 (Prelude.succ 0))) 0 Nil))))

consClos :: FinType0 -> (Retract (SigList SigHClos) EqType_X) -> PTM Unit
consClos sigStep retr_closures_step0 =
  unsafeCoerce seq (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep)))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (finType_CS unit_eq_dec finTypeC_unit)
    (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ
      (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ 0))) (finType_CS unit_eq_dec finTypeC_unit)
      (changeAlphabet (finType_CS (sigPair_dec (eqType_dec (type0 sigHAdd_fin)) (eqType_dec (type0 sigPro_fin))) (sigPair_fin sigHAdd_fin sigPro_fin)) sigStep
        (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce constr_pair sigHAdd_fin sigPro_fin)
        (unsafeCoerce retr_clos_step sigStep retr_closures_step0)) (Cons (FS (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0))) (Prelude.succ 0) (Cons (FS
      (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0))) 0 Nil))) (finType_CS unit_eq_dec finTypeC_unit)
    (seq (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep)))
      (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (finType_CS unit_eq_dec finTypeC_unit)
      (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ
        (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ 0))) (finType_CS unit_eq_dec finTypeC_unit)
        (changeAlphabet (finType_CS (sigList_dec (eqType_dec (type0 sigHClos_fin))) (sigList_fin sigHClos_fin)) sigStep (Prelude.succ (Prelude.succ 0))
          (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce constr_cons sigHClos_fin) (unsafeCoerce retr_closures_step0)) (Cons (F1 (Prelude.succ (Prelude.succ 0)))
        (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0))) 0 Nil))) (finType_CS unit_eq_dec finTypeC_unit)
      (seq (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep)))
        (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (finType_CS unit_eq_dec finTypeC_unit)
        (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
          (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ 0))) (finType_CS unit_eq_dec finTypeC_unit) (reset sigStep) (Cons (FS (Prelude.succ (Prelude.succ
          0)) (FS (Prelude.succ 0) (F1 0))) 0 Nil)) (finType_CS unit_eq_dec finTypeC_unit)
        (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
          (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ 0))) (finType_CS unit_eq_dec finTypeC_unit) (reset sigStep) (Cons (FS (Prelude.succ (Prelude.succ
          0)) (F1 (Prelude.succ 0))) 0 Nil))))

step_lam :: FinType0 -> (Retract (SigList SigHClos) EqType_X) -> PTM Prelude.Bool
step_lam sigStep retr_closures_step0 =
  unsafeCoerce if0 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    0)))))))))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
    (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (finType_CS bool_eq_dec finTypeC_bool)
      (changeAlphabet
        (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
          (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType))))) sigStep
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce jumpTarget)
        (unsafeCoerce retr_pro_step sigStep retr_closures_step0)) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (F1 (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (Cons (FS
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))
      (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (F1
      (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (Prelude.succ (Prelude.succ (Prelude.succ 0))) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ
      0))) (F1 (Prelude.succ (Prelude.succ 0)))))))))) (Prelude.succ (Prelude.succ 0)) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ
      (Prelude.succ 0)) (F1 (Prelude.succ 0)))))))))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (FS
      (Prelude.succ 0) (F1 0)))))))))) 0 Nil)))))) (finType_CS bool_eq_dec finTypeC_bool)
    (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))
      (finType_CS unit_eq_dec finTypeC_unit)
      (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))
        (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
        (finType_CS unit_eq_dec finTypeC_unit)
        (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
          (Prelude.succ (Prelude.succ (Prelude.succ 0))) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ 0)))))))))) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce tailRec sigStep retr_closures_step0) (Cons (F1 (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (Prelude.succ (Prelude.succ 0))
          (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ 0)))))))))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) 0 Nil))))
        (finType_CS unit_eq_dec finTypeC_unit)
        (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
          (Prelude.succ (Prelude.succ (Prelude.succ 0))) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ 0)))))))))) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce consClos sigStep retr_closures_step0) (Cons (FS (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (F1 (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (Prelude.succ (Prelude.succ 0)) (Cons (FS (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (F1
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (F1 (Prelude.succ (Prelude.succ
          (Prelude.succ 0)))))))))) 0 Nil))))) (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.True))
    (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))
      (finType_CS unit_eq_dec finTypeC_unit)
      (unsafeCoerce nop (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))))
      (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.False))

retr_nat_step_hent :: FinType0 -> (Retract SigHeap EqType_X) -> Retract SigNat EqType_X
retr_nat_step_hent _ retr_heap_step0 =
  composeRetract retr_heap_step0 retr_nat_heap_entry

retr_clos_step_hent :: FinType0 -> (Retract SigHeap EqType_X) -> Retract SigHClos EqType_X
retr_clos_step_hent _ retr_heap_step0 =
  composeRetract retr_heap_step0 retr_clos_heap

retr_hent'_step :: FinType0 -> (Retract SigHeap EqType_X) -> Retract SigHEntr' EqType_X
retr_hent'_step _ retr_heap_step0 =
  composeRetract retr_heap_step0 retr_hent'_heap

retr_hent_step :: FinType0 -> (Retract SigHeap EqType_X) -> Retract SigHEntr EqType_X
retr_hent_step _ retr_heap_step0 =
  composeRetract retr_heap_step0 retr_hent_heap

put :: FinType0 -> (Retract (SigList SigHClos) EqType_X) -> (Retract SigHeap EqType_X) -> PTM Unit
put sigStep retr_closures_step0 retr_heap_step0 =
  unsafeCoerce seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FinType
    (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
    (finType_CS unit_eq_dec finTypeC_unit)
    (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))
      (finType_CS unit_eq_dec finTypeC_unit)
      (unsafeCoerce length0 sigStep
        (finType_CS (sigOption_dec (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq))
          (sigOption_fin
            (finType_CS (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq)
              (sigPair_fin
                (finType_CS (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
                  (sigPair_fin (finType_CS sigNat_eq sigNat_fin)
                    (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                      (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
                (finType_CS sigNat_eq sigNat_fin))))) retr_heap_step0 (retr_nat_step_clos_ad sigStep retr_closures_step0)) (Cons (F1 (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (Prelude.succ (Prelude.succ (Prelude.succ 0))) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (F1 (Prelude.succ
      (Prelude.succ 0)))))) (Prelude.succ (Prelude.succ 0)) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0))))))
      (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0)))))) 0 Nil)))))
    (finType_CS unit_eq_dec finTypeC_unit)
    (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FinType
      (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
      (finType_CS unit_eq_dec finTypeC_unit)
      (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ
        0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (finType_CS unit_eq_dec finTypeC_unit)
        (changeAlphabet (finType_CS (sigList_dec (eqType_dec (type0 sigHEntr_fin))) (sigList_fin sigHEntr_fin)) sigStep (Prelude.succ 0)
          (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce constr_nil sigHEntr_fin) (unsafeCoerce retr_heap_step0)) (Cons (FS (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ
        0))) (FS (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0)))))) 0 Nil)) (finType_CS unit_eq_dec finTypeC_unit)
      (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FinType
        (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
        (finType_CS unit_eq_dec finTypeC_unit)
        (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
          (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (finType_CS unit_eq_dec finTypeC_unit)
          (translate0 sigStep (finType_CS sigNat_eq sigNat_fin) (unsafeCoerce retr_nat_step_clos_ad sigStep retr_closures_step0)
            (unsafeCoerce retr_nat_step_hent sigStep retr_heap_step0)) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) 0 Nil))
        (finType_CS unit_eq_dec finTypeC_unit)
        (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FinType
          (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
          (finType_CS unit_eq_dec finTypeC_unit)
          (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
            (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (finType_CS unit_eq_dec finTypeC_unit)
            (translate0 sigStep
              (finType_CS (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
                (sigPair_fin (finType_CS sigNat_eq sigNat_fin)
                  (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                    (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
              (unsafeCoerce retr_clos_step sigStep retr_closures_step0) (unsafeCoerce retr_clos_step_hent sigStep retr_heap_step0)) (Cons (FS (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) 0 Nil))
          (finType_CS unit_eq_dec finTypeC_unit)
          (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FinType
            (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
            (finType_CS unit_eq_dec finTypeC_unit)
            (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
              (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))
              (finType_CS unit_eq_dec finTypeC_unit)
              (changeAlphabet (finType_CS (sigPair_dec (eqType_dec (type0 sigHClos_fin)) (eqType_dec (type0 sigHAdd_fin))) (sigPair_fin sigHClos_fin sigHAdd_fin))
                sigStep (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce constr_pair sigHClos_fin sigHAdd_fin)
                (unsafeCoerce retr_hent'_step sigStep retr_heap_step0)) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (F1
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) 0 Nil)))
            (finType_CS unit_eq_dec finTypeC_unit)
            (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FinType
              (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
              (finType_CS unit_eq_dec finTypeC_unit)
              (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
                (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (finType_CS unit_eq_dec finTypeC_unit)
                (changeAlphabet (finType_CS (sigOption_dec (eqType_dec (type0 sigHEntr'_fin))) (sigOption_fin sigHEntr'_fin)) sigStep (Prelude.succ 0)
                  (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce constr_Some sigHEntr'_fin) (unsafeCoerce retr_hent_step sigStep retr_heap_step0)) (Cons (FS
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (F1
                (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) 0 Nil)) (finType_CS unit_eq_dec finTypeC_unit)
              (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FinType
                (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
                (finType_CS unit_eq_dec finTypeC_unit)
                (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
                  (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))
                  (finType_CS unit_eq_dec finTypeC_unit)
                  (changeAlphabet (finType_CS (sigList_dec (eqType_dec (type0 sigHEntr_fin))) (sigList_fin sigHEntr_fin)) sigStep (Prelude.succ (Prelude.succ 0))
                    (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce constr_cons sigHEntr_fin) (unsafeCoerce retr_heap_step0)) (Cons (FS (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ
                  (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0)))))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ
                  0)))))) 0 Nil))) (finType_CS unit_eq_dec finTypeC_unit)
                (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FinType
                  (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
                  (finType_CS unit_eq_dec finTypeC_unit)
                  (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
                    (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))
                    (finType_CS unit_eq_dec finTypeC_unit)
                    (changeAlphabet (FinType (unsafeCoerce sigList_dec (eqType_dec (type0 sigHEntr_fin))) (sigList_fin sigHEntr_fin)) sigStep (Prelude.succ (Prelude.succ
                      0)) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce app' sigHEntr_fin) (unsafeCoerce retr_heap_step0)) (Cons (F1 (Prelude.succ (Prelude.succ
                    (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                    0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ
                    (Prelude.succ 0)) (F1 (Prelude.succ 0)))))) 0 Nil))) (finType_CS unit_eq_dec finTypeC_unit)
                  (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FinType
                    (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
                    (finType_CS unit_eq_dec finTypeC_unit)
                    (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
                      (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))
                      (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce moveValue sigStep) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                      (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS
                      (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0)))))) (Prelude.succ 0) (Cons (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                      (Prelude.succ 0)))))) 0 Nil))) (finType_CS unit_eq_dec finTypeC_unit)
                    (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FinType
                      (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
                      (finType_CS unit_eq_dec finTypeC_unit)
                      (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep)))
                        (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                        (Prelude.succ (Prelude.succ 0)))))) (finType_CS unit_eq_dec finTypeC_unit) (reset sigStep) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ
                        (Prelude.succ (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (F1 (Prelude.succ (Prelude.succ
                        (Prelude.succ 0)))))) 0 Nil)) (finType_CS unit_eq_dec finTypeC_unit)
                      (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep)))
                        (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                        (Prelude.succ (Prelude.succ 0)))))) (finType_CS unit_eq_dec finTypeC_unit) (reset sigStep) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ
                        (Prelude.succ (Prelude.succ 0))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) 0 Nil)))))))))))

step_app :: FinType0 -> (Retract (SigList SigHClos) EqType_X) -> (Retract SigHeap EqType_X) -> PTM Prelude.Bool
step_app sigStep retr_closures_step0 retr_heap_step0 =
  unsafeCoerce if0 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ 0))))))))))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
    (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ
      (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ 0))))))))))) (finType_CS bool_eq_dec finTypeC_bool)
      (changeAlphabet (finType_CS (sigList_dec (eqType_dec (type0 sigHClos_fin))) (sigList_fin sigHClos_fin)) sigStep (Prelude.succ (Prelude.succ 0))
        (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce caseList sigHClos_fin) (unsafeCoerce retr_closures_step0)) (Cons (FS (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (F1 (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ 0) (Cons (FS (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (F1
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) 0 Nil))) (finType_CS bool_eq_dec finTypeC_bool)
    (if0 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      0))))))))))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
      (unsafeCoerce liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
        (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ 0))))))))))) (finType_CS bool_eq_dec finTypeC_bool)
        (changeAlphabet (finType_CS (sigList_dec (eqType_dec (type0 sigHClos_fin))) (sigList_fin sigHClos_fin)) sigStep (Prelude.succ (Prelude.succ 0))
          (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce caseList sigHClos_fin) (unsafeCoerce retr_closures_step0)) (Cons (FS (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (F1 (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ 0) (Cons (FS (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FS
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) 0 Nil)))
      (finType_CS bool_eq_dec finTypeC_bool)
      (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))))
        (finType_CS unit_eq_dec finTypeC_unit)
        (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          0))))))))))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
          (finType_CS unit_eq_dec finTypeC_unit)
          (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
            (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ 0))))))))))) (finType_CS unit_eq_dec finTypeC_unit)
            (changeAlphabet (finType_CS (sigPair_dec (eqType_dec (type0 sigHAdd_fin)) (eqType_dec (type0 sigPro_fin))) (sigPair_fin sigHAdd_fin sigPro_fin)) sigStep
              (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce casePair sigHAdd_fin sigPro_fin)
              (unsafeCoerce retr_clos_step sigStep retr_closures_step0)) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            0))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (F1 (Prelude.succ (Prelude.succ
            (Prelude.succ 0))))))))))) 0 Nil))) (finType_CS unit_eq_dec finTypeC_unit)
          (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            0))))))))))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
            (finType_CS unit_eq_dec finTypeC_unit)
            (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
              (Prelude.succ (Prelude.succ (Prelude.succ 0))) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) (finType_CS unit_eq_dec finTypeC_unit)
              (unsafeCoerce tailRec sigStep retr_closures_step0) (Cons (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ (Prelude.succ 0)) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ 0))))))))))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (F1 (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) 0 Nil)))) (finType_CS unit_eq_dec finTypeC_unit)
            (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ 0))))))))))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep)))
              (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (finType_CS unit_eq_dec finTypeC_unit)
              (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
                (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ 0))))))))))) (finType_CS unit_eq_dec finTypeC_unit) (reset sigStep) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) 0
                Nil)) (finType_CS unit_eq_dec finTypeC_unit)
              (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                (Prelude.succ 0))))))))))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep)))
                (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (finType_CS unit_eq_dec finTypeC_unit)
                (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) (finType_CS unit_eq_dec finTypeC_unit)
                  (unsafeCoerce put sigStep retr_closures_step0 retr_heap_step0) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (Cons
                  (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  0)))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))))
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (F1 (Prelude.succ
                  (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ (Prelude.succ (Prelude.succ 0))) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (F1 (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ (Prelude.succ 0))
                  (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  0)))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0))
                  (F1 (Prelude.succ 0))))))))))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ
                  (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0))))))))))) 0 Nil))))))) (finType_CS unit_eq_dec finTypeC_unit)
                (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
                  (Prelude.succ (Prelude.succ (Prelude.succ 0))) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) (finType_CS unit_eq_dec finTypeC_unit)
                  (unsafeCoerce consClos sigStep retr_closures_step0) (Cons (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ (Prelude.succ 0)) (Cons (FS (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (F1 (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ 0)
                  (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  0)))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (F1
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) 0 Nil)))))))) (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.True))
      (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))))
        (finType_CS unit_eq_dec finTypeC_unit)
        (unsafeCoerce nop (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          0)))))))))))) (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.False)))
    (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))))
      (finType_CS unit_eq_dec finTypeC_unit)
      (unsafeCoerce nop (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        0)))))))))))) (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.False))

step_var :: FinType0 -> (Retract (SigList SigHClos) EqType_X) -> (Retract SigHeap EqType_X) -> PTM Prelude.Bool
step_var sigStep retr_closures_step0 retr_heap_step0 =
  unsafeCoerce seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FinType
    (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
    (finType_CS unit_eq_dec finTypeC_unit)
    (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ
      (Prelude.succ (Prelude.succ 0))) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))
      (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce tailRec sigStep retr_closures_step0) (Cons (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (Prelude.succ (Prelude.succ 0)) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (Prelude.succ 0) (Cons (FS
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ 0)))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) 0 Nil)))) (finType_CS bool_eq_dec finTypeC_bool)
    (if0 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FinType
      (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
      (unsafeCoerce liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ 0)))))))) (finType_CS bool_eq_dec finTypeC_bool) (step_Lookup sigStep retr_closures_step0 retr_heap_step0) (Cons (FS (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ 0)))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0)))) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))
        (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (Prelude.succ (Prelude.succ
        (Prelude.succ 0))) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))
        (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (F1 (Prelude.succ (Prelude.succ 0))))))))
        (Prelude.succ (Prelude.succ 0)) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ
        (Prelude.succ 0)) (F1 (Prelude.succ 0)))))))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ
        0))) (FS (Prelude.succ (Prelude.succ 0)) (FS (Prelude.succ 0) (F1 0)))))))) 0 Nil)))))) (finType_CS bool_eq_dec finTypeC_bool)
      (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (finType_CS unit_eq_dec finTypeC_unit)
        (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FinType
          (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
          (finType_CS unit_eq_dec finTypeC_unit)
          (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
            (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))
            (finType_CS unit_eq_dec finTypeC_unit)
            (changeAlphabet (finType_CS (sigList_dec (eqType_dec (type0 sigHClos_fin))) (sigList_fin sigHClos_fin)) sigStep (Prelude.succ (Prelude.succ 0))
              (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce constr_cons sigHClos_fin) (unsafeCoerce retr_closures_step0)) (Cons (FS (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ 0)))))))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))
            (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ
            (Prelude.succ 0)) (F1 (Prelude.succ 0)))))))) 0 Nil))) (finType_CS unit_eq_dec finTypeC_unit)
          (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
            (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))
            (finType_CS unit_eq_dec finTypeC_unit) (reset sigStep) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ
            (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0)) (F1 (Prelude.succ 0)))))))) 0 Nil))) (finType_CS bool_eq_dec finTypeC_bool)
        (unsafeCoerce Prelude.True))
      (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (finType_CS unit_eq_dec finTypeC_unit)
        (unsafeCoerce nop (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))
        (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.False)))

bool2optunit :: Prelude.Bool -> Prelude.Maybe Unit
bool2optunit b =
  case b of {
   Prelude.True -> Prelude.Nothing;
   Prelude.False -> Prelude.Just Tt}

step :: FinType0 -> (Retract (SigList SigHClos) EqType_X) -> (Retract SigHeap EqType_X) -> PTM (Prelude.Maybe Unit)
step sigStep retr_closures_step0 retr_heap_step0 =
  unsafeCoerce relabel (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    0))))))))))) (finType_CS bool_eq_dec finTypeC_bool) (finType_CS (option_eq_dec unit_eq_dec) (finTypeC_Option (finType_CS unit_eq_dec finTypeC_unit)))
    (if0 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      0))))))))))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
      (unsafeCoerce liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
        (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ 0))))))))))) (finType_CS bool_eq_dec finTypeC_bool)
        (changeAlphabet (finType_CS (sigList_dec (eqType_dec (type0 sigHClos_fin))) (sigList_fin sigHClos_fin)) sigStep (Prelude.succ (Prelude.succ 0))
          (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce caseList sigHClos_fin) (unsafeCoerce retr_closures_step0)) (Cons (F1 (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ 0) (Cons (FS
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) 0 Nil))) (finType_CS bool_eq_dec finTypeC_bool)
      (seq (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        0))))))))))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
        (finType_CS unit_eq_dec finTypeC_unit)
        (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
          (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ 0))))))))))) (finType_CS unit_eq_dec finTypeC_unit)
          (changeAlphabet (finType_CS (sigPair_dec (eqType_dec (type0 sigHAdd_fin)) (eqType_dec (type0 sigPro_fin))) (sigPair_fin sigHAdd_fin sigPro_fin)) sigStep
            (Prelude.succ (Prelude.succ 0)) (finType_CS unit_eq_dec finTypeC_unit) (unsafeCoerce casePair sigHAdd_fin sigPro_fin)
            (unsafeCoerce retr_clos_step sigStep retr_closures_step0)) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ 0)))))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ 0)
          (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          0)))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ 0))))))))))) 0 Nil))) (finType_CS bool_eq_dec finTypeC_bool)
        (if0 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          0))))))))))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
          (unsafeCoerce liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep)))
            (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) (finType_CS bool_eq_dec finTypeC_bool)
            (changeAlphabet (finType_CS (sigList_dec (eqType_dec (type0 sigCom_fin))) (sigList_fin sigCom_fin)) sigStep (Prelude.succ (Prelude.succ 0))
              (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce caseList sigCom_fin) (unsafeCoerce retr_pro_step sigStep retr_closures_step0)) (Cons (FS (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ 0))))))))))) 0 Nil))) (finType_CS bool_eq_dec finTypeC_bool)
          (switch (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ 0))))))))))) (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep)))
            (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
            (finType_CS (option_eq_dec aCom_eq_dec) (finTypeC_Option (finType_CS aCom_eq_dec aCom_finType)))
            (liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
              (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ 0))))))))))) (finType_CS (option_eq_dec aCom_eq_dec) (finTypeC_Option (finType_CS aCom_eq_dec aCom_finType)))
              (changeAlphabet (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))
                sigStep (Prelude.succ 0) (finType_CS (option_eq_dec aCom_eq_dec) (finTypeC_Option (finType_CS aCom_eq_dec aCom_finType))) (unsafeCoerce caseCom)
                (unsafeCoerce retr_tok_step sigStep retr_closures_step0)) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              0))))))))))) 0 Nil)) (finType_CS bool_eq_dec finTypeC_bool) (\t ->
            case unsafeCoerce t of {
             Prelude.Just a ->
              case a of {
               RetAT ->
                return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ 0))))))))))) (finType_CS unit_eq_dec finTypeC_unit)
                  (unsafeCoerce nop (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep)))
                    (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))))) (finType_CS bool_eq_dec finTypeC_bool)
                  (unsafeCoerce Prelude.False);
               LamAT ->
                liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ 0))))))))))) (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce step_lam sigStep retr_closures_step0) (Cons (F1 (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))))
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (Cons (FS
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))
                  (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))))
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (Cons (FS (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (F1
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ 0)))))) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (F1
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ 0))))) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))
                  (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (Cons (FS (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (F1 (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ (Prelude.succ (Prelude.succ 0))) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ 0)))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ (Prelude.succ 0)) (Cons (FS (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (F1 (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ 0)
                  (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  0)))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                  0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS
                  (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (FS (Prelude.succ (Prelude.succ (Prelude.succ 0))) (FS (Prelude.succ (Prelude.succ 0))
                  (F1 (Prelude.succ 0))))))))))) 0 Nil))))))))));
               AppAT -> unsafeCoerce step_app sigStep retr_closures_step0 retr_heap_step0};
             Prelude.Nothing ->
              liftTapes (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))))
                (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce step_var sigStep retr_closures_step0 retr_heap_step0) (Cons (F1 (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ 0)))))) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (Cons (FS (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (F1 (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (Cons
                (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                0)))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))
                (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ (Prelude.succ (Prelude.succ 0))) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (F1 (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) (Prelude.succ (Prelude.succ 0)) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) (FS (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FS
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))))
                (Prelude.succ 0) (Cons (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                (Prelude.succ 0)))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                (Prelude.succ 0))))))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))
                (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))) (FS (Prelude.succ (Prelude.succ
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (FS (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (FS
                (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (F1 (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) 0 Nil))))))))}))
          (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))))
            (finType_CS unit_eq_dec finTypeC_unit)
            (unsafeCoerce nop (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              0)))))))))))) (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.False))))
      (return (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep)) (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))))
        (finType_CS unit_eq_dec finTypeC_unit)
        (unsafeCoerce nop (FinType (unsafeCoerce sum_eq_dec boundary_eq (eqType_dec (type0 sigStep))) (finTypeC_sum (finType_CS boundary_eq boundary_fin) sigStep))
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          0)))))))))))) (finType_CS bool_eq_dec finTypeC_bool) (unsafeCoerce Prelude.False))) bool2optunit

type SigStep = Sum (SigList SigHClos) SigHeap

retr_heap_step :: Retract SigHeap SigStep
retr_heap_step =
  retract_inr retract_id

retr_closures_step :: Retract (SigList SigHClos) SigStep
retr_closures_step =
  retract_inl retract_id

loop :: PTM EqType_X
loop =
  while (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    0))))))))))) (FinType
    (unsafeCoerce sum_eq_dec boundary_eq
      (eqType_dec
        (type0
          (finType_CS
            (sum_eq_dec (sigList_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))))
              (sigList_dec (sigOption_dec (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq))))
            (finTypeC_sum
              (finType_CS (sigList_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))))
                (sigList_fin
                  (finType_CS (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
                    (sigPair_fin (finType_CS sigNat_eq sigNat_fin)
                      (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                        (sigList_fin
                          (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))))
              (finType_CS (sigList_dec (sigOption_dec (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq)))
                (sigList_fin
                  (finType_CS (sigOption_dec (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq))
                    (sigOption_fin
                      (finType_CS (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq)
                        (sigPair_fin
                          (finType_CS (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
                            (sigPair_fin (finType_CS sigNat_eq sigNat_fin)
                              (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                                (sigList_fin
                                  (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
                          (finType_CS sigNat_eq sigNat_fin))))))))))))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin)
      (finType_CS
        (sum_eq_dec (sigList_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))))
          (sigList_dec (sigOption_dec (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq))))
        (finTypeC_sum
          (finType_CS (sigList_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))))
            (sigList_fin
              (finType_CS (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
                (sigPair_fin (finType_CS sigNat_eq sigNat_fin)
                  (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                    (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))))
          (finType_CS (sigList_dec (sigOption_dec (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq)))
            (sigList_fin
              (finType_CS (sigOption_dec (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq))
                (sigOption_fin
                  (finType_CS (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq)
                    (sigPair_fin
                      (finType_CS (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
                        (sigPair_fin (finType_CS sigNat_eq sigNat_fin)
                          (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                            (sigList_fin
                              (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
                      (finType_CS sigNat_eq sigNat_fin))))))))))) (finType_CS unit_eq_dec finTypeC_unit)
    (unsafeCoerce step
      (finType_CS
        (sum_eq_dec (sigList_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))))
          (sigList_dec (sigOption_dec (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq))))
        (finTypeC_sum
          (finType_CS (sigList_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))))
            (sigList_fin
              (finType_CS (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
                (sigPair_fin (finType_CS sigNat_eq sigNat_fin)
                  (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                    (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))))
          (finType_CS (sigList_dec (sigOption_dec (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq)))
            (sigList_fin
              (finType_CS (sigOption_dec (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq))
                (sigOption_fin
                  (finType_CS (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq)
                    (sigPair_fin
                      (finType_CS (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
                        (sigPair_fin (finType_CS sigNat_eq sigNat_fin)
                          (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                            (sigList_fin
                              (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
                      (finType_CS sigNat_eq sigNat_fin))))))))) retr_closures_step retr_heap_step) (unsafeCoerce inhabited_unit)

loop_states :: FinType0
loop_states =
  states (FinType
    (unsafeCoerce sum_eq_dec boundary_eq
      (eqType_dec
        (type0
          (finType_CS
            (sum_eq_dec (sigList_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))))
              (sigList_dec (sigOption_dec (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq))))
            (finTypeC_sum
              (finType_CS (sigList_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))))
                (sigList_fin
                  (finType_CS (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
                    (sigPair_fin (finType_CS sigNat_eq sigNat_fin)
                      (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                        (sigList_fin
                          (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))))
              (finType_CS (sigList_dec (sigOption_dec (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq)))
                (sigList_fin
                  (finType_CS (sigOption_dec (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq))
                    (sigOption_fin
                      (finType_CS (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq)
                        (sigPair_fin
                          (finType_CS (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
                            (sigPair_fin (finType_CS sigNat_eq sigNat_fin)
                              (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                                (sigList_fin
                                  (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
                          (finType_CS sigNat_eq sigNat_fin))))))))))))
    (finTypeC_sum (finType_CS boundary_eq boundary_fin)
      (finType_CS
        (sum_eq_dec (sigList_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))))
          (sigList_dec (sigOption_dec (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq))))
        (finTypeC_sum
          (finType_CS (sigList_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))))
            (sigList_fin
              (finType_CS (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
                (sigPair_fin (finType_CS sigNat_eq sigNat_fin)
                  (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                    (sigList_fin (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))))
          (finType_CS (sigList_dec (sigOption_dec (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq)))
            (sigList_fin
              (finType_CS (sigOption_dec (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq))
                (sigOption_fin
                  (finType_CS (sigPair_dec (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))) sigNat_eq)
                    (sigPair_fin
                      (finType_CS (sigPair_dec sigNat_eq (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec)))
                        (sigPair_fin (finType_CS sigNat_eq sigNat_fin)
                          (finType_CS (sigList_dec (sigSum_dec sigNat_eq aCom_eq_dec))
                            (sigList_fin
                              (finType_CS (sigSum_dec sigNat_eq aCom_eq_dec) (sigSum_fin (finType_CS sigNat_eq sigNat_fin) (finType_CS aCom_eq_dec aCom_finType)))))))
                      (finType_CS sigNat_eq sigNat_fin))))))))))) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) (projT1 loop)

loop_states_card :: Prelude.Int
loop_states_card =
  length (elem loop_states)

main = print (loop_states_card)