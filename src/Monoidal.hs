{-# language EmptyCase #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language DataKinds #-}
{-# language ConstraintKinds, GADTs #-}
{-# language MultiParamTypeClasses, FunctionalDependencies #-}
{-# language TypeFamilyDependencies #-}
{-# language TypeFamilies #-}
{-# language TypeOperators #-}
{-# language RankNTypes #-}
{-# language PolyKinds #-}
{-# language TypeInType #-}
{-# language ScopedTypeVariables #-}
{-# language TypeApplications #-}

{-# language TemplateHaskell #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# OPTIONS_GHC -O -fplugin Test.Inspection.Plugin #-}

module Monoidal where

import Prelude hiding (id, (.), Functor(..), const, uncurry, fst, snd, curry)
import qualified Prelude
import Data.Coerce
import Data.Functor.Identity
import Data.Kind
import Data.Proxy
import Data.Void
import Test.Inspection

import qualified Data.Functor.Day as Functor
import qualified Data.Functor.Sum as Functor
import qualified Data.Functor.Product as Functor

class Vacuous (a :: *) where
instance Vacuous a where

instance Category (->) where
  type Obj (->) = Vacuous
  id = \a -> a
  (.) = \f g x -> f (g x)

class Category (arr :: k -> k -> Type) where
  type Obj arr :: k -> Constraint
  id :: a `arr` a
  (.) :: b `arr` c -> a `arr` b -> a `arr` c

class Category (arr :: k -> k -> Type) => Product arr (p :: k -> k -> k)
  | p -> arr, arr -> p -- products are unique up to isomorphism, so there only needs to be one instance per category
  where

  fst :: p a b `arr` a
  snd :: p a b `arr` b
  intro
    :: y `arr` a
    -> y `arr` b
    -> y `arr` p a b

instance Product (->) (,) where
  {-# inline fst #-}
  fst (a, _) = a

  {-# inline snd #-}
  snd (_, b) = b

  {-# inline intro #-}
  intro f g x = (f x, g x)

prodAssoc :: Product arr p => p a (p b c) `arr` p (p a b) c
prodAssoc = intro (intro fst (fst . snd)) (snd . snd)

prodDeassoc :: Product arr p => p (p a b) c `arr` p a (p b c)
prodDeassoc = intro (fst . fst) (intro (snd . fst) snd)

prodSwap :: Product arr p => p a b `arr` p b a
prodSwap = intro snd fst

class Category (arr :: k -> k -> Type) => Coproduct arr (p :: k -> k -> k) | p -> arr, arr -> p where
  inl :: a `arr` p a b
  inr :: b `arr` p a b
  elim
    :: a `arr` y
    -> b `arr` y
    -> p a b `arr` y

instance Coproduct (->) Either where
  inl = Left
  inr = Right
  elim = either

class Product (arr :: k -> k -> Type) p => Exponential arr p (e :: k -> k -> k)
  | e -> arr p, arr -> p e -- not sure about this one
  where
  apply :: p (e z y) y `arr` z
  curry :: p x y `arr` z -> x `arr` e z y

uncurry :: Exponential arr p e => x `arr` e z y -> p x y `arr` z
uncurry f = apply . intro (f . fst) snd

class Category arr => Terminating (arr :: k -> k -> Type) where
  type Terminal arr :: k
  terminal :: a `arr` Terminal arr

class Terminating arr => Pointed arr where
  point :: a -> Terminal arr `arr` a

const :: Pointed arr => a -> b `arr` a
const a = point a . terminal

instance Terminating (->) where
  type Terminal (->) = ()

  {-# inline terminal #-}
  terminal _ = ()

powerOfOne_to :: (Terminating arr, Exponential arr p e) => e (Terminal arr) a `arr` Terminal arr
powerOfOne_to = terminal

powerOfOne_from :: (Terminating arr, Exponential arr p e) => Terminal arr `arr` e (Terminal arr) a
powerOfOne_from = curry fst

expPoints_to :: (Terminating arr, Exponential arr p e) => Terminal arr `arr` e y x -> x `arr` y
expPoints_to f = uncurry f . intro terminal id

expPoints_from :: (Terminating arr, Exponential arr p e) => x `arr` y -> Terminal arr `arr` e y x
expPoints_from f = curry (f . snd)

firstPower_to :: forall a arr p e. (Terminating arr, Exponential arr p e) => e a (Terminal arr) `arr` a
firstPower_to = apply . intro id terminal

firstPower_from :: forall a arr p e. (Terminating arr, Exponential arr p e) => a `arr` e a (Terminal arr)
firstPower_from = curry fst

expUncurry :: forall arr p e z y x. Exponential arr p e => e (e z y) x `arr` e z (p y x)
expUncurry =
  curry $
  apply . intro @arr @p (apply . fst) snd .
  prodAssoc . intro fst (prodSwap . snd)

expProd_from :: Exponential arr p e => e z (p x y) `arr` e (e z y) x
expProd_from = curry (curry (apply . prodDeassoc))

expFlipConst :: Exponential arr p e => b `arr` e a a
expFlipConst = curry snd

expConst :: Exponential arr p e => a `arr` e a b
expConst = curry fst

class Category arr => Initiating (arr :: k -> k -> Type) where
  type Initial arr :: k
  initial :: Initial arr `arr` a

newtype Arr1 (a :: * -> *) (b :: * -> *)
  = Arr1 { apArr1 :: forall x. a x -> b x }

instance Category Arr1 where
  type Obj Arr1 = Prelude.Functor
  id = Arr1 id
  Arr1 f . Arr1 g = Arr1 (f . g)

class (Category p, Category q, Category r) => Bifunctor p q r (f :: i -> j -> k)
  | f -> p q r
  where
  bimap
    :: (a `p` b)
    -> (c `q` d)
    -> (f a c `r` f b d)

instance Bifunctor Arr1 Arr1 Arr1 Functor.Day where
  {-# inline bimap #-}
  bimap f g = Arr1 $ \(Functor.Day x y z) -> Functor.Day (apArr1 f x) (apArr1 g y) z

instance Bifunctor Arr1 Arr1 Arr1 Functor.Product where
  {-# inline bimap #-}
  bimap f g = Arr1 $ \(Functor.Pair x y) -> Functor.Pair (apArr1 f x) (apArr1 g y)

instance Product Arr1 Functor.Product where
  {-# inline fst #-}
  fst = Arr1 $ \(Functor.Pair a _) -> a

  {-# inline snd #-}
  snd = Arr1 $ \(Functor.Pair _ a) -> a

  {-# inline intro #-}
  intro f g = Arr1 $ \a -> Functor.Pair (apArr1 f a) (apArr1 g a)

instance Bifunctor Arr1 Arr1 Arr1 Functor.Sum where
  {-# inline bimap #-}
  bimap f g = Arr1 $ \a -> case a of
    Functor.InL x -> Functor.InL (apArr1 f x)
    Functor.InR x -> Functor.InR (apArr1 g x)

instance Coproduct Arr1 Functor.Sum where
  {-# inline inl #-}
  inl = Arr1 Functor.InL
  {-# inline inr #-}
  inr = Arr1 Functor.InR
  {-# inline elim #-}
  elim f g =
    Arr1 $ \a -> case a of
      Functor.InL x -> apArr1 f x
      Functor.InR x -> apArr1 g x

instance StrongBifunctor Arr1 Functor.Product Functor.Sum where
  {-# inline lstrength #-}
  lstrength =
    Arr1 $ \(Functor.Pair a b) -> case b of
      Functor.InL c -> Functor.InL (Functor.Pair a c)
      Functor.InR c -> Functor.InR c

  {-# inline rstrength #-}
  rstrength =
    Arr1 $ \(Functor.Pair a b) -> case b of
      Functor.InL c -> Functor.InL c
      Functor.InR c -> Functor.InR (Functor.Pair a c)

class (Category arr, Bifunctor arr arr arr t) => Tensor arr (t :: k -> k -> k) where
  type Unit t :: k

  assoc :: t (t a b) c `arr` t a (t b c)
  deassoc :: t a (t b c) `arr` t (t a b) c

  unitLeftTo :: Obj arr a => t (Unit t) a `arr` a
  unitLeftFrom :: a `arr` t (Unit t) a

  unitRightTo :: Obj arr a => t a (Unit t) `arr` a
  unitRightFrom :: a `arr` t a (Unit t)

class Tensor arr t => Symmetric arr t where
  swap :: t a b `arr` t b a

instance Tensor Arr1 Functor.Day where
  type Unit Functor.Day = Identity
  assoc = Arr1 Functor.disassoc
  deassoc = Arr1 Functor.assoc

  unitLeftTo = Arr1 Functor.elim1
  unitLeftFrom = Arr1 Functor.intro1

  unitRightTo = Arr1 Functor.elim2
  unitRightFrom = Arr1 Functor.intro2

instance Tensor Arr1 Functor.Product where
  type Unit Functor.Product = Proxy
  assoc = Arr1 $ \(Functor.Pair (Functor.Pair a b) c) -> Functor.Pair a (Functor.Pair b c)
  deassoc = Arr1 $ \(Functor.Pair a (Functor.Pair b c)) -> Functor.Pair (Functor.Pair a b) c

  unitLeftTo = Arr1 $ \(Functor.Pair _ a) -> a
  unitLeftFrom = Arr1 $ \a -> Functor.Pair Proxy a

  unitRightTo = Arr1 $ \(Functor.Pair a _) -> a
  unitRightFrom = Arr1 $ \a -> Functor.Pair a Proxy

data Void1 a

absurd1 :: Void1 x -> a
absurd1 a = case a of

instance Prelude.Functor Void1 where; fmap _ = absurd1

instance Tensor Arr1 Functor.Sum where
  type Unit Functor.Sum = Void1
  assoc =
    Arr1 $ \a -> case a of
      Functor.InL (Functor.InL a) -> Functor.InL a
      Functor.InL (Functor.InR a) -> Functor.InR (Functor.InL a)
      Functor.InR a -> Functor.InR (Functor.InR a)
  deassoc =
    Arr1 $ \a -> case a of
      Functor.InL a -> Functor.InL (Functor.InL a)
      Functor.InR (Functor.InL a) -> Functor.InL (Functor.InR a)
      Functor.InR (Functor.InR a) -> Functor.InR a

  unitLeftTo =
    Arr1 $ \a -> case a of
    Functor.InL a -> absurd1 a
    Functor.InR a -> a
  unitLeftFrom = Arr1 $ Functor.InR

  unitRightTo =
    Arr1 $ \a -> case a of
      Functor.InL a -> a
      Functor.InR a -> absurd1 a
  unitRightFrom = Arr1 $ Functor.InL

class
  ( Category (p :: i -> i -> Type)
  , Category (q :: j -> j -> Type)
  ) => Functor p q (f :: i -> j) | f -> p q where

  fmap :: (a `p` b) -> (f a `q` f b)

type family Fst a where; Fst '(a, b) = a
type family Snd a where; Snd '(a, b) = b

data ProdCat
  (p :: i -> i -> Type)
  (q :: j -> j -> Type)
  (a :: (i, j))
  (b :: (i, j)) =

  ProdCat (Fst a `p` Fst b) (Snd a `q` Snd b)

class (Category p, Category q) => ProdObj p q (a :: (i, j)) | p q -> a where
instance (Category p, Category q) => ProdObj p q '(p, q) where

instance (Category p, Category q) => Category (ProdCat p q) where
  type Obj (ProdCat p q) = ProdObj p q
  id = ProdCat id id
  ProdCat f f' . ProdCat g g' = ProdCat (f . g) (f' . g')

-- |
-- This is kinda dubious, but it gets me where I need to go
class (Tensor k t, Bifunctor k k k f) => StrongBifunctor k t f where
  lstrength :: t a (f b c) `k` f (t a b) c
  rstrength :: t a (f b c) `k` f b (t a c)

instance StrongBifunctor (->) (,) (,) where
  {-# inline lstrength #-}
  lstrength (a, b) =
    case b of
      (c, d) -> ((a, c), d)

  {-# inline rstrength  #-}
  rstrength (a, b) =
    case b of
      (c, d) -> (c, (a, d))

instance StrongBifunctor (->) (,) Either where
  {-# inline lstrength #-}
  lstrength (a, b) =
    case b of
      Left c -> Left (a, c)
      Right c -> Right c

  {-# inline rstrength  #-}
  rstrength (a, b) =
    case b of
      Left c -> Left c
      Right c -> Right (a, c)

first :: Bifunctor p q r f => p a b -> f a c `r` f b c
first f = bimap f id

second :: Bifunctor p q r f => q a b -> f c a `r` f c b
second f = bimap id f

instance Bifunctor (->) (->) (->) Either where
  bimap f _ (Left a) = Left (f a)
  bimap _ g (Right a) = Right (g a)

instance Tensor (->) Either where
  type Unit Either = Void
  assoc (Left (Left a)) = Left a
  assoc (Left (Right a)) = Right (Left a)
  assoc (Right a) = Right (Right a)

  deassoc (Left a) = Left (Left a)
  deassoc (Right (Left a)) = Left (Right a)
  deassoc (Right (Right a)) = Right a

  unitLeftTo (Left a) = absurd a
  unitLeftTo (Right a) = a
  unitLeftFrom = Right

  unitRightTo (Left a) = a
  unitRightTo (Right a) = absurd a
  unitRightFrom = Left

newtype EitherK a b = EitherK { unEitherK :: forall r. (a -> r) -> (b -> r) -> r }

left :: a -> EitherK a b
left a = EitherK $ \f _ -> f a

right :: b -> EitherK a b
right a = EitherK $ \_ g -> g a

instance Bifunctor (->) (->) (->) EitherK where
  bimap f g e = unEitherK e (left . f) (right . g)

instance Tensor (->) EitherK where
  type Unit EitherK = Void
  {-# inline assoc #-}
  assoc e = unEitherK e (\e' -> unEitherK e' left (right . left)) (right . right)
  {-# inline deassoc #-}
  deassoc e = unEitherK e (left . left) (\e' -> unEitherK e' (left . right) right)
  {-# inline unitLeftTo #-}
  unitLeftTo e = unEitherK e absurd id
  {-# inline unitLeftFrom #-}
  unitLeftFrom a = EitherK $ \_ y -> y a
  {-# inline unitRightTo #-}
  unitRightTo e = unEitherK e id absurd
  {-# inline unitRightFrom #-}
  unitRightFrom a = EitherK $ \x _ -> x a

newtype TupleK a b = TupleK { unTupleK :: forall r. (a -> b -> r) -> r }

tuple :: a -> b -> TupleK a b
tuple a b = TupleK $ \f -> f a b

fstK :: TupleK a b -> a
fstK a = unTupleK a $ \x _ -> x

sndK :: TupleK a b -> b
sndK a = unTupleK a $ \_ y -> y

toTupleK :: (a, b) -> TupleK a b
toTupleK (a, b) = tuple a b

fromTupleK :: TupleK a b -> (a, b)
fromTupleK a = unTupleK a (,)

swapK :: TupleK a b -> TupleK b a
swapK a = unTupleK a $ \x y -> tuple y x

instance Bifunctor (->) (->) (->) TupleK where
  bimap f g t = unTupleK t $ \x y -> tuple (f x) (g y)

instance Tensor (->) TupleK where
  type Unit TupleK = ()
  {-# inline assoc #-}
  assoc a = unTupleK a $ \x y -> unTupleK x $ \z w -> tuple z (tuple w y)
  {-# inline deassoc #-}
  deassoc a = unTupleK a $ \x y -> unTupleK y $ \z w -> tuple (tuple x z) w
  {-# inline unitLeftTo #-}
  unitLeftTo = sndK
  {-# inline unitLeftFrom #-}
  unitLeftFrom a = tuple () a
  {-# inline unitRightTo #-}
  unitRightTo = fstK
  {-# inline unitRightFrom #-}
  unitRightFrom a = tuple a ()

instance Bifunctor (->) (->) (->) (,) where
  bimap f g (a, b) = (f a, g b)

instance Tensor (->) (,) where
  type Unit (,) = ()

  {-# inline assoc #-}
  assoc ((a, b), c) = (a, (b, c))

  {-# inline deassoc #-}
  deassoc (a, (b, c)) = ((a, b), c)

  {-# inline unitLeftTo #-}
  unitLeftTo ((), a) = a
  {-# inline unitLeftFrom #-}
  unitLeftFrom = (,) ()

  {-# inline unitRightTo #-}
  unitRightTo (a, ()) = a
  {-# inline unitRightFrom #-}
  unitRightFrom a = (a, ())


---- Optics ----

newtype Optic k p s t a b
  = Optic
  { unOptic
    -- forall x. Optic (s -> (,)    a x) ((,)       b x -> t)
    -- forall x. Optic (s -> Either a x) (Either    b x -> t)
    --
    -- forall x. Optic (s `k` tensor a x) (tensor b x `k` t)
    --
    -- We can't do 'forall x. TupleK (s -> p a x) (p b x -> t)' or something
    -- like it. This way we get true existential quantification on x
    :: forall r. (forall x. (s `k` p a x) -> (p b x `k` t) -> r) -> r
  }

{-# inline idOptic #-}
idOptic :: (Obj k a, Tensor k p) => Optic k p a a a a
idOptic = Optic $ \f -> f unitRightFrom unitRightTo

{-# inline composeOptic #-}
composeOptic
  :: Tensor k p
  => Optic k p x y a b
  -> Optic k p s t x y
  -> Optic k p s t a b
composeOptic (Optic o1) (Optic o2) =
  o1 $ \xa by ->
  o2 $ \sx yt ->
  Optic $ \f -> f (assoc . first xa . sx) (yt . first by . deassoc)

{-# inline o #-}
o
  :: Tensor k p
  => Optic k p s t x y
  -> Optic k p x y a b
  -> Optic k p s t a b
o = flip composeOptic


over :: (Obj k a, Obj k b, Tensor k p) => Optic k p s t a b -> (a `k` b) -> s `k` t
over (Optic o) m = o (\f g -> g . bimap m id . f)

set
  :: forall k p prod s t a b
   . ( StrongBifunctor k prod p
     , Tensor k p
     , Product k prod
     )
  => Optic k p s t a b
  -> prod b s `k` t
set (Optic o1) =
  o1 (\f g -> g . first fst . lstrength . intro @k @prod fst (f . snd))

---- Lenses ----

get :: (Tensor k p, Product k p) => Optic k p s t a b -> s `k` a
get (Optic o1) = o1 $ \f _ -> fst . f

lens :: (Tensor k p, Product k p) => (s `k` a) -> (p s b `k` t) -> Optic k p s t a b
lens sa sbt =
  -- Optic $ \f -> f (\s -> tuple (sa s) s) (\a -> unTupleK a $ flip sbt)
  Optic $ \f -> f (intro sa id) (sbt . prodSwap)

_1 :: (Tensor k p, Product k p) => Optic k p (p a c) (p b c) a b
_1 = lens fst (intro snd (snd . fst))

_2 :: (Tensor k p, Product k p) => Optic k p (p c a) (p c b) a b
_2 = lens snd (intro (fst . fst) snd)


---- Prisms ----

{-# inline preview #-}
preview :: (Tensor k p, Coproduct k p, Terminating k) => Optic k p s t a b -> s `k` p (Terminal k) a
preview (Optic o1) = o1 $ \f _ -> elim inr (inl . terminal) . f

review :: (Tensor k p, Coproduct k p) => Optic k p s t a b -> b `k` t
review (Optic o1) = o1 $ \_ g -> g . inl

{-# inline prism #-}
prism :: (Tensor k p, Coproduct k p) =>  (s `k` p a t) -> (b `k` t) -> Optic k p s t a b
prism pre re = Optic $ \f -> f (elim inl inr . pre) (elim re id)

{-# inline _Left #-}
_Left :: (Tensor k p, Coproduct k p) => Optic k p (p a c) (p b c) a b
_Left = prism (elim inl (inr . inr)) inl

{-# inline _Right #-}
_Right :: (Obj k b, Obj k (p c b), Tensor k p, Coproduct k p) => Optic k p (p c a) (p c b) a b
_Right = prism (elim (inr . inl) inl) inr

{-# inline _Just #-}
_Just :: (Tensor (->) p, Coproduct (->) p) => Optic (->) p (Maybe a) (Maybe b) a b
_Just = prism (maybe (inr Nothing) inl) Just

_True :: (Tensor (->) p, Coproduct (->) p) => Optic (->) p Bool Bool () ()
_True = prism (\b -> if b then inl () else inr b) (\() -> True)

_Nothing :: (Tensor (->) p, Coproduct (->) p) => Optic (->) p (Maybe a) (Maybe a) () ()
_Nothing = prism (maybe (inl ()) (inr . Just)) (\() -> Nothing)


---- Inspection Tests for fusion ----

set_left1, set_left1' :: (Prelude.Functor b, Prelude.Functor c) => Functor.Product c (Functor.Sum a b) `Arr1` Functor.Sum c b
set_left1 = set _Left
set_left1' =
  Arr1 $ \(Functor.Pair a e) ->
  case e of
    Functor.InL _ -> Functor.InL a
    Functor.InR a -> Functor.InR a
inspect ('set_left1 === 'set_left1')

set_left, set_left' :: (a, Either a b) -> Either a b
set_left = set _Left
set_left' (a, e) =
  case e of
    Left _ -> Left a
    Right a -> Right a
inspect ('set_left === 'set_left')

get_222, get_222' :: (a, (b, (c, d))) -> d
get_222 = get (_2 `o` (_2 `o` _2))
get_222' (_, (_, (_, a))) = a
inspect ('get_222 === 'get_222')

preview_LJR, preview_LJR' :: Either (Maybe (Either a b)) c -> Either () b
preview_LJR = preview (_Left `o `(_Just `o` _Right))
preview_LJR' x =
  case x of
    Left (Just (Right a)) -> Right a
    _ -> Left ()
inspect ('preview_LJR ==- 'preview_LJR')

review_LJR = review (_Left `o `(_Just `o` _Right))
review_LJR' = Left . Just . Right
inspect ('review_LJR === 'review_LJR')

set_LJR, set_LJR' :: (d, Either (Maybe (Either a b)) c) -> Either (Maybe (Either a d)) c
set_LJR = set (_Left `o `(_Just `o` _Right))
set_LJR' (b, x) =
  case x of
    Left x' ->
      case x' of
        Nothing -> Left Nothing
        Just x'' ->
          case x'' of
            Right _ -> Left (Just (Right b))
            Left a -> Left (Just (Left a))
    Right a -> Right a
inspect ('set_LJR === 'set_LJR')

{-
set_222, set_222' :: (e, (a, (b, (c, d)))) -> (a, (b, (c, e)))
set_222 = set (_2 `o` (_2 `o` _2))
set_222' (x, a) =
  case a of
    (b, c) ->
      case c of
        (d, e) ->
          case e of
            (f, _) -> (b, (d, (f, x)))
inspect ('set_222 === 'set_222')
-}

---- w00t ----