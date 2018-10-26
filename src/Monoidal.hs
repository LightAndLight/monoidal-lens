{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language DataKinds #-}
{-# language ConstraintKinds, GADTs #-}
{-# language MultiParamTypeClasses, FunctionalDependencies #-}
{-# language TypeFamilies #-}
{-# language TypeOperators #-}
{-# language RankNTypes #-}
{-# language PolyKinds #-}
{-# language TypeInType #-}
{-# language ScopedTypeVariables #-}
{-# language TypeApplications #-}

{-# language TemplateHaskell #-}
{-# OPTIONS_GHC -O -fplugin Test.Inspection.Plugin #-}

module Monoidal where

import Prelude hiding (id, (.), Functor(..), const, uncurry, fst, snd, curry)
import Unsafe.Coerce
import Data.Coerce
import Data.Kind
import Data.Void
import Test.Inspection

instance Category (->) where
  id = \a -> a
  (.) = \f g x -> f (g x)

class Category (arr :: k -> k -> Type) where
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

expProd_to :: forall arr p e z y x. Exponential arr p e => e (e z y) x `arr` e z (p y x)
expProd_to =
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

class (Category p, Category q, Category r) => Bifunctor p q r (f :: i -> j -> k)
  | p r -> q, q r -> p -- no idea if these are correct
  where
  bimap
    :: (a `p` b)
    -> (c `q` d)
    -> (f a c `r` f b d)

-- |
-- Take an (end) functor  f : C * C -> C
-- if C has products, then C * C is a subcategory of of C (?)
--
-- so instead consider the functor   f : C -> C
-- this functor is strong w.r.t a tensor   t : (C * C) -> C if
-- there's a natural transformation from   a * f(b) -> f(a * b)
class (Product k p, Tensor k p, Bifunctor k k k f) => StrongBifunctor k p f where
  lstrength :: p a (f b c) `k` f (p a b) c
  rstrength :: p a (f b c) `k` f b (p a c)

instance StrongBifunctor (->) (,) (,) where
  lstrength = deassoc
  rstrength = intro (fst . snd) (intro fst (snd . snd))

first :: Bifunctor p q r f => p a b -> f a c `r` f b c
first f = bimap f id

second :: Bifunctor p q r f => q a b -> f c a `r` f c b
second f = bimap id f

instance Bifunctor (->) (->) (->) Either where
  bimap f _ (Left a) = Left (f a)
  bimap _ g (Right a) = Right (g a)

class Bifunctor arr arr arr t => Tensor arr (t :: k -> k -> k) where
  type Unit t :: k
  assoc :: t (t a b) c `arr` t a (t b c)
  deassoc :: t a (t b c) `arr` t (t a b) c

  unitLeftTo :: t (Unit t) a `arr` a
  unitLeftFrom :: a `arr` t (Unit t) a

  unitRightTo :: t a (Unit t) `arr` a
  unitRightFrom :: a `arr` t a (Unit t)

-- left :: Bifunctor p q r t => p a b -> t a c `arr` t b c
-- left = _

instance Tensor (->) Either where
  type Unit Either = Void
  assoc (Left (Left a)) = Left a
  assoc (Left (Right a)) = Right (Left a)
  assoc (Right a) = Right (Right a)

  deassoc (Left a) = Left (Left a)
  deassoc (Right (Left a)) = Left (Right a)
  deassoc (Right (Right a)) = Right a

  unitLeftTo (Right a) = a
  unitLeftFrom = Right

  unitRightTo (Left a) = a
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
idOptic :: Tensor k p => Optic k p a a a a
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

set
  :: forall k p prod s t a b
   . ( StrongBifunctor k prod p
     , Tensor k p
     , Product k prod
     )
  => Optic k p s t a b
  -> prod b s `k` t
set (Optic o1) = o1 (\f g -> g . first fst . lstrength . intro @k @prod fst (f . snd))

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
prism :: (Tensor k p, Coproduct k p) => (s `k` p a t) -> (b `k` t) -> Optic k p s t a b
prism pre re = Optic $ \f -> f (elim inl inr . pre) (elim re id)

{-# inline _Left #-}
_Left :: (Tensor k p, Coproduct k p) => Optic k p (p a c) (p b c) a b
_Left = prism (elim inl (inr . inr)) inl

{-# inline _Right #-}
_Right :: (Tensor k p, Coproduct k p) => Optic k p (p c a) (p c b) a b
_Right = prism (elim (inr . inl) inl) inr

{-# inline _Just #-}
_Just :: (Tensor (->) p, Coproduct (->) p) => Optic (->) p (Maybe a) (Maybe b) a b
_Just = prism (maybe (inr Nothing) inl) Just

_True :: (Tensor (->) p, Coproduct (->) p) => Optic (->) p Bool Bool () ()
_True = prism (\b -> if b then inl () else inr b) (\() -> True)

_Nothing :: (Tensor (->) p, Coproduct (->) p) => Optic (->) p (Maybe a) (Maybe a) () ()
_Nothing = prism (maybe (inl ()) (inr . Just)) (\() -> Nothing)


---- Inspection Tests for fusion ----

get_222, get_222' :: (a, (b, (c, d))) -> d
get_222 = get (_2 `o` (_2 `o` _2))
get_222' (_, (_, (_, a))) = a

inspect ('get_222 === 'get_222')

set_222, set_222' :: (e, (a, (b, (c, d)))) -> (a, (b, (c, e)))
set_222 = set (_2 `o` (_2 `o` _2))
-- which is preferable?
set_222' (d, (a, x)) = (a, case x of; (b, x') -> (b, case x' of; (c, _) -> (c, d)))
set_222'' (d, (a, (b, (c, _)))) = (a, (b, (c, d)))

-- inspect ('set_222 === 'set_222')
inspect ('set_222 === 'set_222'')


preview_LJR, preview_LJR' :: Either (Maybe (Either a b)) c -> Either () b
preview_LJR = preview (_Left `o `(_Just `o` _Right))
preview_LJR' x =
  case x of
    Left (Just (Right a)) -> Right a
    _ -> Left ()

inspect ('preview_LJR === 'preview_LJR')


{-
review_LJR = review (_Left `o `(_Just `o` _Right))
review_LJR' = Left . Just . Right

inspect ('review_LJR === 'review_LJR')


set_LJR = set (_Left `o `(_Just `o` _Right))
set_LJR' b x =
  case x of
    Left x' ->
      case x' of
        Nothing -> Left Nothing
        Just x'' ->
          case x'' of
            Right _ -> Left (Just (Right b))
            Left a -> Left (Just (Left a))
    Right a -> Right a
set_LJR'' a (Left (Just (Right _))) = Left . Just . Right $ a
set_LJR'' _ a = a

inspect ('set_LJR === 'set_LJR')

---- w00t ----

main = do
  print . fst $ set_222' 'b' ('a', undefined)
  print $ set_222' 'b' ('a', ('b', ('c', 'd')))
  print . fst $ set_222'' 'b' ('a', undefined)
-}
