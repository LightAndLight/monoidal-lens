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

{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -O -fplugin Test.Inspection.Plugin #-}

module Monoidal where

import Prelude hiding (id, (.), Functor(..), const, uncurry, fst, snd, curry)
import Data.Kind
import Data.Void
import Test.Inspection

instance Category (->) where
  id = \a -> a
  (.) = \f g x -> f (g x)

class Category (arr :: k -> k -> Type) where
  id :: a `arr` a
  (.) :: b `arr` c -> a `arr` b -> a `arr` c

class Category (arr :: k -> k -> Type) => Product arr (p :: k -> k -> k) | p -> arr where
  fst :: p a b `arr` a
  snd :: p a b `arr` b
  intro
    :: y `arr` a
    -> y `arr` b
    -> y `arr` p a b

prodAssoc :: Product arr p => p a (p b c) `arr` p (p a b) c
prodAssoc = intro (intro fst (fst . snd)) (snd . snd)

prodSwap :: Product arr p => p a b `arr` p b a
prodSwap = intro snd fst

class Category (arr :: k -> k -> Type) => Coproduct arr (p :: k -> k -> k) | p -> arr where
  inl :: a `arr` p a b
  inr :: b `arr` p a b
  elim
    :: a `arr` y
    -> b `arr` y
    -> p a b `arr` y

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

powerOfOne_to :: (Terminating arr, Exponential arr p e) => e (Terminal arr) a `arr` Terminal arr
powerOfOne_to = terminal

powerOfOne_from :: (Terminating arr, Exponential arr p e) => Terminal arr `arr` e (Terminal arr) a
powerOfOne_from = curry fst

firstPower_to :: forall a arr p e. (Terminating arr, Exponential arr p e) => e a (Terminal arr) `arr` a
firstPower_to = apply . intro id terminal

firstPower_from :: forall a arr p e. (Terminating arr, Exponential arr p e) => a `arr` e a (Terminal arr)
firstPower_from = curry fst

expProd_to :: forall arr p e z y x. Exponential arr p e => e (e z y) x `arr` e z (p y x)
expProd_to =
  curry $
  apply . intro @arr @p (apply . fst) snd .
  prodAssoc . intro fst (prodSwap . snd)

expProd_from :: forall arr p e z y x. Exponential arr p e => e z (p y x) `arr` e (e z y) x
expProd_from = _

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

class Tensor arr t => Symmetric arr (t :: k -> k -> k) where
  swap :: t a b `arr` t b a

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
  assoc ((a, b), c) = (a, (b, c))

  deassoc (a, (b, c)) = ((a, b), c)

  unitLeftTo ((), a) = a
  unitLeftFrom = (,) ()

  unitRightTo (a, ()) = a
  unitRightFrom a = (a, ())


---- Optics ----

newtype Optic k p s t a b
  = Optic
  { unOptic
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

set :: forall k p prod e s t a b. (Symmetric k p, Exponential k prod e) => Optic k p s t a b -> prod b s `k` t
-- set (Optic o1) b = o1 $ \f g -> g . first (const b) . f
set (Optic o1) =
  o1 (\f g -> _ . intro @k @prod fst (f . snd))

{-

---- Lenses ----

type Lens = Optic TupleK

get :: Lens s t a b -> s -> a
get (Optic o1) s = o1 $ \f _ -> fstK (f s)

lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens sa sbt =
  Optic $ \f -> f (\s -> tuple (sa s) s) (\a -> unTupleK a $ flip sbt)

_1 :: Lens (a, c) (b, c) a b
_1 = lens fst (\(_, b) a -> (a, b))

_2 :: Lens (c, a) (c, b) a b
_2 = lens snd (\(a, _) b -> (a, b))


---- Prisms ----

type Prism = Optic EitherK

preview :: Prism s t a b -> s -> Maybe a
preview (Optic o1) = o1 $ \f _ -> (\a -> unEitherK a Just (const Nothing)) . f

review :: Prism s t a b -> b -> t
review (Optic o1) = o1 $ \_ g -> g . left

prism :: (s -> Either a t) -> (b -> t) -> Prism s t a b
prism pre re = Optic $ \f -> f (either left right . pre) (\a -> unEitherK a re id)

_Left :: Prism (Either a c) (Either b c) a b
_Left = prism (either Left (Right . Right)) Left

_Right :: Prism (Either c a) (Either c b) a b
_Right = prism (either (Right . Left) Left) Right

_Just :: Prism (Maybe a) (Maybe b) a b
_Just = prism (maybe (Right Nothing) Left) Just

_True :: Prism Bool Bool () ()
_True = prism (\b -> if b then Left () else Right b) (\() -> True)

_Nothing :: Prism (Maybe a) (Maybe a) () ()
_Nothing = prism (maybe (Left ()) (Right . Just)) (\() -> Nothing)


---- Inspection Tests for fusion ----

get_222 = get (_2 `o` (_2 `o` _2))
get_222' (_, (_, (_, a))) = a

inspect ('get_222 === 'get_222')


set_222 = set (_2 `o` (_2 `o` _2))
-- which is preferable?
set_222' d (a, x) = (a, case x of; (b, x') -> (b, case x' of; (c, _) -> (c, d)))
set_222'' d (a, (b, (c, _))) = (a, (b, (c, d)))

inspect ('set_222 === 'set_222')


preview_LJR = preview (_Left `o `(_Just `o` _Right))
preview_LJR' x =
  case x of
    Left (Just (Right a)) -> Just a
    _ -> Nothing

inspect ('preview_LJR === 'preview_LJR')


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