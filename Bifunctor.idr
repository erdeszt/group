-- NOTE: From: https://github.com/japesinator/Idris-Bifunctors/blob/master/src/Data/Bifunctor.idr add as dep
module Bifunctor

%access public export

||| Bifunctors
||| @p The action of the Bifunctor on pairs of objects
interface Bifunctor (p : Type -> Type -> Type) where
  ||| The action of the Bifunctor on pairs of morphisms
  |||
  ||| ````idris example
  ||| bimap (\x => x + 1) reverse (1, "hello") == (2, "olleh")
  ||| ````
  |||
  bimap : (a -> b) -> (c -> d) -> p a c -> p b d
  bimap f g = first f . second g

  ||| The action of the Bifunctor on morphisms pertaining to the first object
  |||
  ||| ````idris example
  ||| first (\x => x + 1) (1, "hello") == (2, "hello")
  ||| ````
  |||
  first : (a -> b) -> p a c -> p b c
  first = flip bimap id

  ||| The action of the Bifunctor on morphisms pertaining to the second object
  |||
  ||| ````idris example
  ||| second reverse (1, "hello") == (1, "olleh")
  ||| ````
  |||
  second : (a -> b) -> p c a -> p c b
  second = bimap id

interface Bifunctor p => VerifiedBifunctor (p : Type -> Type -> Type) where
  bifunctorIdentity : (x : p a b) -> bimap Basics.id Basics.id x = x
  bifunctorComposition : (x : p a d) -> (f : a -> b) -> (g : b -> c) ->
                          (h : d -> e) -> (i : e -> a') ->
                          (bimap (g . f) (i . h) x) =
                          (bimap g i . bimap f h) x

implementation Bifunctor Either where
  bimap f _ (Left  a) = Left  $ f a
  bimap _ g (Right b) = Right $ g b

implementation VerifiedBifunctor Either where
  bifunctorIdentity    (Left  _)         = Refl
  bifunctorIdentity    (Right _)         = Refl
  bifunctorComposition (Left  _) _ _ _ _ = Refl
  bifunctorComposition (Right _) _ _ _ _ = Refl

implementation Bifunctor Pair where
  bimap f g (a, b) = (f a, g b)

implementation VerifiedBifunctor Pair where
  bifunctorIdentity    (_, _)         = Refl
  bifunctorComposition (_, _) _ _ _ _ = Refl