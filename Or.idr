module Or

import Bifunctor

%access public export

data Or : Type -> Type -> Type where
  OnlyLeft : a -> Or a b
  OnlyRight : b -> Or a b
  Both : a -> b -> Or a b

Bifunctor Or where
  bimap f g (OnlyLeft x) = OnlyLeft (f x)
  bimap f g (OnlyRight x) = OnlyRight (g x)
  bimap f g (Both x y) = Both (f x) (g y)

VerifiedBifunctor Or where
  bifunctorIdentity (OnlyLeft _) = Refl
  bifunctorIdentity (OnlyRight _) = Refl
  bifunctorIdentity (Both _ _) = Refl

  bifunctorComposition (OnlyLeft _) _ _ _ _ = Refl
  bifunctorComposition (OnlyRight _) _ _ _ _ = Refl
  bifunctorComposition (Both _ _) _ _ _ _ = Refl
