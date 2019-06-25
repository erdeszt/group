module ListCondIdx

import Data.So
import Data.Nat.Parity

data Find : (a -> Bool) -> List a -> Type where
  FoundHere : (prf : So (p x)) -> Find p (x :: xs)
  FoundThere : Find p xs -> Find p (y :: xs)

find : (p : a -> Bool) -> (xs : List a) -> Maybe (Find p xs)
find p [] = Nothing
find p (x :: xs) =
  case decEq (p x) True of
    Yes prf => Just (FoundHere (rewrite prf in Oh))
    No _ => map FoundThere (find p xs)

