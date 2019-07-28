module ListCondIdx

import Data.So
import Data.Nat.Parity

data Find : (a -> Bool) -> List a -> Type where
  FoundHere : a -> {prf : So (p x)} -> Find p (x :: xs)
  FoundThere : Find p xs -> Find p (y :: xs)

findFirst : (p : a -> Bool) -> (xs : List a) -> Maybe (Find p xs)
findFirst p [] = Nothing
findFirst p (x :: xs) =
  case decEq (p x) True of
    Yes prf => Just (FoundHere x {prf=rewrite prf in Oh})
    No _ => map FoundThere (findFirst p xs)

data ListForAll : (p : a -> Bool) -> List a -> Type where
  ListForAllEmpty : ListForAll p []
  ListForAllCons : {xs : List a} -> (x : a) -> ListForAll p xs -> {prf : So (p x)} -> ListForAll p (x :: xs)

listForAll : (p : a -> Bool) -> (xs : List a) -> Maybe (ListForAll p xs)
listForAll p [] = Just ListForAllEmpty
listForAll p (x :: xs) =
  case decEq (p x) True of
    (Yes prf) =>
      case listForAll p xs of
        Nothing => Nothing
        Just xs' => Just (ListForAllCons x xs' {prf=rewrite prf in Oh})
    (No contra) => Nothing

filter : (p : a -> Bool) -> (xs : List a) -> (ys : List a ** ListForAll p ys)
filter p [] = ([] ** ListForAllEmpty)
filter p (x :: xs) =
  case decEq (p x) True of
    (Yes prf) =>
      case ListCondIdx.filter p xs of
        (xs' ** forall) => (x :: xs' ** ListForAllCons x forall {prf=rewrite prf in Oh})
    (No contra) => ListCondIdx.filter p xs

listForAllToList : {xs : List a} -> ListForAll p xs -> List a
listForAllToList ListForAllEmpty = []
listForAllToList (ListForAllCons x xs) = x :: listForAllToList xs