module ListIndex

import Pruviloj
import Pruviloj.Induction

%default total
%language ElabReflection
%access public export

data Elem : a -> List a -> Type where
  Here  :              Elem x (x :: xs)
  There : Elem x xs -> Elem x (y :: xs)

createElem : DecEq a => (list : List a) -> (item : a) -> Maybe (Elem item list)
createElem [] _ = Nothing
createElem (x :: xs) item =
  case decEq x item of
    Yes Refl => Just Here
    No contra => map (\path => There path) (createElem xs item)

getElem : (list : List a) -> Elem item list -> a
getElem (item :: ys) Here = item
getElem (y :: ys) (There x) = getElem ys x
