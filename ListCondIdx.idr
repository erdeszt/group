module ListCondIdx

data Find : (a : Type) -> (p : a -> Type) -> List a -> (prf : Type) -> Type where
  FoundHere : Find x p (x :: xs) (p x = True)

  -- Here : Find x (x :: xs) (p x = True)