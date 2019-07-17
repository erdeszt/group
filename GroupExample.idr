module Main

import Group
import GroupAccess
import GroupApi
import GroupChild
import GroupElem

exampleGroupTree : Group
exampleGroupTree =
  MkGroup (MkGID 1) Nothing
    (Just (MkGroup (MkGID 2) Nothing
      (Just (MkGroup (MkGID 4) Nothing
        (Just (MkGroup (MkGID 8) Nothing
          Nothing
          Nothing
        ))
        (Just (MkGroup (MkGID 9) Nothing
          Nothing
          Nothing
        ))
      ))
      (Just (MkGroup (MkGID 5) Nothing
        Nothing
        Nothing
      ))
    ))
    (Just (MkGroup (MkGID 3) Nothing
      (Just (MkGroup (MkGID 6) Nothing
        Nothing
        Nothing
      ))
      (Just (MkGroup (MkGID 7) Nothing
        Nothing
        Nothing
      ))
    ))

main : IO ()
main = do
  let elem2 = createElem' exampleGroupTree (MkGID 2)
  let elem4 = createElem' exampleGroupTree (MkGID 4)
  let elem8 = createElem' exampleGroupTree (MkGID 8)
  let child4Of2 = createChild' elem4 elem2
  let child8Of4 = createChild' elem8 elem4
  let child8Of2 = lemma_child_trans child4Of2 child8Of4
  let (treeWAccessToElem2ForUser1 ** (elem2', userHasAccessTo2)) = grant exampleGroupTree elem2 (MkUID 1)
  putStrLn (showChild child4Of2)
  putStrLn (showChild child8Of4)
  putStrLn (showChild child8Of2)
  printLn elem2
  putStrLn (showHasAccess userHasAccessTo2)