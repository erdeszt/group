module Main

import Group
import GroupAccess
import GroupApi
import GroupChild
import GroupElem


-- Example tree:
--         1
--       /   \
--      2     3
--     / \   / \
--    4   5 6   7
--   / \
--  8   9
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
  (Just exampleElem2) <- pure $ createElem exampleGroupTree (MkGID 2)
  let (tree' ** (elem2 ** accessTo2)) = grantUnchecked exampleGroupTree exampleElem2 (MkUID 1)
  (Just elem4) <- pure $ createElem tree' (MkGID 4)
  (Just elem8) <- pure $ createElem tree' (MkGID 8)
  (Just child4Of2) <- pure $ createChild elem4 elem2
  (Just child8Of4) <- pure $ createChild elem8 elem4
  let child8Of2 = lemma_child_trans child4Of2 child8Of4
  let accessTo4 = directAccessExtendsToChildren accessTo2 child4Of2
  let accessTo8 = directAccessExtendsToChildren accessTo2 child8Of2
  let accessTo8' = accessExtendsToChildren accessTo4 child8Of4
  putStrLn (showChild child4Of2)
  putStrLn (showChild child8Of4)
  putStrLn (showChild child8Of2)
  putStrLn (showHasDirectAccess accessTo2)
  putStrLn (showHasAccess accessTo4)
  putStrLn (showHasAccess accessTo8)
  putStrLn (showHasAccess accessTo8')
  pure ()
