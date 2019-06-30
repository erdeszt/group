module GroupElem

import Group

%default total
%access public export

data Elem : GroupId -> Group -> Type where
  ThisGroup : Elem g (MkGroup g m l r)
  LeftGroup : Elem g group -> Elem g (MkGroup h m (Just group) r)
  RightGroup : Elem g group -> Elem g (MkGroup h m l (Just group))

createElem : (group : Group) -> (groupId : GroupId) -> Maybe (Elem groupId group)
createElem (MkGroup currentGid member Nothing Nothing) gid =
  case decEq currentGid gid of
    Yes Refl => Just ThisGroup
    No contra => Nothing
createElem (MkGroup currentGid member Nothing (Just right)) gid =
  case decEq currentGid gid of
    Yes Refl => Just ThisGroup
    No contra => map RightGroup (createElem right gid)
createElem (MkGroup currentGid member (Just left) Nothing) gid =
  case decEq currentGid gid of
    Yes Refl => Just ThisGroup
    No contra => map LeftGroup (createElem left gid)
createElem (MkGroup currentGid member (Just left) (Just right)) gid =
  case decEq currentGid gid of
    Yes Refl => Just ThisGroup
    No contra =>
      map LeftGroup (createElem left gid) <|> map RightGroup (createElem right gid)