module GroupApi

import Group
import GroupChild
import GroupElem

%default total
%access public export

data HasAccess : GroupId -> UserId -> Group -> Type where
  DirectAccess : HasAccess gid uid (MkGroup gid (Just uid) left right)
  AccessToParent : HasAccess gid uid (MkGroup gid' (Just uid) left right)
  AccessToLeft : HasAccess gid uid group -> HasAccess gid uid (MkGroup gid' member (Just group) right)
  AccessToRight : HasAccess gid uid group -> HasAccess gid uid (MkGroup gid' member left (Just group))

access : {groupId : GroupId}
      -> (group : Group)
      -> (elem : Elem groupId group)
      -> (userId : UserId)
      -> Maybe (HasAccess groupId userId group)
access (MkGroup groupId member left right) ThisGroup uid =
  case member of
    Nothing => Nothing
    Just mid =>
      case decEq uid mid of
        No contra => Nothing
        Yes Refl => Just DirectAccess
access (MkGroup groupId member (Just left) right) (LeftGroup leftElem) uid =
  case member of
    Nothing =>
      case access left leftElem uid of
        Nothing => Nothing
        Just leftAccess => Just (AccessToLeft leftAccess)
    Just mid =>
        case decEq uid mid of
          No contra =>
            case access left leftElem uid of
              Nothing => Nothing
              Just leftAccess => Just (AccessToLeft leftAccess)
          Yes Refl => Just AccessToParent
access (MkGroup groupId member left (Just right)) (RightGroup rightElem) uid =
  case member of
    Nothing =>
      case access right rightElem uid of
        Nothing => Nothing
        Just rightAccess => Just (AccessToRight rightAccess)
    Just mid =>
        case decEq uid mid of
          No contra =>
            case access right rightElem uid of
              Nothing => Nothing
              Just rightAccess => Just (AccessToRight rightAccess)
          Yes Refl => Just AccessToParent

grant : {groupId : GroupId}
      -> (group : Group)
      -> Elem groupId group
      -> (userId : UserId)
      -> (group' : Group ** (Elem groupId group', HasAccess groupId userId group'))
grant (MkGroup currentGid member left right) ThisGroup newMember =
  ((MkGroup currentGid (Just newMember) left right) ** (ThisGroup, DirectAccess))
grant (MkGroup currentGid member (Just left) right) (LeftGroup elem) newMember =
  case grant left elem newMember of
    (group ** (elemPrf, memberPrf)) =>
      ((MkGroup currentGid member (Just group) right) ** (LeftGroup elemPrf, AccessToLeft memberPrf))
grant (MkGroup currentGid member left (Just right)) (RightGroup elem) newMember =
  case grant right elem newMember of
    (group ** (elemPrf, memberPrf)) =>
      ((MkGroup currentGid member left (Just group)) ** (RightGroup elemPrf, AccessToRight memberPrf))


{- EXPERIMENTAL: -}

data ChildAccess : {childId : GroupId}
                -> {parentId : GroupId}
                -> {group : Group}
                -> {childElem : Elem childId group}
                -> {parentElem : Elem parentId group}
                -> {child : Child childElem parentElem}
                -> (HasAccess parentId userId group)
                -> (HasAccess childId userId group)
                -> Type
                where
  ChildAccessDirectToParent : ChildAccess DirectAccess AccessToParent
  ChildAccessToParentsParent : ChildAccess AccessToParent AccessToParent
  ChildAccessOnLeft : ChildAccess parentAccess childAccess -> ChildAccess (AccessToLeft parentAccess) (AccessToLeft childAccess)
  ChildAccessOnRight : ChildAccess parentAccess childAccess -> ChildAccess (AccessToRight parentAccess) (AccessToRight childAccess)

-- access_to_child_access : {parentId : GroupId}
--                       -> {childId : GroupId}
--                       -> {userId : UserId}
--                       -> {group : Group}
--                       -> {childElem : Elem childId group}
--                       -> {parentElem : Elem parentId group}
--                       -> {child : Child childElem parentElem}
--                       -> (parentAccess : HasAccess parentId userId group)
--                       -> ChildAccess parentAccess childAccess
-- access_to_child_access DirectAccess = ?wattt
-- access_to_child_access AccessToParent = ?watt
-- access_to_child_access (AccessToLeft x) = ?wat
-- access_to_child_access (AccessToRight x) = ?wat_4

access_extends_to_children : {childId : GroupId}
                          -> {parentId : GroupId}
                          -> {userId : UserId}
                          -> {group : Group}
                          -> {childElem : Elem childId group}
                          -> {parentElem : Elem parentId group}
                          -> {child : Child childElem parentElem}
                          -> (parentAccess : HasAccess parentId userId group)
                          -> HasAccess childId userId group
access_extends_to_children {group = (MkGroup parentId (Just userId) left right)} {child = child} DirectAccess = AccessToParent
access_extends_to_children {group = (MkGroup gid' (Just userId) left right)} {child = child} AccessToParent = AccessToParent
access_extends_to_children {group = (MkGroup parentId member (Just x) right)} {child = ChildOnLeft} {childElem = (LeftGroup child)} {parentElem = pe@ThisGroup} (AccessToLeft y) =
  let rec = access_extends_to_children {childElem = child} {parentElem = ThisGroup} {group=x} y in
  let ret = AccessToLeft rec in
  ret
access_extends_to_children {group = (MkGroup parentId member (Just x) (Just group))} {child = ChildOnRight} {childElem = (RightGroup child)} {parentElem = ThisGroup} (AccessToLeft y) = ?wat_2
access_extends_to_children {group = (MkGroup parentId member (Just x) right)} {child = (PrefixLeft z)} {childElem = (LeftGroup parent)} {parentElem = (LeftGroup child)} (AccessToLeft y) = ?wat_3
access_extends_to_children {group = (MkGroup parentId member (Just x) (Just group))} {child = (PrefixRight z)} {childElem = (RightGroup parent)} {parentElem = (RightGroup child)} (AccessToLeft y) = ?wat_5
  -- let rec = access_extends_to_children {childElem = ?wat} {group=x} y in
  -- let ret = AccessToLeft rec in
  -- ret
access_extends_to_children {group = (MkGroup gid' member left (Just x))} {child = child} (AccessToRight y) = ?wat_4

-- access_extends_to_children (MkGroup parentId (Just userId) left right) DirectAccess = AccessToParent
-- access_extends_to_children (MkGroup gid' (Just userId) left right) AccessToParent = AccessToParent

-- access_extends_to_children (MkGroup parentId member (Just x) right) (AccessToLeft y) = AccessToLeft ?wat

-- data HasLeftChild : Group -> GroupId -> Type where
--   MkHasLeftChild : HasLeftChild (MkGroup gid member (Just (MkGroup lGid lMember lLeft lRight)) right) lGid

-- leftChild : (group : Group) -> HasLeftChild group leftId -> Group
-- leftChild (MkGroup gid member (Just left@(MkGroup lGid lMember lLeft lRight)) right) MkHasLeftChild = left

-- data HasRightChild : Group -> GroupId -> Type where
--   MkHasRightChild : HasRightChild (MkGroup gid member left (Just (MkGroup rGid rMember rLeft rRight))) rGid

-- rightChild : (group : Group) -> HasRightChild group rightId -> Group
-- rightChild (MkGroup gid member left (Just right@(MkGroup rGid rMember rLeft rRight))) MkHasRightChild = right

-- data HasDirectAccess : GroupId -> UserId -> Group -> Type where
--   MkDirectAccess : HasDirectAccess gid uid (MkGroup gid (Just uid) left right)

-- direct_access_extends_left : {groupId : GroupId}
--                           -> {userId : UserId}
--                           -> {group : Group}
--                           -> HasDirectAccess groupId userId group
--                           -> HasLeftChild group leftId
--                           -> HasAccess leftId userId group
-- direct_access_extends_left MkDirectAccess MkHasLeftChild = AccessToParent

-- direct_access_extends_right : {groupId : GroupId}
--                            -> {userId : UserId}
--                            -> {group : Group}
--                            -> HasDirectAccess groupId userId group
--                            -> HasRightChild group rightId
--                            -> HasAccess rightId userId group
-- direct_access_extends_right MkDirectAccess MkHasRightChild = AccessToParent
