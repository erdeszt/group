module GroupApi

import Group
import GroupAccess
import GroupChild
import GroupElem

%default total
%access public export

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

-- This definition is definitely wrong because it's not recursive
-- Problem: can't add a recursive arg to ChildAccessToLeft because
--          it prevents unification of childElem's group and parentElem's group
-- Idea: Missing link between HasAccess and Child, no way to know
--       that group that you have access through(parent of parentElem) is
--       the parent of Child!
-- Idea: Add group to the relation to express the structure
--       or build lower level lemmas to help rewrite the high level operations
data ChildAccess : {childId : GroupId}
                -> {parentId : GroupId}
                -> {group : Group}
                -> {childElem : Elem childId group}
                -> {parentElem : Elem parentId group}
                -> {child : Child childElem parentElem}
                -> (HasAccess parentId userId group)
                -> Child childElem parentElem
                -> Type
                where
    ChildAccessDirectToParent : ChildAccess DirectAccess child
    ChildAccessToParent : ChildAccess AccessToParent child
    ChildAccessToLeft : ChildAccess (AccessToLeft parentAccess) child
    ChildAccessToRight : ChildAccess (AccessToRight parentAccess) child

access_to_child_access : {parentId : GroupId}
                      -> {childId : GroupId}
                      -> {userId : UserId}
                      -> {group : Group}
                      -> {childElem : Elem childId group}
                      -> {parentElem : Elem parentId group}
                      -> (child : Child childElem parentElem)
                      -> (parentAccess : HasAccess parentId userId group)
                      -> ChildAccess parentAccess childAccess
access_to_child_access child DirectAccess = ChildAccessDirectToParent
access_to_child_access child AccessToParent = ChildAccessToParent
access_to_child_access child (AccessToLeft x) = ChildAccessToLeft
access_to_child_access child (AccessToRight x) = ChildAccessToRight

child_access_to_access : {parentId : GroupId}
                      -> {childId : GroupId}
                      -> {userId : UserId}
                      -> {group : Group}
                      -> {childElem : Elem childId group}
                      -> {parentElem : Elem parentId group}
                      -> {child : Child childElem parentElem}
                      -> {parentAccess : HasAccess parentId userId group}
                      -> (childAccess : ChildAccess parentAccess child)
                      -> HasAccess childId userId group

access_extends_to_children : {childId : GroupId}
                          -> {parentId : GroupId}
                          -> {userId : UserId}
                          -> {group : Group}
                          -> {childElem : Elem childId group}
                          -> {parentElem : Elem parentId group}
                          -> {child : Child childElem parentElem}
                          -> (parentAccess : HasAccess parentId userId group)
                          -> HasAccess childId userId group
