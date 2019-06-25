module Groups

-- import Pruviloj
-- import Pruviloj.Induction
-- import Language.Reflection
-- Note: rewriteWith `(eq_refl_uid {x=~(Var $ `{{userId}})})

%default total

data GroupId = MkGID Nat

Eq GroupId where
  (MkGID gid1) == (MkGID gid2) = gid1 == gid2

lemma_mkgid_inj : (MkGID gid1 = MkGID gid2) -> gid1 = gid2
lemma_mkgid_inj Refl = Refl

DecEq GroupId where
  decEq (MkGID gid1) (MkGID gid2) =
    case decEq gid1 gid2 of
      Yes Refl => Yes Refl
      No contra => No (\p => contra (lemma_mkgid_inj p))

data UserId = MkUID Nat

Eq UserId where
  (MkUID uid1) == (MkUID uid2) = uid1 == uid2

lemma_mkuid_inj : (MkUID uid1 = MkUID uid2) -> uid1 = uid2
lemma_mkuid_inj Refl = Refl

DecEq UserId where
  decEq (MkUID uid1) (MkUID uid2) =
    case decEq uid1 uid2 of
      Yes Refl => Yes Refl
      No contra => No (\p => contra (lemma_mkuid_inj p))

data Group : Type where
  MkGroup : GroupId -> (member : Maybe UserId) -> (left: Maybe Group) -> (right: Maybe Group) -> Group

data Elem : GroupId -> Group -> Type where
  ThisGroup : Elem g (MkGroup g m l r)
  LeftGroup : Elem g group -> Elem g (MkGroup h m (Just group) r)
  RightGroup : Elem g group -> Elem g (MkGroup h m l (Just group))

data ElemGroup : GroupId -> Maybe UserId -> Maybe Group -> Maybe Group -> Group -> Type where
  ThisGroup' : ElemGroup g m l r (MkGroup g m l r)
  LeftGroup' : ElemGroup g m l r group -> ElemGroup g m l r (MkGroup g' m' (Just group) r')
  RightGroup' : ElemGroup g m l r group -> ElemGroup g m l r (MkGroup g' m' l' (Just group))


data Child : (child : GroupId) -> (parent : GroupId) -> Group -> Type where
  LeftChildHere : Child child parent (MkGroup parent m (Just (MkGroup child m' l' r')) r)
  LeftChildThere : Child child parent group -> Child child parent (MkGroup parent m (Just group) r)
  RightChildHere : Child child parent (MkGroup parent m l (Just (MkGroup child m' l' r')))
  RightChildThere : Child child parent group -> Child child parent (MkGroup parent m l (Just group))

  -- LeftChildHere : Child child parent (MkGroup parent m (Just (MkGroup child m' l' r')) r)
  -- LeftChildThere : Child child parent group -> Child child parent (MkGroup parent m (Just (MkGroup child' m' (Just group) r')) r)
  -- RightChildHere : Child child parent (MkGroup parent m l (Just (MkGroup child m' l' r')))
  -- RightChildThere : Child child parent group -> Child child parent (MkGroup parent m l (Just (MkGroup child' m' l' (Just group))))

createChild : (group : Group) -> (child : GroupId) -> (parent : GroupId) -> {childElem : ElemGroup child cm cl cr group} -> {parentElem : ElemGroup parent pm pl pr group} -> Maybe (Child child parent group)
createChild (MkGroup parent pm pl pr) parent parent {childElem = ThisGroup'} {parentElem = ThisGroup'} = Nothing
createChild (MkGroup parent pm (Just (MkGroup child cm cl cr)) pr) child parent {childElem = (LeftGroup' ThisGroup')} {parentElem = ThisGroup'} =
  Just LeftChildHere
createChild group@(MkGroup parent pm (Just (MkGroup g' m' (Just left) r')) pr) child parent {childElem = (LeftGroup' (LeftGroup' y))} {parentElem = ThisGroup'} =
  -- let c = createChild (assert_smaller group left) child parent in
  -- let re = map LeftChildThere c in
  ?wat
createChild (MkGroup parent pm (Just (MkGroup g' m' l' (Just right))) pr) child parent {childElem = (LeftGroup' (RightGroup' y))} {parentElem = ThisGroup'} = ?createChild_rhs_7
createChild (MkGroup parent pm pl (Just group)) child parent {childElem = (RightGroup' x)} {parentElem = ThisGroup'} = ?createChild_rhs_6
createChild (MkGroup g' m' (Just x) r') child parent {childElem = childElem} {parentElem = (LeftGroup' y)} = ?createChild_rhs_2
createChild (MkGroup g' m' l' (Just x)) child parent {childElem = childElem} {parentElem = (RightGroup' y)} = ?createChild_rhs_3

-- createChild (MkGroup parent m l r) parent parent {childElem = ThisGroup} {parentElem = ThisGroup} = Nothing -- Parent and child are the same, should prevent it somehow
-- createChild (MkGroup parent m (Just (MkGroup child m' l' r')) r) child parent {childElem = (LeftGroup ThisGroup)} {parentElem = ThisGroup} = Just LeftChildHere
-- createChild fullGroup@(MkGroup parent m (Just group@(MkGroup child' m' (Just l') r')) r) child parent {childElem = (LeftGroup (LeftGroup childElem'))} {parentElem = ThisGroup} =
--   let c = createChild l' child parent in
--   let c = createChild (assert_smaller fullGroup group) child parent in
--   -- let cc = createChild l' child parent {childElem = LeftGroup $ LeftGroup childElem'} in
--   let re = map LeftChildThere c in
--   ?wat
-- createChild (MkGroup parent m (Just (MkGroup h x l (Just y))) r) child parent {childElem = (LeftGroup (RightGroup z))} {parentElem = ThisGroup} = ?wat_3
-- createChild (MkGroup parent m l (Just group)) child parent {childElem = (RightGroup x)} {parentElem = ThisGroup} = ?createChild_rhs_6
-- createChild (MkGroup h m (Just x) r) child parent {childElem = childElem} {parentElem = (LeftGroup y)} = ?createChild_rhs_2
-- createChild (MkGroup h m l (Just x)) child parent {childElem = childElem} {parentElem = (RightGroup y)} = ?createChild_rhs_3

-- createChild (MkGroup parent m l r) parent parent {childElem = ThisGroup} {parentElem = ThisGroup} = Nothing -- Parent and child are the same, should prevent it somehow
-- createChild (MkGroup parent m (Just (MkGroup child member left right)) r) child parent {childElem = (LeftGroup ThisGroup)} {parentElem = ThisGroup} = Just LeftChildHere
-- createChild (MkGroup parent m (Just (MkGroup child' member (Just group@(MkGroup y z left w)) right)) r) child parent {childElem = (LeftGroup (LeftGroup x))} {parentElem = ThisGroup} = -- ?wat_1
  -- let c = createChild group child parent in
  -- map LeftChildThere c

  -- ?wat

--   -- map LeftChildThere (createChild group child parent) -- {childElem = LeftGroup x} {parentElem = LeftGroup ThisGroup})
-- createChild (MkGroup parent m (Just (MkGroup y member left (Just group))) r) child parent {childElem = (LeftGroup (RightGroup x))} {parentElem = ThisGroup} = ?wat_3
-- createChild (MkGroup parent m l (Just group)) child parent {childElem = (RightGroup x)} {parentElem = ThisGroup} = ?createChild_rhs_6
-- createChild (MkGroup h m (Just x) r) child parent {childElem = childElem} {parentElem = (LeftGroup y)} = ?createChild_rhs_2
-- createChild (MkGroup h m l (Just x)) child parent {childElem = childElem} {parentElem = (RightGroup y)} = ?createChild_rhs_3

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
      case createElem left gid of
        Nothing =>
          case createElem right gid of
            Nothing => Nothing
            Just elem => Just (RightGroup elem)
        Just elem => Just (LeftGroup elem)

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




      {-
data HasLeftChild : Group -> GroupId -> Type where
  MkHasLeftChild : HasLeftChild (MkGroup gid member (Just (MkGroup lGid lMember lLeft lRight)) right) lGid

leftChild : (group : Group) -> HasLeftChild group leftId -> Group
leftChild (MkGroup gid member (Just left@(MkGroup lGid lMember lLeft lRight)) right) MkHasLeftChild = left

data HasRightChild : Group -> GroupId -> Type where
  MkHasRightChild : HasRightChild (MkGroup gid member left (Just (MkGroup rGid rMember rLeft rRight))) rGid

rightChild : (group : Group) -> HasRightChild group rightId -> Group
rightChild (MkGroup gid member left (Just right@(MkGroup rGid rMember rLeft rRight))) MkHasRightChild = right

data HasDirectAccess : GroupId -> UserId -> Group -> Type where
  MkDirectAccess : HasDirectAccess gid uid (MkGroup gid (Just uid) left right)

direct_access_extends_left : {groupId : GroupId}
                          -> {userId : UserId}
                          -> {group : Group}
                          -> HasDirectAccess groupId userId group
                          -> HasLeftChild group leftId
                          -> HasAccess leftId userId group
direct_access_extends_left MkDirectAccess MkHasLeftChild = AccessToParent

direct_access_extends_right : {groupId : GroupId}
                           -> {userId : UserId}
                           -> {group : Group}
                           -> HasDirectAccess groupId userId group
                           -> HasRightChild group rightId
                           -> HasAccess rightId userId group
direct_access_extends_right MkDirectAccess MkHasRightChild = AccessToParent
                          -}