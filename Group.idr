module Groups

%default total
%access public export

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
