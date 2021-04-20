module Data.AList

import Data.Bool.DecBool
import Decidable.Equality
import Prelude.Uninhabited

||| Check whether a key is in a list.  Exposed so that proofs can use it in various ways.
public export
keyInList : Eq a => a -> List (Pair a b) -> Bool
keyInList k [] = False
keyInList k ((k1, v1) :: others) =
  if k == k1 then
    True
  else
    keyInList k others

||| Check whether all keys are unique in a list.  Exposed so that proofs can use it in various ways.
public export
allKeysUniqueInList : Eq a => List (Pair a b) -> Bool
allKeysUniqueInList [] = True
allKeysUniqueInList ((k, v) :: others) =
  let
    headIsUnique = not (keyInList k others)
    tailsAreUnique = allKeysUniqueInList others
  in
  tailsAreUnique && headIsUnique

kvCons : a -> b -> List (Pair a b) -> List (Pair a b)
kvCons k v l = (k,v) :: l

appendBreak : Eq a => (k : a) -> (v : b) -> (l : List (Pair a b)) -> (p : allKeysUniqueInList l = True) -> (DPair (List (Pair a b)) (\l => allKeysUniqueInList l = True))
appendBreak k v l p with (decEq (keyInList k l) True)
  appendBreak k v l p | Yes prf = (l ** p)
  appendBreak k v l p | No contra =
    let
      cproof = invertContraBool (keyInList k l) True contra
    in
    (kvCons k v l ** outProof k l p cproof)
    where
      outProof : (k : a) -> (l : List (Pair a b)) -> (p : allKeysUniqueInList l = True) -> (kp : not (keyInList k l) = True) -> (allKeysUniqueInList l && not (keyInList k l) = True)
      outProof k l p kp =
        rewrite kp in
        rewrite p in
        Refl

||| Prove that a list contains only unique keys, returning a maybe of the proved list type.
public export
proveList : Eq a => (l : List (Pair a b)) -> Maybe (DPair (List (Pair a b)) (\l => allKeysUniqueInList l = True))
proveList l with (decEq (allKeysUniqueInList l) True)
  proveList l | Yes prf = Just (l ** prf)
  proveList l | No _ = Nothing

||| Insert a new key only if it doesn't already appear in the list.
public export
addIfUnique : Eq a => (k : a) -> (v : b) -> (l : DPair (List (Pair a b)) (\l => allKeysUniqueInList l = True)) -> DPair (List (Pair a b)) (\l => allKeysUniqueInList l = True)
addIfUnique k v (l ** p) = appendBreak k v l p

public export
simpleTail : List x -> List x
simpleTail [] = []
simpleTail (hd :: tl) = tl

anyAndNotTrueIsFalse : (a : Bool) -> (a && not True) = False
anyAndNotTrueIsFalse False = Refl
anyAndNotTrueIsFalse True = Refl

selectAFromANBTrue : (a : Bool) -> (b : Bool) -> (a && b) = True -> a = True
selectAFromANBTrue False False prf impossible
selectAFromANBTrue False True prf impossible
selectAFromANBTrue True False prf = Refl
selectAFromANBTrue True True prf = Refl

selectBFromANBTrue : (a : Bool) -> (b : Bool) -> (a && b) = True -> b = True
selectBFromANBTrue False False prf impossible
selectBFromANBTrue False True prf impossible
selectBFromANBTrue True False prf impossible
selectBFromANBTrue True True prf = Refl

aAndProvablyTrueIsA : (a : Bool) -> (b : Bool) -> (b = True) -> (a && b) = a
aAndProvablyTrueIsA False False prf = Refl
aAndProvablyTrueIsA False True prf = Refl
aAndProvablyTrueIsA True False prf impossible
aAndProvablyTrueIsA True True prf = Refl

contradiction : (a : Bool) -> a = False -> a = True -> Void
contradiction False p1 p2 impossible
contradiction True p1 p2 impossible

||| Given a list for which uniqueness holds, return a proof that uniqueness holds for its tail.
public export
largerListUniqueMeansSublistUnique :
  Eq a =>
    (l : List (Pair a b)) ->
    (prf : allKeysUniqueInList l = True) ->
    (allKeysUniqueInList (simpleTail l) = True)
largerListUniqueMeansSublistUnique [] prf = Refl
largerListUniqueMeansSublistUnique (Prelude.Types.(::) hd []) prf = Refl
largerListUniqueMeansSublistUnique (Prelude.Types.(::) hd (Prelude.Types.(::) (hk,hv) tt)) prf with (decEq (keyInList hk tt) True)
  largerListUniqueMeansSublistUnique (Prelude.Types.(::) hd (Prelude.Types.(::) (hk,hv) tt)) prf | Yes found  =
    let
      proved : ((allKeysUniqueInList tt && not (keyInList hk tt)) = False)
      proved =
        let
          s = largerListUniqueMeansSublistUnique (Prelude.Types.(::) hd (Prelude.Types.(::) (hk,hv) tt)) prf
        in
        rewrite found in
        rewrite anyAndNotTrueIsFalse (allKeysUniqueInList tt) in
        Refl

      stated : ((allKeysUniqueInList tt && not (keyInList hk tt)) = True)
      stated = largerListUniqueMeansSublistUnique (Prelude.Types.(::) hd (Prelude.Types.(::) (hk,hv) tt)) prf

      res : (True = False) -> Void
      res r impossible
    in
    absurd (contradiction (allKeysUniqueInList tt && not (keyInList hk tt)) proved stated)

  largerListUniqueMeansSublistUnique (Prelude.Types.(::) hd (Prelude.Types.(::) (hk,hv) tt)) prf | No contra with (decEq (allKeysUniqueInList tt) True)
    largerListUniqueMeansSublistUnique (Prelude.Types.(::) hd (Prelude.Types.(::) (hk,hv) tt)) prf | No contra | Yes p2 =
      let
        cproof = invertContraBool (keyInList hk tt) True contra
      in
      rewrite cproof in
      rewrite p2 in
      Refl
    largerListUniqueMeansSublistUnique (Prelude.Types.(::) hd (Prelude.Types.(::) (hk,hv) tt)) prf | No contra | No c2 =
      let
        cproof = invertContraBool (keyInList hk tt) True contra
        stated : (allKeysUniqueInList tt = True)
        stated =
          let
            s = largerListUniqueMeansSublistUnique (Prelude.Types.(::) hd (Prelude.Types.(::) (hk,hv) tt)) prf
          in
          rewrite sym (aAndProvablyTrueIsA (allKeysUniqueInList tt) (not (keyInList hk tt)) cproof) in
         s
      in
      rewrite cproof in
      absurd (c2 stated)

replaceBreak : Eq a => (k : a) -> (v : b) -> (l : List (Pair a b)) -> (p : allKeysUniqueInList l = True) -> (DPair (List (Pair a b)) (\l => allKeysUniqueInList l = True))
replaceBreak k v [] p = appendBreak k v [] p
replaceBreak k v ((kl,vl) :: tl) p with (decEq (k == kl) True)
  replaceBreak k v ((kl,vl) :: tl) p | Yes prf =
    (((kl,v) :: tl) ** p)

  replaceBreak k v ((kl,vl) :: tl) p | No contra =
    let
      apart = selectAFromANBTrue (allKeysUniqueInList tl) (not (keyInList kl tl)) p
      (replaced ** rproof) = replaceBreak k v tl apart
      rp1 =
        rewrite rproof in
        Refl
    in
    appendBreak kl vl replaced rp1

||| Replace an element in the list, preserving key order.  The element is added if it wasn't present.
public export
replace : Eq a => (k : a) -> (v : b) -> (l : DPair (List (Pair a b)) (\l => allKeysUniqueInList l = True)) -> DPair (List (Pair a b)) (\l => allKeysUniqueInList l = True)
replace k v (l ** p) = replaceBreak k v l p

removeBreak : Eq a => (k : a) -> (l : List (Pair a b)) -> (p : allKeysUniqueInList l = True) -> (DPair (List (Pair a b)) (\l => allKeysUniqueInList l = True))
removeBreak k [] p = ([] ** Refl)
removeBreak k ((kl,vl) :: tl) p with (decEq (k == kl) True)
  removeBreak k ((kl,vl) :: tl) p | Yes prf =
    let
      apart = selectAFromANBTrue (allKeysUniqueInList tl) (not (keyInList kl tl)) p
    in
    (tl ** apart)

  removeBreak k ((kl,vl) :: tl) p | No contra =
    let
      subproof = largerListUniqueMeansSublistUnique ((kl,vl) :: tl) p
    in
    addIfUnique kl vl (removeBreak k tl subproof)

||| Remove a key and its value from the list.  The list is unchanged if it wasn't present.
public export
remove : Eq a => (k : a) -> (l : DPair (List (Pair a b)) (\l => allKeysUniqueInList l = True)) -> DPair (List (Pair a b)) (\l => allKeysUniqueInList l = True)
remove k (l ** p) = removeBreak k l p

||| An empty list.
public export
empty : Eq a => DPair (List (Pair a b)) (\l => allKeysUniqueInList l = True)
empty = ([] ** Refl)

mergeBreak :
  Eq a =>
    (l : List (Pair a b)) ->
    (allKeysUniqueInList l = True) ->
    (DPair (List (Pair a b)) (\l => allKeysUniqueInList l = True)) ->
    (DPair (List (Pair a b)) (\l => allKeysUniqueInList l = True))
mergeBreak [] p onto = onto
mergeBreak ((k,v) :: tl) p onto =
  let
    subproof = largerListUniqueMeansSublistUnique ((k,v) :: tl) p
    (merged ** mprf) = mergeBreak tl subproof onto
  in
  replaceBreak k v merged mprf

||| For each key in a, replace in b.
public export
merge :
  Eq a =>
    (DPair (List (Pair a b)) (\l => allKeysUniqueInList l = True)) ->
    (DPair (List (Pair a b)) (\l => allKeysUniqueInList l = True)) ->
    (DPair (List (Pair a b)) (\l => allKeysUniqueInList l = True))
merge (a ** p) b = mergeBreak a p b
