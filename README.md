Lisp style alists for idris2

    λΠ> Data.AList.remove "yo" $ Data.AList.replace "hi" "there" $ addIfUnique "hello" "dude" $ addIfUnique "yo" "man" $ addIfUnique "hi" "fren" Data.AList.empty
    MkDPair [("hello", "dude"), ("hi", "there")] Refl

The proof that these lists carry is:

    keyInList : Eq a => a -> List (Pair a b) -> Bool
    keyInList k [] = False
    keyInList k ((k1, v1) :: others) =
      if k == k1 then
        True
      else
        keyInList k others

    allKeysUniqueInList : Eq a => List (Pair a b) -> Bool
    allKeysUniqueInList [] = True
    allKeysUniqueInList ((k, v) :: others) =
      let
        headIsUnique = not (keyInList k others)
        tailsAreUnique = allKeysUniqueInList others
      in
      tailsAreUnique && headIsUnique

I'm hoping both the library itself and the ratty beginner code might be of benefit to others
as I feel like I've reached an intermediate stage in my ability to provide data with proofs.
