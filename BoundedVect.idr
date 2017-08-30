module BoundedVect
import Data.Vect
import NatHelpers

%default total

||| A bounded Vect is a vector with a maximum capacity that cannot be exceeded.
|||
||| The only way to append an element to the vector is to provide a prood that
||| it's size is strictly less than it's capacity. Therefore the size of a BoundedVect
||| will always be less or equal to its maximum capacity
public export
data BoundedVect : (max, size: Nat) -> (elem : Type) -> Type where
  Nil : BoundedVect max Z elem
  Cons : (prf : size `LT` max) -> (x : elem) -> BoundedVect max size elem -> BoundedVect max (S size) elem
%name BoundedVect xs, ys, zs, ws

export
fromVect : Vect size elem -> (ok : size `LTE` max) -> BoundedVect max size elem
fromVect [] ok = []
fromVect (x :: xs) ok = Cons ok x (fromVect xs (lteSuccLeft ok))

export
fromVectAuto : Vect size elem -> {auto ok : size `LTE` max} -> BoundedVect max size elem
fromVectAuto xs {ok} = fromVect xs ok

||| attempt to append an element to a bounded vect, if the vect is at max capacity
||| return nothing, otherwise, return the new boundedVect with the same bounds
export maybeAppendBoundedVect : (x : elem) -> BoundedVect max size elem -> Maybe (BoundedVect max (S size) elem)
maybeAppendBoundedVect x xs {max} {size}  with (cmp size max)
  maybeAppendBoundedVect x xs {max = (size + (S y))} {size = size} | (CmpLT y) =
    let lte = LTESucc $ lteRightPlusNat {k = y} (size) in
      Just (Cons (lteRighPlusSuccRightSucc lte) x xs)
  maybeAppendBoundedVect x xs {max = max} {size = max} | CmpEQ = Nothing
  maybeAppendBoundedVect x xs {max = max} {size = (max + (S k))} | (CmpGT k) = Nothing

||| Appends an element to a boundedVect and increase the size of its bound
export
appendVectExtendBound : (x : elem) -> BoundedVect max size elem -> BoundedVect (S max) (S size) elem
appendVectExtendBound x [] = Cons (LTESucc LTEZero) x []
appendVectExtendBound x (Cons prf y xs) with (appendVectExtendBound y xs)
  appendVectExtendBound x (Cons prf y xs) | (Cons z w ys) = Cons (LTESucc prf) w (Cons z w ys)
