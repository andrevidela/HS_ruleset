
module BoundedNat
import Data.Fin
import NatHelpers
-- Bounded Nats, Nats which are LTE than the upper bound


%default total

public export
data BoundedNat : (bound : Nat) -> Type where
  Val : (n : Nat) -> (ok : LTE n bound) -> BoundedNat bound

export
MkUpperBound : (b : Nat) -> BoundedNat b
MkUpperBound Z = Val Z LTEZero
MkUpperBound (S k) = Val (S k) (LTESucc lteRefl)

export
weakenBound : BoundedNat b -> BoundedNat (S b)
weakenBound (Val n ok) = Val n (lteRightSucc ok)

export
weakenBoundN : (n : Nat) -> BoundedNat b -> BoundedNat (b + n)
weakenBoundN k (Val n ok) = Val n (lteRightPlus ok)


||| Add a nat to a boundednat, either the sum it out of bound and the excess is returned as Left. Or the new bounded value is returned as right
export boundedAdd : BoundedNat b -> Nat -> Either Nat (BoundedNat b)
boundedAdd bounded Z = Right bounded
boundedAdd bounded (S k) {b = Z} = Left (S k)
boundedAdd (Val n ok) (S j) {b = (S k)} with (isLTE n k)
  boundedAdd (Val n ok) (S j) {b = (S k)} | (Yes prf) = let p = LTESucc prf in
                                                            boundedAdd (Val (S n) p) j
  boundedAdd (Val n ok) (S j) {b = (S k)} | (No contra) = Left (S j)

||| the predecessor of l in l <= r is also smaller than r
export lteLeftSucc : LTE (S j) k -> LTE j k
lteLeftSucc (LTESucc LTEZero) = LTEZero
lteLeftSucc (LTESucc (LTESucc x)) = LTESucc (lteLeftSucc (LTESucc x))

||| subtract a bounded nat by a Nat, the result is within bounds,
export subtractBounded : BoundedNat k -> Nat -> BoundedNat k
subtractBounded x Z = x
subtractBounded (Val Z ok) (S k) = Val Z ok
subtractBounded (Val (S j) ok) (S k) = subtractBounded (Val j (lteLeftSucc ok)) k

export
boundPlusRight : (value : Nat) -> BoundedNat (value + more)
boundPlusRight value = Val value (lteRightPlusNat value)


export
addBounded : BoundedNat b -> Nat -> BoundedNat b
addBounded x k with (boundedAdd x k)
  addBounded x k | (Left l) {b} = MkUpperBound b
  addBounded x k | (Right r) = r
