module NatHelpers
import Data.Fin
%default total

export
natToProvedFin : (n : Nat) -> (bound : Nat) -> {auto prf : LT n bound} -> Fin bound
natToProvedFin Z (S right) {prf=LTESucc x} = FZ
natToProvedFin (S k) (S right) {prf=LTESucc x} = FS $ natToProvedFin k right

export
lteRightPlusZero : LTE hp (hp + (fromInteger 0))
lteRightPlusZero {hp = Z} = LTEZero
lteRightPlusZero {hp = (S k)} = LTESucc lteRightPlusZero

export
lteRightSucc : LTE k j -> LTE k (S j)
lteRightSucc LTEZero = LTEZero
lteRightSucc (LTESucc x) = LTESucc (lteRightSucc x)

export
lteRightPlus : LTE k j -> LTE k (j + l)
lteRightPlus LTEZero = LTEZero
lteRightPlus (LTESucc x) = LTESucc (lteRightPlus x)

export
lteRightPlusLeft : LTE n (n + k) -> LTE n ((n + j) + k)
lteRightPlusLeft LTEZero = LTEZero
lteRightPlusLeft (LTESucc x) = LTESucc (lteRightPlusLeft x)

export
lteRightPlusNat : (n : Nat) -> LTE n (n + k)
lteRightPlusNat Z = LTEZero
lteRightPlusNat (S k) = LTESucc (lteRightPlusNat k)

export
lteEq : (n : Nat) -> LTE n n
lteEq Z = LTEZero
lteEq (S k) = LTESucc (lteEq k)

public export
data NatNeg = Pos Nat | Neg Nat

export
NatToPos : Nat -> NatNeg
NatToPos = Pos

export
subtract : Nat -> Nat -> NatNeg
subtract k Z = Pos k
subtract Z (S j) = Neg (S j)
subtract (S k) (S j) = subtract k j
