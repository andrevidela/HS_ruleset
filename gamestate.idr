import Data.Vect
import Data.Fin

%default total

data NatNeg = Pos Nat | Neg Nat

NatToPos : Nat -> NatNeg
NatToPos = Pos

subtract : Nat -> Nat -> NatNeg
subtract k Z = Pos k
subtract Z (S j) = Neg (S j)
subtract (S k) (S j) = subtract k j

natToProvedFin : (n : Nat) -> (bound : Nat) -> {auto prf : LT n bound} -> Fin bound
natToProvedFin Z (S right) {prf=LTESucc x} = FZ
natToProvedFin (S k) (S right) {prf=LTESucc x} = FS $ natToProvedFin k right 

lteRightPlusZero : LTE hp (hp + (fromInteger 0))
lteRightPlusZero {hp = Z} = LTEZero
lteRightPlusZero {hp = (S k)} = LTESucc lteRightPlusZero

Minion : Type

BoardSide : (size : Nat) -> Type
BoardSide size = Vect size (Maybe Minion)

data PlayerType = Fst | Snd

data BoundedNat : (bound : Nat) -> Type where
  Val : (n : Nat) -> (ok : LTE n bound) -> BoundedNat bound

MkUpperBound : (b : Nat) -> BoundedNat b
MkUpperBound Z = Val Z LTEZero
MkUpperBound (S k) = Val (S k) (LTESucc lteRefl)

||| Add a nat to a boundednat, either the sum it out of bound and the excess is returned as Left. Or the new bounded value is returned as right
boundedAdd : BoundedNat b -> Nat -> Either Nat (BoundedNat b)
boundedAdd bounded Z = Right bounded
boundedAdd bounded (S k) {b = Z} = Left (S k)
boundedAdd (Val n ok) (S j) {b = (S k)} with (isLTE n k)
  boundedAdd (Val n ok) (S j) {b = (S k)} | (Yes prf) = let p = LTESucc prf in 
                                                            boundedAdd (Val (S n) p) j
  boundedAdd (Val n ok) (S j) {b = (S k)} | (No contra) = Left (S j)

lteLeftSucc : LTE (S j) k -> LTE j k
lteLeftSucc (LTESucc LTEZero) = LTEZero
lteLeftSucc (LTESucc (LTESucc x)) = LTESucc (lteLeftSucc (LTESucc x))

||| subtract a bounded nat by a Nat, the result is within bounds
subtractBounded : BoundedNat k -> Nat -> BoundedNat k
subtractBounded x Z = x
subtractBounded (Val Z ok) (S k) = Val Z ok
subtractBounded (Val (S j) ok) (S k) = subtractBounded (Val j (lteLeftSucc ok)) k


record PlayerHP where
  constructor MkPlayerHP
  maxHP : Nat
  armor : Nat
  bonusHP : Nat
  currentHitPoints : BoundedNat (maxHP + bonusHP)


dealDamage : (dmg : Nat) -> PlayerHP -> PlayerHP
dealDamage dmg (MkPlayerHP maxHP armor bonusHP currentHitPoints) = 
  case subtract armor dmg of
       (Pos remainingArmor) => MkPlayerHP maxHP remainingArmor bonusHP currentHitPoints
       (Neg remainingDmg) => let diff = subtractBounded currentHitPoints remainingDmg in
                                 MkPlayerHP maxHP 0 bonusHP diff

InitialHP : (hp : Nat) -> PlayerHP
InitialHP hp = MkPlayerHP hp 0 0 (Val hp lteRightPlusZero)



lteRightPlus : (maxHP : Nat) -> LTE maxHP (maxHP + bonusHP)
lteRightPlus Z = LTEZero
lteRightPlus (S k) = LTESucc (lteRightPlus k)

regularHeal : (heal : Nat) -> PlayerHP -> PlayerHP
regularHeal heal (MkPlayerHP maxHP armor bonusHP currentHitPoints) = 
  case boundedAdd currentHitPoints heal of
       Left overflow => MkPlayerHP maxHP armor bonusHP (Val maxHP (lteRightPlus maxHP))
       Right newHP => MkPlayerHP maxHP armor bonusHP newHP


mutual

  record Player where
    constructor MkPlayer
    type : PlayerType
    hitPoints : PlayerHP
    heroPower : Hearthstone -> Hearthstone
    board : BoardSide 7

  record Hearthstone where
    constructor MkHearthstone
    turn : BoundedNat 50
    currentPlayer : Player
    opposingPlayer : Player


