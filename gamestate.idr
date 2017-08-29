import Data.Vect
import Data.Fin
import BoundedNat
import NatHelpers

%default total

Minion : Type

BoardSide : (size : Nat) -> Type
BoardSide size = Vect size (Maybe Minion)

data PlayerType = Fst | Snd


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

regularHeal : (heal : Nat) -> PlayerHP -> PlayerHP
regularHeal heal (MkPlayerHP maxHP armor bonusHP currentHitPoints) =
  case boundedAdd currentHitPoints heal of
       Left overflow => MkPlayerHP maxHP armor bonusHP (Val maxHP (lteRightPlus maxHP))
       Right newHP => MkPlayerHP maxHP armor bonusHP newHP

alextrazaEffect : (newMax : Nat) -> PlayerHP -> PlayerHP
alextrazaEffect newMax (MkPlayerHP maxHP armor bonusHP currentHitPoints)  with (cmp newMax maxHP)
  alextrazaEffect newMax (MkPlayerHP (newMax + (S y)) armor bonusHP currentHitPoints)  | (CmpLT y) =
    MkPlayerHP (newMax + (S y)) armor bonusHP (?prf)
  alextrazaEffect maxHP (MkPlayerHP maxHP armor bonusHP currentHitPoints)  | CmpEQ =
    MkPlayerHP maxHP armor bonusHP (Val maxHP $ lteRightPlus maxHP)
  alextrazaEffect (maxHP + (S x)) (MkPlayerHP maxHP armor bonusHP currentHitPoints)  | (CmpGT x) =
    ?alextrazaEffect_rhs_3

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
