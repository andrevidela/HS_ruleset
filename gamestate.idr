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
       Left overflow => MkPlayerHP maxHP armor bonusHP (Val maxHP (lteRightPlusNat maxHP))
       Right newHP => MkPlayerHP maxHP armor bonusHP newHP

alextrazaEffect : (newMax : Nat) -> PlayerHP -> PlayerHP
alextrazaEffect newMax (MkPlayerHP maxHP armor bonusHP currentHitPoints)  with (cmp newMax maxHP)
  -- new max is lower than the current max HP -> reduce the current amout of hp
  alextrazaEffect newMax (MkPlayerHP (newMax + (S y)) armor bonusHP currentHitPoints)  | (CmpLT y) =
    let upperBoundPrf = lteRightPlusLeft (lteRightPlusNat newMax) in
      MkPlayerHP (newMax + (S y)) armor bonusHP $ Val newMax upperBoundPrf
  -- new max is equal to the current max HP -> set current hp to max hp
  alextrazaEffect maxHP (MkPlayerHP maxHP armor bonusHP currentHitPoints)  | CmpEQ =
    MkPlayerHP maxHP armor bonusHP (Val maxHP $ lteRightPlusNat maxHP)
  -- new max is higher than current maxi HP -> keep max HP, add the extra amount of HP as bonus, set the current to bonus + max
  alextrazaEffect (maxHP + (S x)) (MkPlayerHP maxHP armor bonusHP currentHitPoints)  | (CmpGT x) =
    MkPlayerHP maxHP armor (S x) (Val (maxHP + (S x)) $ lteEq (maxHP + (S x)))

Card : Type

data Deck : (card : Type) -> Type where
  MkDeck : Vect n card -> Nat -> Deck card

-- Attempts to draw a card, returns the card and the new state of the deck.
-- Either the deck is empty and the overdraw count is returned, or the card is successfully drawn
drawCard : Deck card -> (Either Nat card, Deck card)
drawCard (MkDeck [] overDraw) = (Left (S overDraw), MkDeck [] (S overDraw))
drawCard (MkDeck (x :: xs) overDraw) = (Right x, MkDeck xs overDraw)

mutual

  record Player where
    constructor MkPlayer
    type : PlayerType
    hitPoints : PlayerHP
    heroPower : Hearthstone -> Hearthstone
    deck : Deck Card
    board : BoardSide 7

  record Hearthstone where
    constructor MkHearthstone
    turn : BoundedNat 50
    currentPlayer : Player
    opposingPlayer : Player
