module ArithmeticExpressions where
open import Data.Maybe
open import Data.Bool hiding (if_then_else_)
open import Relation.Nullary

data Term : Set where
  true false : Term
  if_then_else_ : Term → Term → Term → Term
  zero : Term
  succ pred iszero : Term → Term

data Value : Term → Set where
  true : Value true
  false : Value false
  zero : Value zero
  succ : ∀ {t} → Value t → Value (succ t)

data _⟶_ : Term → Term → Set where
  E-IfTrue : ∀ {t₂ t₃} →
    if true then t₂ else t₃ ⟶ t₂
  E-IfFalse : ∀ {t₂ t₃} →
    if false then t₂ else t₃ ⟶ t₃
  E-If : ∀ {t₁ t₁′ t₂ t₃} →
    t₁ ⟶ t₁′ →
    if t₁ then t₂ else t₃ ⟶ if t₁′ then t₂ else t₃
  E-Succ : ∀ {t₁ t₁′} →
    succ t₁ ⟶ succ t₁′
  E-PredZero :
    pred zero ⟶ zero
  E-PredSucc : ∀ {nv₁} →
    pred (succ nv₁) ⟶ nv₁
  E-Pred : ∀ {t₁ t₁′} →
    t₁ ⟶ t₁′ → 
    pred t₁ ⟶ pred t₁′
  E-IsZeroZero :
    iszero zero ⟶ true
  E-IsZeroSucc : ∀ {nv₁} →
    iszero (succ nv₁) ⟶ false
  E-IsZero : ∀ {t₁ t₁′} →
    iszero t₁ ⟶ iszero t₁′

Normal : Term → Set
Normal t = ∀ t′ → ¬ t ⟶ t′

Stuck : Term → Set
Stuck t = Normal t → ¬ Value t

data Terminating (t : Term) : Set where
  done : Normal t → Terminating t
  step : ∀ {t′} → t ⟶ t′ → Terminating t′ → Terminating t

terminates : ∀ t → Terminating t
terminates true = done λ _ ()
terminates false = done λ _ ()
terminates zero = done λ _ ()
terminates _ = {!!}

