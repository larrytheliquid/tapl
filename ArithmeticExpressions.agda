module ArithmeticExpressions where
open import Data.Empty
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
    t₁ ⟶ t₁′ →
    succ t₁ ⟶ succ t₁′
  E-PredZero :
    pred zero ⟶ zero
  E-PredSucc : ∀ {t₁} →
    pred (succ t₁) ⟶ t₁
  E-Pred : ∀ {t₁ t₁′} →
    t₁ ⟶ t₁′ → 
    pred t₁ ⟶ pred t₁′
  E-IszeroZero :
    iszero zero ⟶ true
  E-IszeroSucc : ∀ {t₁} →
    iszero (succ t₁) ⟶ false
  E-Iszero : ∀ {t₁ t₁′} →
    t₁ ⟶ t₁′ →
    iszero t₁ ⟶ iszero t₁′

Normal : Term → Set
Normal t = ∀ t′ → ¬ t ⟶ t′

Stuck : Term → Set
Stuck t = Normal t → ¬ Value t

data Terminating (t : Term) : Set where
  done : Normal t → Terminating t
  step : ∀ {t′} → t ⟶ t′ → Terminating t′ → Terminating t

normalTrue : Normal true
normalTrue _ ()

normalFalse : Normal false
normalFalse _ ()

normalZero : Normal zero
normalZero _ ()

module SuccHelpers where
  normalSucc : ∀ {t} → Normal t → Normal (succ t)
  normalSucc n .(succ _) (E-Succ r) = n _ r

  terminatesSucc : ∀ {t} → Terminating t → Terminating (succ t)
  terminatesSucc (done n) = done (normalSucc n)
  terminatesSucc (step r p) = step (E-Succ r) (terminatesSucc p)
open SuccHelpers

module IszeroHelpers where
  normalIszeroTrue : Normal (iszero true)
  normalIszeroTrue ._ (E-Iszero r) = normalTrue _ r

  normalIszeroFalse : Normal (iszero false)
  normalIszeroFalse ._ (E-Iszero r) = normalFalse _ r

  normalIszeroPred : ∀ {t} → Normal (pred t) → Normal (iszero (pred t))
  normalIszeroPred n ._ (E-Iszero r) = n _ r

  normalIszeroIszero : ∀ {t} → Normal (iszero t) → Normal (iszero (iszero t))
  normalIszeroIszero n ._ (E-Iszero r) = n _ r

  normalIszeroIf : ∀ {t₁ t₂ t₃} → Normal (if t₁ then t₂ else t₃) → Normal (iszero (if t₁ then t₂ else t₃))
  normalIszeroIf n ._ (E-Iszero r) = n _ r

  terminatesIszero : ∀ {t} → Terminating t → Terminating (iszero t)
  terminatesIszero {zero} (done _) = step E-IszeroZero (done normalTrue)
  terminatesIszero {succ _} (done _) = step E-IszeroSucc (done normalFalse)
  terminatesIszero {true} (done _) = done normalIszeroTrue
  terminatesIszero {false} (done _) = done normalIszeroFalse
  terminatesIszero {pred _} (done n) = done (normalIszeroPred n)
  terminatesIszero {iszero _} (done n) = done (normalIszeroIszero n)
  terminatesIszero {if _ then _ else _} (done n) = done (normalIszeroIf n)
  terminatesIszero (step r p) = step (E-Iszero r) (terminatesIszero p)
open IszeroHelpers

terminates : ∀ t → Terminating t
terminates true = done normalTrue
terminates false = done normalFalse
terminates zero = done normalZero
terminates (succ t) = terminatesSucc (terminates t)
terminates (iszero t) = terminatesIszero (terminates t)
terminates _ = {!!}

terminal : ∀ {t} → Terminating t → Term
terminal {t} (done _ ) = t
terminal (step _ p) = terminal p
    
eval : Term → Term
eval t = terminal (terminates t)
