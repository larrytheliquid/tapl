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

  normalIszeroIf : ∀ {t₁ t₂ t₃} → Normal (if t₁ then t₂ else t₃) → Normal (iszero (if t₁ then t₂ else t₃))
  normalIszeroIf n ._ (E-Iszero r) = n _ r

  normalIszeroPred : ∀ {t} → Normal (pred t) → Normal (iszero (pred t))
  normalIszeroPred n ._ (E-Iszero r) = n _ r

  normalIszeroIszero : ∀ {t} → Normal (iszero t) → Normal (iszero (iszero t))
  normalIszeroIszero n ._ (E-Iszero r) = n _ r

  terminatesIszero : ∀ {t} → Terminating t → Terminating (iszero t)
  terminatesIszero {true} (done _) = done normalIszeroTrue
  terminatesIszero {false} (done _) = done normalIszeroFalse
  terminatesIszero {if _ then _ else _} (done n) = done (normalIszeroIf n)
  terminatesIszero {zero} (done _) = step E-IszeroZero (done normalTrue)
  terminatesIszero {succ _} (done _) = step E-IszeroSucc (done normalFalse)
  terminatesIszero {pred _} (done n) = done (normalIszeroPred n)
  terminatesIszero {iszero _} (done n) = done (normalIszeroIszero n)
  terminatesIszero (step r p) = step (E-Iszero r) (terminatesIszero p)
open IszeroHelpers

module PredHelpers where
  normalPredTrue : Normal (pred true)
  normalPredTrue ._ (E-Pred r) = normalTrue _ r

  normalPredFalse : Normal (pred false)
  normalPredFalse ._ (E-Pred r) = normalFalse _ r

  normalPredIf : ∀ {t₁ t₂ t₃} → Normal (if t₁ then t₂ else t₃) → Normal (pred (if t₁ then t₂ else t₃))
  normalPredIf n ._ (E-Pred r) = n _ r

  normalSuccInv : ∀ {t} → Normal (succ t) → Normal t
  normalSuccInv n t r = n (succ t) (E-Succ r)

  normalPredPred : ∀ {t} → Normal (pred t) → Normal (pred (pred t))
  normalPredPred n ._ (E-Pred r) = n _ r

  normalPredIszero : ∀ {t} → Normal (iszero t) → Normal (pred (iszero t))
  normalPredIszero n ._ (E-Pred r) = n _ r

  terminatesPred : ∀ {t} → Terminating t → Terminating (pred t)
  terminatesPred {true} (done _) = done normalPredTrue
  terminatesPred {false} (done _) = done normalPredFalse
  terminatesPred {if _ then _ else _} (done n) = done (normalPredIf n)
  terminatesPred {zero} (done _) = step E-PredZero (done normalZero)
  terminatesPred {succ _} (done n) = step E-PredSucc (done (normalSuccInv n))
  terminatesPred {pred _} (done n) = done (normalPredPred n)
  terminatesPred {iszero _} (done n) = done (normalPredIszero n)
  terminatesPred (step r p) = step (E-Pred r) (terminatesPred p)
open PredHelpers

terminates : ∀ t → Terminating t
terminates true = done normalTrue
terminates false = done normalFalse
terminates zero = done normalZero
terminates (succ t) = terminatesSucc (terminates t)
terminates (pred t) = terminatesPred (terminates t)
terminates (iszero t) = terminatesIszero (terminates t)
terminates _ = {!!}

terminal : ∀ {t} → Terminating t → Term
terminal {t} (done _ ) = t
terminal (step _ p) = terminal p
    
eval : Term → Term
eval t = terminal (terminates t)
