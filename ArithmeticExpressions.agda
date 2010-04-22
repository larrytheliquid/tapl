module ArithmeticExpressions where
open import Data.Empty
open import Data.Maybe
open import Data.Bool hiding (if_then_else_)
open import Level
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary

data Term : Set where
  true false : Term
  if_then_else_ : Term → Term → Term → Term
  zero : Term
  succ pred iszero : Term → Term

data Value : Pred Term zero where
  true : Value true
  false : Value false
  zero : Value zero
  succ : ∀ {t} → Value t → Value (succ t)

data _⟶_ : Rel Term zero where
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

Normal : Pred Term zero
Normal t = ∀ t′ → ¬ t ⟶ t′

Stuck : Pred Term zero
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

module IfHelpers where
  normalIfIf : ∀ {t₁′ t₂′ t₃′ t₂ t₃} → Normal (if t₁′ then t₂′ else t₃′) → Normal (if (if t₁′ then t₂′ else t₃′) then t₂ else t₃)
  normalIfIf n ._ (E-If r) = n _ r

  normalIfZero : ∀ {t₂ t₃} → Normal (if zero then t₂ else t₃)
  normalIfZero ._ (E-If r) = normalZero _ r

  normalIfSucc : ∀ {t t₂ t₃} → Normal (succ t) → Normal (if (succ t) then t₂ else t₃)
  normalIfSucc n ._ (E-If r) = n _ r

  normalIfPred : ∀ {t t₂ t₃} → Normal (pred t) → Normal (if (pred t) then t₂ else t₃)
  normalIfPred n ._ (E-If r) = n _ r

  normalIfIszero : ∀ {t t₂ t₃} → Normal (iszero t) → Normal (if (iszero t) then t₂ else t₃)
  normalIfIszero n ._ (E-If r) = n _ r

  terminatesIf : ∀ {t₁ t₂ t₃} → Terminating t₁ → Terminating t₂ → Terminating t₃ → Terminating (if t₁ then t₂ else t₃)
  terminatesIf {true} (done _) t₂ _ = step E-IfTrue t₂
  terminatesIf {false} (done _) _ t₃ = step E-IfFalse t₃
  terminatesIf {if _ then _ else _} (done n) _ _ = done (normalIfIf n)
  terminatesIf {zero} (done _) _ _ = done normalIfZero
  terminatesIf {succ _} (done n) _ _ = done (normalIfSucc n)
  terminatesIf {pred _} (done n) _ _ = done (normalIfPred n)
  terminatesIf {iszero _} (done n) _ _ = done (normalIfIszero n)
  terminatesIf (step r p) t₂ t₃ = step (E-If r) (terminatesIf p t₂ t₃)
open IfHelpers

module SuccHelpers where
  normalSucc : ∀ {t} → Normal t → Normal (succ t)
  normalSucc n .(succ _) (E-Succ r) = n _ r

  terminatesSucc : ∀ {t} → Terminating t → Terminating (succ t)
  terminatesSucc (done n) = done (normalSucc n)
  terminatesSucc (step r p) = step (E-Succ r) (terminatesSucc p)
open SuccHelpers

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

terminates : ∀ t → Terminating t
terminates true = done normalTrue
terminates false = done normalFalse
terminates (if t₁ then t₂ else t₃) = terminatesIf (terminates t₁) (terminates t₂) (terminates t₃)
terminates zero = done normalZero
terminates (succ t) = terminatesSucc (terminates t)
terminates (pred t) = terminatesPred (terminates t)
terminates (iszero t) = terminatesIszero (terminates t)

terminal : ∀ {t} → Terminating t → Term
terminal {t} (done _ ) = t
terminal (step _ p) = terminal p
    
eval : Term → Term
eval t = terminal (terminates t)
