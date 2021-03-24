open import prelude
open import ch6 using (Term  ; var ; fun ; _$_ ; two ; four)

-- A stack is a list of values
-- Values are either closures or errors

data Value : Set where
  error : Value
  closure : List(Value) → Term → Value

Stack = List(Value)

lookup : (s : Stack) → (x : Nat) → Value
lookup nil x = error
lookup (v :: s) zero = v
lookup (v :: s) (suc x) = lookup s x

-- Big step sematics

data _▷_⇓_ : Stack → Term → Value → Set where

  E─Var : ∀ {s x} →

    --------------------------
    s ▷ (var x) ⇓ (lookup s x)
    
  E─Fun : ∀ {s t} →
  
    ---------------------------
    s ▷ (fun t) ⇓ (closure s t)

  E─App : ∀ {s s′ t t′ u u′ v} →

    s ▷ t ⇓ (closure s′ t′) →
    s ▷ u ⇓ u′ →
    (u′ :: s′) ▷ t′ ⇓ v →
    -------------------
    s ▷ (t $ u) ⇓ v

  E─AppErr : ∀ {s t u} →

    s ▷ t ⇓ error →
    -------------------
    s ▷ (t $ u) ⇓ error

-- An interpreter result

data Result : Stack → Term → Set where

  result : ∀ {s t} →

    (v : Value) →
    (s ▷ t ⇓ v) →
    -------------
    Result s t

{-# NON_TERMINATING #-}
interpret : (s : Stack) → (t : Term) → Result s t
interpret s (var x) = result (lookup s x) E─Var
interpret s (fun t) = result (closure s t) E─Fun
interpret s (t₁ $ t₂) = helper₁ (interpret s t₁) where

  helper₃ : ∀ {s′ t′ u′} → (s ▷ t₁ ⇓ (closure s′ t′)) → (s ▷ t₂ ⇓ u′) → Result (u′ :: s′) t′ → Result s (t₁ $ t₂)
  helper₃ p q (result v r) = result v (E─App p q r)

  helper₂ : ∀ {s′ t′} → (s ▷ t₁ ⇓ (closure s′ t′)) → Result s t₂ → Result s (t₁ $ t₂)
  helper₂ {s′} {t′} p (result u′ q) = helper₃ p q (interpret (u′ :: s′) t′)
  
  helper₁ : Result s t₁ → Result s (t₁ $ t₂)
  helper₁ (result error           p) = result error (E─AppErr p)
  helper₁ (result (closure s′ t′) p) = helper₂ p (interpret s t₂)

-- Shorthand for starting from the empty stack

i = interpret nil
