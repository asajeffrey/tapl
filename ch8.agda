open import prelude

-- Copied pretty much verbatim

data Term : Set where
  true : Term
  false : Term
  if_then_else_end : Term → Term → Term → Term
  zero : Term
  succ : Term → Term
  iszero : Term → Term
  
data NValue : Term → Set where
  zero : NValue zero
  succ : ∀ {t} → NValue(t) → NValue(succ t)
  
data Value : Term → Set where
  true : Value true
  false :  Value false
  nv : ∀ {t} → NValue(t) → Value(t)
  
data _⟶_ : Term → Term → Set where

  E─IfTrue : ∀ {t₂ t₃} →

    -----------------------------------
    if true then t₂ else t₃ end ⟶ t₂

  E─IfFalse : ∀ {t₂ t₃} →
    
    -----------------------------------
    if false then t₂ else t₃ end ⟶ t₃

  E─IfCong : ∀ {t₁ t₁′ t₂ t₃} →
  
    (t₁ ⟶ t₁′) →
    ----------------------------------------------------------
    (if t₁ then t₂ else t₃ end ⟶ if t₁′ then t₂ else t₃ end)

  E─SuccCong : ∀ {t₁ t₁′} →
  
    (t₁ ⟶ t₁′) →
    ----------------------
    (succ t₁ ⟶ succ t₁′)

  E─IsZero : 
  
    ----------------------
    (iszero zero ⟶ true)

  E─IsSucc : ∀ {n} →
  
    --------------------------
    (iszero (succ n) ⟶ false)

  E─IsCong : ∀ {t₁ t₁′} →
  
    (t₁ ⟶ t₁′) →
    --------------------------
    (iszero t₁ ⟶ iszero t₁′)
    
data Redex  : Term → Set where

  redex : ∀ {t t′} →
  
    t ⟶ t′ →
    --------
    Redex(t)

-- Types

data Type : Set where
  bool : Type
  nat : Type

data _∈_ : Term → Type → Set where

  T-True :

    -----------
    true ∈ bool
    
  T-False :

    -----------
    false ∈ bool
    
  T-If : ∀ {t₁ t₂ t₃ T} →

    t₁ ∈ bool →
    t₂ ∈ T →
    t₃ ∈ T →
    -----------------------------
    if t₁ then t₂ else t₃ end ∈ T

  T-Zero :

    ----------
    zero ∈ nat
    
  T-Succ : ∀ {t₁} →

    t₁ ∈ nat →
    -------------
    succ t₁ ∈ nat
    
  T-IsZero : ∀ {t₁} →

    t₁ ∈ nat →
    -------------
    iszero t₁ ∈ bool
    
    
-- Proving that well-typed terms stay well-typed

preservation : ∀ {t t′ T} → (t ∈ T) → (t ⟶ t′) → (t′ ∈ T)
preservation (T-If p₁ p₂ p₃) E─IfTrue = p₂
preservation (T-If p₁ p₂ p₃) E─IfFalse = p₃
preservation (T-If p₁ p₂ p₃) (E─IfCong q) = T-If (preservation p₁ q) p₂ p₃
preservation (T-Succ p) (E─SuccCong q) = T-Succ (preservation p q)
preservation (T-IsZero p) E─IsZero = T-True
preservation (T-IsZero p) E─IsSucc = T-False
preservation (T-IsZero p) (E─IsCong q) = T-IsZero (preservation p q)

-- Proving that every term is a value or a redex

data ValueOrRedex : Term → Set where

  value : ∀ {t} →

    (Value(t)) →
    ---------------
    ValueOrRedex(t)

  redex : ∀ {t t′} →
  
    t ⟶ t′ →
    ---------------
    ValueOrRedex(t)

progress : ∀ {t T} → (t ∈ T) → ValueOrRedex(t)
progress T-True = value true
progress T-False = value false
progress (T-If p₁ p₂ p₃) = helper (progress p₁) p₁ where

  helper : ∀ {t₀ t₁ t₂} → ValueOrRedex(t₀) → t₀ ∈ bool → ValueOrRedex(if t₀ then t₁ else t₂ end)
  helper (value true) p = redex E─IfTrue
  helper (value false) p = redex E─IfFalse
  helper (redex r) p = redex (E─IfCong r)
  helper (value (nv ())) T-True
  helper (value (nv ())) T-False
  helper (value (nv ())) (T-If p p₁ p₂)

progress T-Zero = value (nv zero)
progress (T-Succ p) = helper (progress p) p where

  helper : ∀ {t₀} → ValueOrRedex(t₀) → t₀ ∈ nat → ValueOrRedex(succ t₀)
  helper (value (nv n)) p = value (nv (succ n))
  helper (redex r) p = redex (E─SuccCong r)

progress (T-IsZero p) = helper (progress p) p where

  helper : ∀ {t₀} → ValueOrRedex(t₀) → t₀ ∈ nat → ValueOrRedex(iszero t₀)
  helper (value (nv zero)) p = redex E─IsZero
  helper (value (nv (succ x))) p = redex E─IsSucc
  helper (redex r) p = redex (E─IsCong r)

-- Interpreter

data _⟶*_ : Term → Term → Set where

  done : ∀ {t} →

    --------
    t ⟶* t

  redex : ∀ {t t′ t″} →

    t ⟶ t′ →
    t′ ⟶* t″ →
    ----------
    t ⟶* t″

-- An interpreter result

data Result  : Term → Set where

  result : ∀ {t t′} →
  
    t ⟶* t′ →
    Value(t′) →
    ---------
    Result(t)

-- The interpreter just calls `progress` until it is a value.
-- This might bot terminate!

{-# NON_TERMINATING #-}
interp : ∀ {t T} → (t ∈ T) → Result(t)
interp p = helper₂ p (progress p) where

  helper₁ : ∀ {t t′} → (t ⟶ t′) → Result(t′) → Result(t)
  helper₁ r (result s v) = result (redex r s) v

  helper₂ : ∀ {t T} → (t ∈ T) → ValueOrRedex(t) → Result(t)
  helper₂ p (value v) = result done v
  helper₂ p (redex r) = helper₁ r (interp (preservation p r))

ex = if (iszero zero) then (succ zero) else (zero) end

exNat : (ex ∈ nat)
exNat = T-If (T-IsZero T-Zero) (T-Succ T-Zero) T-Zero

-- Normalize (C-N) interp exNat
-- result
--   (redex (E─IfCong E─IsZero)
--     (redex E─IfTrue
--       done))
--   (nv (succ zero))
