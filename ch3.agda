open import prelude

-- Copied pretty much verbatim

data Term : Set where
  true : Term
  false : Term
  if_then_else_end : Term → Term → Term → Term

data Value : Term → Set where
  true : Value true
  false :  Value false

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

data Redex  : Term → Set where

  redex : ∀ {t t′} →
  
    t ⟶ t′ →
    --------
    Redex(t)

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

valueOrRedex : (t : Term) → ValueOrRedex(t)
valueOrRedex true = value true
valueOrRedex false = value false
valueOrRedex if t₀ then t₁ else t₂ end = helper (valueOrRedex t₀) where

  helper : ∀ {t₀ t₁ t₂} → ValueOrRedex(t₀) → ValueOrRedex(if t₀ then t₁ else t₂ end)
  helper (value true) = redex E─IfTrue
  helper (value false) = redex E─IfFalse
  helper (redex r) = redex (E─IfCong r)

-- From which we get some of the theorems in the book

NormalForm : Term → Set
NormalForm(t) = Redex(t) → FALSE

thm357 : ∀ {t} → Value(t) → NormalForm(t)
thm357 true (redex ())
thm357 false (redex ())

thm358 : ∀ {t} → NormalForm(t) → Value(t)
thm358 {t} nf = helper (valueOrRedex t) nf where

  helper : ∀ {t} → ValueOrRedex(t) → NormalForm(t) → Value(t)
  helper (value v) nf = v
  helper (redex r) nf = CONTRADICTION (nf (redex r))

-- But also we can buid an interpreter.
-- The idea is to provide some "fuel" n, and run the term for at most n steps
-- `t ⟶^[ n ] t′` whenever `t` can reduce to `t′` in at most n steps.

data _⟶^[_]_ : Term → Nat → Term → Set where

  nofuel : ∀ {t} →

    -------------
    t ⟶^[ 0 ] t

  value : ∀ {t n} →

    Value(t) →
    -------------
    t ⟶^[ n ] t

  redex : ∀ {t t′ t″ n} →

    t ⟶ t′ →
    t′ ⟶^[ n ] t″ →
    ------------------
    t ⟶^[ 1 + n ] t″

-- An interpreter result for running term `t` with fuel `n` is `t ⟶^[ n ] t′`  for some term `t′`.

data Result^[_]  : Nat → Term → Set where

  result : ∀ {n t t′} →
  
    t ⟶^[ n ] t′ →
    -------------
    Result^[ n ](t)

-- The interpreter just calls `valueOrRedex` at most `n` times.

interp : (n : Nat) → (t : Term) → Result^[ n ](t)
interp zero    t = result nofuel
interp (suc n) t = helper n (valueOrRedex t) where

  step : ∀ {t t′ n} → (t ⟶ t′) → Result^[ n ](t′) → Result^[ 1 + n ](t)
  step r (result s) = result (redex r s)

  helper : ∀ {t} → (n : Nat) → ValueOrRedex(t) → Result^[ 1 + n ](t)
  helper n (value v) = result (value v)
  helper n (redex {t} {t′} r) = step r (interp n t′)

-- Examples

not : Term → Term
not(t) = if t then false else true end

_and_ : Term → Term → Term
s and t = if s then t else false end

_or_ : Term → Term → Term
s or t = if s then true else t end

ex : Term
ex = (true and false) or (not true)

-- Try normalizing (CTRL-C CTRL-N) `interp 4 ex`
-- you get told the result but also the derivation tree for every step!
-- ```
-- result
-- (redex (E─IfCong E─IfTrue)
--  (redex E─IfFalse
--   (redex E─IfTrue
--    (value false))))
-- ```
