open import prelude

infixl 5 _$_

-- Copied pretty much verbatim

Var = String

data Term : Set where
  var : Var → Term
  fun : Var → Term → Term
  _$_ : Term → Term → Term

data Value : Term → Set where
  fun : (x : Var) → (t : Term) → Value(fun x t)

-- Free variables of a term.
-- (Turns out to be easiest to define when a variable isn't free rather than when it is.)

data _∉FV_ : Var → Term → Set where

  var : ∀ {x y} →

    x ≢ y →
    -------------
    x ∉FV(var y)
    
  fun₁ : ∀ {x y t} →

    (x ≡ y) →
    ---------------
    x ∉FV(fun y t)
    
  fun₂ : ∀ {x y t} →

    (x ∉FV(t)) →
    ---------------
    x ∉FV(fun y t)

  app : ∀ {x t₁ t₂} →

    (x ∉FV(t₁)) →
    (x ∉FV(t₂)) →
    -----------------
    (x ∉FV(t₁ $ t₂))

-- Substitution
-- TAPL defines substitution as a partial function, which Agda doesn't implement.
-- So instead we keep track of the derivation tree.

data [_↦_]_is_ : Var → Term → Term → Term → Set where

  yes : ∀ {x y s} →

    (x ≡ y) →
    ----------------------
    [ x ↦ s ] (var y) is s
    
  no : ∀ {x y s} →

    (x ≢ y) →
    ----------------------------
    [ x ↦ s ] (var y) is (var y)

  fun₁ : ∀ {x y s t} →

    (x ≡ y) →
    --------------------------------
    [ x ↦ s ] (fun y t) is (fun y t)

  fun₂ : ∀ {x y s t t′} →

    (x ≢ y) →
    (y ∉FV(s)) →
    [ x ↦ s ] t is t′ →
    ---------------------------------
    [ x ↦ s ] (fun y t) is (fun y t′)

  app : ∀ {x s t₁ t₁′ t₂ t₂′} →

    [ x ↦ s ] t₁ is t₁′ →
    [ x ↦ s ] t₂ is t₂′ →
    ---------------------------------
    [ x ↦ s ] (t₁ $ t₂) is (t₁′ $ t₂′)

-- Reduction is as per TAPL

data _⟶_ : Term → Term → Set where

  E─App1 : ∀ {t₁ t₁′ t₂} →

     (t₁ ⟶ t₁′) →
     ------------------------
     (t₁ $ t₂) ⟶ (t₁′ $ t₂)

  E─App2 : ∀ {t₁ t₂ t₂′} →

     (t₂ ⟶ t₂′) →
     ------------------------
     (t₁ $ t₂) ⟶ (t₁ $ t₂′)

  E─AppAbs : ∀ {x t₁ t₂ t₃} →

     [ x ↦ t₂ ] t₁ is t₃ →
     ----------------------
     (fun x t₁ $ t₂) ⟶ t₃

-- A redex is a term which can reduce

data Redex  : Term → Set where

  redex : ∀ {t t′} →
  
    t ⟶ t′ →
    --------
    Redex(t)

-- A closed term is one with no free variables

Closed : Term → Set
Closed(t) = ∀ {x} → x ∉FV(t)

-- Proving that substitution is well-defined for closed terms

data [_↦_]_⇓ : Var → Term → Term → Set where

  subst : ∀ {x s t t′} →
    ([ x ↦ s ] t is t′) →
    ([ x ↦ s ] t ⇓)

substDef : (x : Var) → (s t : Term) → Closed(s) → ([ x ↦ s ] t ⇓)
substDef x s (var y) c = helper (x ≟ y) where

  helper : Dec(x ≡ y) → ([ x ↦ s ] (var y) ⇓)
  helper (yes p) = subst (yes p)
  helper (no  p) = subst (no p)
  
substDef x s (fun y t) c = helper₁ (x ≟ y) where

  helper₂ : (x ≢ y) → ([ x ↦ s ] t ⇓) → ([ x ↦ s ] (fun y t) ⇓)
  helper₂ p (subst s) = subst (fun₂ p c s)

  helper₁ : Dec(x ≡ y) → ([ x ↦ s ] (fun y t) ⇓)
  helper₁ (yes p) = subst (fun₁ p)
  helper₁ (no  p) = helper₂ p (substDef x s t c)
  
substDef x s (t₁ $ t₂) c = helper (substDef x s t₁ c) (substDef x s t₂ c) where

  helper : ([ x ↦ s ] t₁ ⇓) → ([ x ↦ s ] t₂ ⇓) → ([ x ↦ s ] (t₁ $ t₂) ⇓)
  helper (subst s₁) (subst s₂) = subst (app s₁ s₂)

-- Proving that closed terms stay closed

closed₁ : ∀ {t₁ t₂ x} → (x ∉FV(t₁ $ t₂)) → (x ∉FV(t₁))
closed₁ (app p₁ p₂) = p₁

closed₂ :  ∀ {t₁ t₂ x} → (x ∉FV(t₁ $ t₂)) → (x ∉FV(t₂))
closed₂ (app p₁ p₂) = p₂

substClosed₁ : ∀ {y s t t′} → (y ∉FV(s)) → ([ y ↦ s ] t is t′) → (y ∉FV(t′))
substClosed₁ p (yes refl) = p
substClosed₁ p (no q) = var q
substClosed₁ p (fun₁ q) = fun₁ q
substClosed₁ p (fun₂ x x₁ q) = fun₂ (substClosed₁ p q)
substClosed₁ p (app q₁ q₂) = app (substClosed₁ p q₁) (substClosed₁ p q₂)

substClosed₂ : ∀ {x y s t t′} → (x ∉FV(t)) → (x ∉FV(s)) → ([ y ↦ s ] t is t′) → (x ∉FV(t′))
substClosed₂ p q (yes refl) = q
substClosed₂ p q (no r) = p
substClosed₂ p q (fun₁ refl) = p
substClosed₂ (fun₁ p) q (fun₂ x x₁ r) = fun₁ p
substClosed₂ (fun₂ p) q (fun₂ x x₁ r) = fun₂ (substClosed₂ p q r)
substClosed₂ (app p₁ p₂) q (app r₁ r₂) = app (substClosed₂ p₁ q r₁) (substClosed₂ p₂ q r₂)

substClosed₃ : ∀ {x y s t t′} → x ∉FV(fun y t) → x ∉FV(s) → ([ y ↦ s ] t is t′) → x ∉FV(t′)
substClosed₃ (fun₁ refl) q r = substClosed₁ q r
substClosed₃ (fun₂ p)    q r = substClosed₂ p q r

redexClosed : ∀ {t t′} → Closed(t) → (t ⟶ t′) → Closed(t′)
redexClosed c (E─App1 r)   = app (redexClosed (closed₁ c) r) (closed₂ c)
redexClosed c (E─App2 r)   = app (closed₁ c) (redexClosed (closed₂ c) r)
redexClosed c (E─AppAbs s) = substClosed₃ (closed₁ c) (closed₂ c) s

-- Proving that every closed term is a value or a redex

data ValueOrRedex : Term → Set where

  value : ∀ {t} →

    (Value(t)) →
    ---------------
    ValueOrRedex(t)

  redex : ∀ {t t′} →
  
    t ⟶ t′ →
    ---------------
    ValueOrRedex(t)

valueOrRedex : (t : Term) → Closed(t) → ValueOrRedex(t)
valueOrRedex (var x) c = CONTRADICTION (helper c) where

  helper : (x ∉FV(var x)) → FALSE
  helper (var p) = p refl
  
valueOrRedex (fun x t) c = value (fun x t)
valueOrRedex (t₁ $ t₂) c = helper₁ (valueOrRedex t₁ (closed₁ c)) where

  helper₃ : ∀ {x s t} → ([ x ↦ s ] t ⇓) → ValueOrRedex((fun x t) $ s)
  helper₃ (subst s) = redex (E─AppAbs s)
  
  helper₂ : ∀ {t₁} → Value(t₁) → ValueOrRedex(t₂) → ValueOrRedex(t₁ $ t₂)
  helper₂ (fun x t) (value v) = helper₃ (substDef x t₂ t (closed₂ c))
  helper₂ (fun x t) (redex r) = redex (E─App2 r)

  helper₁ : ValueOrRedex(t₁) → ValueOrRedex(t₁ $ t₂)
  helper₁ (value v₁) = helper₂ v₁ (valueOrRedex t₂ (closed₂ c))
  helper₁ (redex r) = redex (E─App1 r)

-- Interpreter!

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

-- The interpreter just calls `valueOrRedex` until it is a value.
-- This might bot terminate!

{-# NON_TERMINATING #-}
interp : (t : Term) → Closed(t) → Result(t)
interp t c = helper₂ (valueOrRedex t c) where

  helper₁ : ∀ {t′} → (t ⟶ t′) → Result(t′) → Result(t)
  helper₁ r (result s v) = result (redex r s) v

  helper₂ : ValueOrRedex(t) → Result(t)
  helper₂ (value v)           = result done v
  helper₂ (redex {t′ = t′} r) = helper₁ r (interp t′ (redexClosed c r))

-- Examples

zer : Term
zer = fun "z" (fun "s" (var "z"))

succ : Term
succ = fun "x" (fun "z" (fun "s" (var "s" $ var "x")))

add : Term
add = fun "x" (fun "y" (var "x" $ var "y" $ succ))

two : Term
two = succ $ (succ $ zer)

four : Term
four = add $ two $ two

zerC : Closed(zer)
zerC {x} with (x ≟ "z")
... | yes refl = fun₁ refl
... | no  p    = fun₂ (fun₂ (var p))

succC : Closed(succ)
succC {x} with (x ≟ "x") | (x ≟ "s")
... | yes refl | _        = fun₁ refl
... | no  p    | yes refl = fun₂ (fun₂ (fun₁ refl))
... | no  p    | no q     = fun₂ (fun₂ (fun₂ (app (var q) (var p))))

addC : Closed(add)
addC {x} with (x ≟ "x") | (x ≟ "y")
... | yes refl | _        = fun₁ refl
... | no  p    | yes refl = fun₂ (fun₁ refl)
... | no  p    | no q     = fun₂ (fun₂ (app (app (var p) (var q)) succC))

twoC : Closed(two)
twoC = app succC (app succC zerC)

fourC : Closed(four)
fourC = app (app addC twoC) twoC
