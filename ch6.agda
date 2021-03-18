open import prelude renaming (_≟Nat_ to _≟_)

infixl 5 _$_

-- Copied pretty much verbatim

Var = Nat

data Term : Set where
  var : Var → Term
  fun : Term → Term
  _$_ : Term → Term → Term

-- Doing full reduction, so values are either of the form
-- (fun v) or (x v1 ... vN)

data VarHeaded : Term → Set
data Value : Term → Set

data VarHeaded where
  var : (x : Var) → VarHeaded(var x)
  _$_ : ∀ {t u} → VarHeaded(t) → Value(u) → VarHeaded(t $ u)
  
data Value where
  var : (x : Var) → Value(var x)
  fun : ∀ {t} → Value(t) → Value(fun t)
  _$_ : ∀ {t u} → VarHeaded(t) → Value(u) → Value(t $ u)

-- Substitution is now total!

shift : Var → Var → Term → Term
shift c d (var x) = if (c ≤? x) (var (d + x)) (var x)
shift c d (fun t) = fun (shift (1 + c) d t)
shift c d (t₁ $ t₂) = (shift c d t₁) $ (shift c d t₂)

[_↦_]_ : Var → Term → Term → Term
[ x ↦ s ] var y = if (x ≟ y) (shift x 0 s) (if (x ≤? y) (var (y - 1)) (var y)) 
[ x ↦ s ] fun t = fun ([ (1 + x) ↦ s ] t)
[ x ↦ s ] (t₁ $ t₂) = ([ x ↦ s ] t₁) $ ([ x ↦ s ] t₂)

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

  E─AppAbs : ∀ {t₁ t₂} →

     ---------------------------------
     (fun t₁ $ t₂) ⟶ ([ 0 ↦ t₂ ] t₁)

  -- Needed for full reduction!
  E─FunCong : ∀ {t t′} →
  
    (t ⟶ t′) →
    ----------------
    fun t ⟶ fun t′

-- A redex is a term which can reduce

data Redex  : Term → Set where

  redex : ∀ {t t′} →
  
    t ⟶ t′ →
    --------
    Redex(t)

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

valueOrRedex : (t : Term) → ValueOrRedex(t)
valueOrRedex (var x) = value (var x)
valueOrRedex (fun t) = helper (valueOrRedex t) where

  helper : ValueOrRedex(t) → ValueOrRedex(fun t)
  helper (value v) = value (fun v)
  helper (redex r) = redex (E─FunCong r)
  
valueOrRedex (t₁ $ t₂) = helper₁ (valueOrRedex t₁) where

  helper₃ : ∀ {t₁} → Value(t₁) → Value(t₂) → ValueOrRedex(t₁ $ t₂)
  helper₃ (var x) v = value (var x $ v)
  helper₃ (fun t) v = redex E─AppAbs
  helper₃ (t $ u) v = value (t $ u $ v)

  helper₂ : Value(t₁) → ValueOrRedex(t₂) → ValueOrRedex(t₁ $ t₂)
  helper₂ v₁ (value v₂) = helper₃ v₁ v₂
  helper₂ v₁ (redex r) = redex (E─App2 r)

  helper₁ : ValueOrRedex(t₁) → ValueOrRedex(t₁ $ t₂)
  helper₁ (value v₁) = helper₂ v₁ (valueOrRedex t₂)
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
-- This might not terminate!

{-# NON_TERMINATING #-}
interp : (t : Term) → Result(t)
interp t = helper₂ (valueOrRedex t) where

  helper₁ : ∀ {t′} → (t ⟶ t′) → Result(t′) → Result(t)
  helper₁ r (result s v) = result (redex r s) v

  helper₂ : ValueOrRedex(t) → Result(t)
  helper₂ (value v)           = result done v
  helper₂ (redex {t′ = t′} r) = helper₁ r (interp t′)

-- Examples

zer : Term
zer = fun (fun (var 1))

succ : Term
succ = fun (fun (fun (var 0 $ var 2)))

add : Term
add = fun (fun (var 1 $ var 0 $ succ))

two : Term
two = succ $ (succ $ zer)

four : Term
four = add $ two $ two
