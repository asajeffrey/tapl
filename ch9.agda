open import prelude renaming (_≟Nat_ to _≟_)

-- Copied pretty much verbatim

Var = Nat

data Term : Set where
  var : Var → Term
  fun : Term → Term
  _$_ : Term → Term → Term
  true : Term
  false : Term
  if_then_else_end : Term → Term → Term → Term
  
data VarHeaded : Term → Set
data Value : Term → Set

data VarHeaded where
  var : (x : Var) → VarHeaded(var x)
  _$_ : ∀ {t} → VarHeaded(t) → (u : Term) → VarHeaded(t $ u)
  if_then_else_end : ∀ {t₀} → VarHeaded(t₀) → (t₁ t₂ : Term) → VarHeaded(if t₀ then t₁ else t₂ end)
  
data Value where
  var : (x : Var) → Value(var x)
  fun : (t : Term) → Value(fun t)
  _$_ : ∀ {t} → VarHeaded(t) → (u : Term) → Value(t $ u)
  if_then_else_end : ∀ {t₀} → VarHeaded(t₀) → (t₁ t₂ : Term) → Value(if t₀ then t₁ else t₂ end)
  true : Value true
  false :  Value false

-- Substitution

shift : Var → Var → Term → Term
shift c d (var x) = if (c ≤? x) (var (d + x)) (var x)
shift c d (fun t) = fun (shift (1 + c) d t)
shift c d (t₁ $ t₂) = (shift c d t₁) $ (shift c d t₂)
shift c d true = true
shift c d false = false
shift c d if t₀ then t₁ else t₂ end = if shift c d t₀ then shift c d t₁ else shift c d t₂ end

[_↦_]_ : Var → Term → Term → Term
[ x ↦ s ] var y = if (x ≟ y) (shift x 0 s) (if (x ≤? y) (var (y - 1)) (var y)) 
[ x ↦ s ] fun t = fun ([ (1 + x) ↦ s ] t)
[ x ↦ s ] (t₁ $ t₂) = ([ x ↦ s ] t₁) $ ([ x ↦ s ] t₂)
[ x ↦ s ] true = true
[ x ↦ s ] false = false
[ x ↦ s ] if t₀ then t₁ else t₂ end = if [ x ↦ s ] t₀ then [ x ↦ s ] t₁ else [ x ↦ s ] t₂ end

-- Reduction

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

data Redex  : Term → Set where

  redex : ∀ {t t′} →
  
    t ⟶ t′ →
    --------
    Redex(t)

-- Types

data Type : Set where
  bool : Type
  _⇒_ : Type → Type → Type

data Context : Set where
  ε : Context
  _,_ : Context → Type → Context
  
data _⊢_∈_ : Context → Term → Type → Set where

  T-True : ∀ {Γ} → 

    -----------
    Γ ⊢ true ∈ bool
    
  T-False : ∀ {Γ} → 

    -----------
    Γ ⊢ false ∈ bool
    
  T-If : ∀ {Γ t₁ t₂ t₃ T} →

    Γ ⊢ t₁ ∈ bool →
    Γ ⊢ t₂ ∈ T →
    Γ ⊢ t₃ ∈ T →
    -----------------------------
    Γ ⊢ if t₁ then t₂ else t₃ end ∈ T

  T-VarZero : ∀ {Γ T} →

    ------------------------
    (Γ , T) ⊢ (var zero) ∈ T

  T-VarSuc : ∀ {Γ n T} →

    Γ ⊢ (var n) ∈ T →
    ---------------------------
    (Γ , T) ⊢ (var (suc n)) ∈ T

  T-Abs : ∀ {Γ t T₁ T₂} →

    (Γ , T₁) ⊢ t ∈ T₂ →
    -----------------------
    Γ ⊢ (fun t) ∈ (T₁ ⇒ T₂)

  T-App : ∀ {Γ t₁ t₂ T₁₁ T₁₂} →

    Γ ⊢ t₁ ∈ (T₁₁ ⇒ T₁₂) →
    Γ ⊢ t₂ ∈ T₁₁ →
    -----------------------
    Γ ⊢ (t₁ $ t₂) ∈ T₁₂

-- Proving that well-typed terms stay well-typed

preservation-substitution : ∀ {Γ s t S T} → (Γ ⊢ s ∈ S) → ((Γ , S) ⊢ t ∈ T) → (Γ ⊢ [ 0 ↦ s ] t ∈ T)
preservation-substitution = {!!}

preservation : ∀ {Γ t t′ T} → (Γ ⊢ t ∈ T) → (t ⟶ t′) → (Γ ⊢ t′ ∈ T)
preservation (T-If p₁ p₂ p₃) E─IfTrue = p₂
preservation (T-If p₁ p₂ p₃) E─IfFalse = p₃
preservation (T-If p₁ p₂ p₃) (E─IfCong q) = T-If (preservation p₁ q) p₂ p₃
preservation (T-App p₁ p₂) (E─App1 q) = T-App (preservation p₁ q) p₂
preservation (T-App p₁ p₂) (E─App2 q) = T-App p₁ (preservation p₂ q)
preservation (T-App (T-Abs p₁) p₂) E─AppAbs = preservation-substitution p₂ p₁

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

progress : ∀ {Γ t T} → (Γ ⊢ t ∈ T) → ValueOrRedex(t)
progress T-True = value true
progress T-False = value false
progress (T-If p₁ p₂ p₃) = helper (progress p₁) p₁ where

  helper : ∀ {Γ t₀ t₁ t₂} → ValueOrRedex(t₀) → (Γ ⊢ t₀ ∈ bool) → ValueOrRedex(if t₀ then t₁ else t₂ end)
  helper (value true) p = redex E─IfTrue
  helper (value false) p = redex E─IfFalse
  helper (value (var x)) p = value (if var x then _ else _ end)
  helper (value (if t₃ then t₄ else t₅ end)) p = value if if t₃ then t₄ else t₅ end then _ else _ end
  helper (value (t₁ $ t₂)) p = value if (t₁ $ t₂) then _ else _ end
  helper (redex r) p = redex (E─IfCong r)

progress T-VarZero = value (var zero)
progress (T-VarSuc p) = value (var (suc _))
progress (T-Abs {t = t} p) = value (fun t)
progress (T-App p₁ p₂) = helper (progress p₁) p₁ where

  helper : ∀ {Γ t₁ t₂ T₁₁ T₁₂} → ValueOrRedex(t₁) → (Γ ⊢ t₁ ∈ (T₁₁ ⇒ T₁₂)) → ValueOrRedex(t₁ $ t₂)
  helper (value (var x)) p = value (var x $ _)
  helper (value (fun t)) p = redex E─AppAbs
  helper (value (t₃ $ t₄)) p = value ((t₃ $ t₄) $ _)
  helper (value (if t₃ then t₄ else t₅ end)) p = value (if t₃ then t₄ else t₅ end $ _)
  helper (redex r) p = redex (E─App1 r)

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
interp : ∀ {Γ t T} → (Γ ⊢ t ∈ T) → Result(t)
interp p = helper₂ p (progress p) where

  helper₁ : ∀ {t t′} → (t ⟶ t′) → Result(t′) → Result(t)
  helper₁ r (result s v) = result (redex r s) v

  helper₂ : ∀ {Γ t T} → (Γ ⊢ t ∈ T) → ValueOrRedex(t) → Result(t)
  helper₂ p (value v) = result done v
  helper₂ p (redex r) = helper₁ r (interp (preservation p r))

