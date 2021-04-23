{-# OPTIONS --rewriting #-}

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
[ x ↦ s ] var y = if (x ≟ y) (shift 0 x s) (if (x ≤? y) (var (y - 1)) (var y))
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

data _∋_⦂_ : Context → Nat → Type → Set where

  zero : ∀ {Γ S} → (Γ , S) ∋ zero ⦂ S
  suc : ∀ {Γ S T n} → (Γ ∋ n ⦂ T) → (Γ , S) ∋ suc n ⦂ T

data _⊢_⦂_ : Context → Term → Type → Set where

  T-True : ∀ {Γ} →

    -----------
    Γ ⊢ true ⦂ bool

  T-False : ∀ {Γ} →

    -----------
    Γ ⊢ false ⦂ bool

  T-If : ∀ {Γ t₁ t₂ t₃ T} →

    Γ ⊢ t₁ ⦂ bool →
    Γ ⊢ t₂ ⦂ T →
    Γ ⊢ t₃ ⦂ T →
    -----------------------------
    Γ ⊢ if t₁ then t₂ else t₃ end ⦂ T

  T-Var : ∀ {Γ n T} →

    Γ ∋ n ⦂ T →
    ------------------------
    Γ ⊢ var n ⦂ T

  T-Abs : ∀ {Γ t T₁ T₂} →

    (Γ , T₁) ⊢ t ⦂ T₂ →
    -----------------------
    Γ ⊢ (fun t) ⦂ (T₁ ⇒ T₂)

  T-App : ∀ {Γ t₁ t₂ T₁₁ T₁₂} →

    Γ ⊢ t₁ ⦂ (T₁₁ ⇒ T₁₂) →
    Γ ⊢ t₂ ⦂ T₁₁ →
    -----------------------
    Γ ⊢ (t₁ $ t₂) ⦂ T₁₂

-- Proving that well-typed terms stay well-typed

# : Context → Nat
# ε = 0
# (Γ , x) = 1 + # Γ

_,,_ : Context → Context → Context
Γ ,, ε = Γ
Γ ,, (Δ , T) = (Γ ,, Δ) , T

T-Eq : ∀ {Γ s S T} → (Γ ⊢ s ⦂ S) → (S ≡ T) → (Γ ⊢ s ⦂ T)
T-Eq p refl = p

hit : ∀ {Γ Δ S T} → (((Γ , S) ,, Δ) ∋ # Δ ⦂ T) → (S ≡ T)
hit {Δ = ε} zero = refl
hit {Δ = Δ , R} (suc p) = hit p

left : ∀ {Γ Δ S T n} → (# Δ < n) → (((Γ , S) ,, Δ) ∋ n ⦂ T) → ((Γ ,, Δ) ∋ (n - 1) ⦂ T)
left {n = zero} p q = CONTRADICTION (p zero)
left {Δ = ε} {n = suc n} p (suc q) = q
left {Δ = Δ , R} {n = suc zero} p (suc q) = CONTRADICTION (p (suc zero))
left {Δ = Δ , R} {n = suc (suc n)} p (suc q) = suc (left (λ a → p (suc a)) q)

right : ∀ {Γ Δ S T n} → (n < # Δ) → (((Γ , S) ,, Δ) ∋ n ⦂ T) → ((Γ ,, Δ) ∋ n ⦂ T)
right {Δ = ε} p q = CONTRADICTION (p zero)
right {Δ = Δ , R} p zero = zero
right {Δ = Δ , R} p (suc q) = suc (right (λ z → p (suc z)) q)

this : ∀ {Γ T} n Δ Ξ → (# Ξ ≤ n) → ((Γ ,, Ξ) ∋ n ⦂ T) → (((Γ ,, Δ) ,, Ξ) ∋ (# Δ + n) ⦂ T)
this n ε ε p q = q
this n (Δ , R) ε p q = suc (this n Δ ε p q)
this (suc n) Δ (Ξ , S) (suc p) (suc q) = suc (this n Δ Ξ p q)

that : ∀ {Γ T} n Δ Ξ → (n < # Ξ) → ((Γ ,, Ξ) ∋ n ⦂ T) → (((Γ ,, Δ) ,, Ξ) ∋ n ⦂ T)
that n Δ ε p q = CONTRADICTION (p zero)
that zero Δ (Ξ , S) p zero = zero
that (suc n) Δ (Ξ , S) p (suc q) = suc (that n Δ Ξ (λ z → p (suc z)) q)

preservation-shift : ∀ {Γ s S} Δ Ξ → ((Γ ,, Ξ) ⊢ s ⦂ S) → (((Γ ,, Δ) ,, Ξ) ⊢ shift (# Ξ) (# Δ) s ⦂ S)
preservation-shift Δ Ξ T-True = T-True
preservation-shift Δ Ξ T-False = T-False
preservation-shift Δ Ξ (T-If p p₁ p₂) = T-If (preservation-shift Δ Ξ p) (preservation-shift Δ Ξ p₁)
                                          (preservation-shift Δ Ξ p₂)
preservation-shift {Γ} {var n} {S} Δ Ξ (T-Var p) = helper (# Ξ ≤? n) where

  helper : (q : Dec(# Ξ ≤ n)) → ((Γ ,, Δ) ,, Ξ) ⊢ if q (var (# Δ + n)) (var n) ⦂ S
  helper (yes q) = T-Var (this n Δ Ξ q p)
  helper (no q)  = T-Var (that n Δ Ξ q p)

preservation-shift Δ Ξ (T-Abs p) = T-Abs (preservation-shift Δ (Ξ , _) p)
preservation-shift Δ Ξ (T-App p p₁) = T-App (preservation-shift Δ Ξ p) (preservation-shift Δ Ξ p₁)

preservation-substitution : ∀ {Γ s t S T} → (Γ ⊢ s ⦂ S) → (Δ : Context) → (((Γ , S) ,, Δ) ⊢ t ⦂ T) → ((Γ ,, Δ) ⊢ [ # Δ ↦ s ] t ⦂ T)
preservation-substitution {Γ} {s} {t} {S} {T} p Δ (T-Var {n = n} q) = helper (# Δ ≟ n) (# Δ ≤? n) where

  helper : (p : Dec(# Δ ≡ n)) → (q : Dec(# Δ ≤ n)) → (Γ ,, Δ) ⊢ if p (shift 0 (# Δ) s) (if q (var (n - 1)) (var n)) ⦂ T
  helper (yes refl) _ = T-Eq (preservation-shift Δ ε p) (hit q)
  helper (no a) (yes b) = T-Var (left (λ c → a (asym b c)) q)
  helper (no a) (no b) = T-Var (right b q)

preservation-substitution p Δ T-True = T-True
preservation-substitution p Δ T-False = T-False
preservation-substitution p Δ (T-If q q₁ q₂) = T-If (preservation-substitution p Δ q)
                                                 (preservation-substitution p Δ q₁)
                                                 (preservation-substitution p Δ q₂)
preservation-substitution p Δ (T-Abs q) = T-Abs (preservation-substitution p (Δ , _) q)
preservation-substitution p Δ (T-App q q₁) = T-App (preservation-substitution p Δ q)
                                               (preservation-substitution p Δ q₁)

preservation : ∀ {Γ t t′ T} → (Γ ⊢ t ⦂ T) → (t ⟶ t′) → (Γ ⊢ t′ ⦂ T)
preservation (T-If p₁ p₂ p₃) E─IfTrue = p₂
preservation (T-If p₁ p₂ p₃) E─IfFalse = p₃
preservation (T-If p₁ p₂ p₃) (E─IfCong q) = T-If (preservation p₁ q) p₂ p₃
preservation (T-App p₁ p₂) (E─App1 q) = T-App (preservation p₁ q) p₂
preservation (T-App p₁ p₂) (E─App2 q) = T-App p₁ (preservation p₂ q)
preservation (T-App (T-Abs p₁) p₂) E─AppAbs = preservation-substitution p₂ ε p₁

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

progress : ∀ {Γ t T} → (Γ ⊢ t ⦂ T) → ValueOrRedex(t)
progress T-True = value true
progress T-False = value false
progress (T-If p₁ p₂ p₃) = helper (progress p₁) p₁ where

  helper : ∀ {Γ t₀ t₁ t₂} → ValueOrRedex(t₀) → (Γ ⊢ t₀ ⦂ bool) → ValueOrRedex(if t₀ then t₁ else t₂ end)
  helper (value true) p = redex E─IfTrue
  helper (value false) p = redex E─IfFalse
  helper (value (var x)) p = value (if var x then _ else _ end)
  helper (value (if t₃ then t₄ else t₅ end)) p = value if if t₃ then t₄ else t₅ end then _ else _ end
  helper (value (t₁ $ t₂)) p = value if (t₁ $ t₂) then _ else _ end
  helper (redex r) p = redex (E─IfCong r)

progress (T-Var {n = n} p) = value (var n)
progress (T-Abs {t = t} p) = value (fun t)
progress (T-App p₁ p₂) = helper (progress p₁) p₁ where

  helper : ∀ {Γ t₁ t₂ T₁₁ T₁₂} → ValueOrRedex(t₁) → (Γ ⊢ t₁ ⦂ (T₁₁ ⇒ T₁₂)) → ValueOrRedex(t₁ $ t₂)
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
interp : ∀ {Γ t T} → (Γ ⊢ t ⦂ T) → Result(t)
interp p = helper₂ p (progress p) where

  helper₁ : ∀ {t t′} → (t ⟶ t′) → Result(t′) → Result(t)
  helper₁ r (result s v) = result (redex r s) v

  helper₂ : ∀ {Γ t T} → (Γ ⊢ t ⦂ T) → ValueOrRedex(t) → Result(t)
  helper₂ p (value v) = result done v
  helper₂ p (redex r) = helper₁ r (interp (preservation p r))

