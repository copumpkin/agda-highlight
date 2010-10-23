# A markdown heading

Here's a blurb

> module STLC where
> 
> open import Data.Nat using (ℕ; zero; suc)
> open import Data.List using (List; []; _∷_)

Some operator _fixities!_
 
> infixr 4 _+_
> infixr 5 _×_
> infixr 6 _⇒_
> 
> data Type : Set where
>   0#  : Type
>   1#  : Type
>   _+_ : (σ τ : Type) → Type
>   _×_ : (σ τ : Type) → Type
>   _⇒_ : (σ τ : Type) → Type

Yeah, I'm just doing random shit here. Here are our terms and typed variables, de Bruijn style (but fancier)

> Context = List Type
> 
> data Var : Context → Type → Set where
>   zero : ∀ {τ Γ} → Var (τ ∷ Γ) τ
>   suc  : ∀ {σ τ Γ} → (n : Var Γ τ) → Var (σ ∷ Γ) τ
> 
> data Term : Context → Type → Set where
>   var : ∀ {τ Γ} → Var Γ τ → Term Γ τ
> 
>   unit : ∀ {Γ} → Term Γ 1#
> 
>   inj₁   : ∀ {σ τ Γ} → (x : Term Γ σ) → Term Γ (σ + τ)
>   inj₂   : ∀ {σ τ Γ} → (y : Term Γ τ) → Term Γ (σ + τ)
>   either : ∀ {σ τ ρ Γ} → (f : Term (σ ∷ Γ) ρ) → (g : Term (τ ∷ Γ) ρ) → (x : Term Γ (σ + τ)) → Term Γ ρ
> 
>   _,_   : ∀ {σ τ Γ} → (x : Term Γ σ) → (y : Term Γ τ) → Term Γ (σ × τ)
>   proj₁ : ∀ {σ τ Γ} → (x : Term Γ (σ × τ)) → Term Γ σ
>   proj₂ : ∀ {σ τ Γ} → (x : Term Γ (σ × τ)) → Term Γ τ
> 
>   lam : ∀ {σ τ Γ} → (q : Term (σ ∷ Γ) τ) → Term Γ (σ ⇒ τ)
>   app : ∀ {σ τ Γ} → (f : Term Γ (σ ⇒ τ)) (x : Term Γ σ) → Term Γ τ

Let's actually "run" the code, in Agda!

> module Reify where
>   open import Data.Empty
>   open import Data.Unit
>   open import Data.Sum
>   open import Data.Product hiding (proj₁; proj₂) renaming (_×_ to _×′_)
> 
>   ⟦_⟧ : Type → Set
>   ⟦ 0# ⟧ = ⊥
>   ⟦ 1# ⟧ = ⊤
>   ⟦ σ + τ ⟧ = ⟦ σ ⟧ ⊎ ⟦ τ ⟧
>   ⟦ σ × τ ⟧ = ⟦ σ ⟧ ×′ ⟦ τ ⟧
>   ⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ → ⟦ τ ⟧
> 
>   data Environment : Context → Set where
>     []  : Environment []
>     _∷_ : ∀ {c cs} → (e : ⟦ c ⟧) → (es : Environment cs) → Environment (c ∷ cs)
> 
>   eval : ∀ {τ Γ} → (t : Term Γ τ) → Environment Γ → ⟦ τ ⟧
>   eval (var zero) (e ∷ es) = e
>   eval (var (suc n)) (e ∷ es) = eval (var n) es
>   eval unit e = tt
>   eval (inj₁ x) e = inj₁ (eval x e)
>   eval (inj₂ y) e = inj₂ (eval y e)
>   eval (either f g x) e = [ (λ x → eval f (x ∷ e)) , (λ y → eval g (y ∷ e)) ]′ (eval x e)
>   eval (x , y) e = eval x e , eval y e
>   eval (proj₁ x) e = Σ.proj₁ (eval x e)
>   eval (proj₂ x) e = Σ.proj₂ (eval x e)
>   eval (lam q) e = λ x → eval q (x ∷ e)
>   eval (app f x) e = (eval f e) (eval x e)
> 
>   run : ∀ {τ} → (t : Term [] τ) → ⟦ τ ⟧
>   run t = eval t []

Yeah, so that's that.

