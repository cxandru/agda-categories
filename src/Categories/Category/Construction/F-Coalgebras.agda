{-# OPTIONS --without-K --safe #-}
open import Categories.Category
module Categories.Category.Construction.F-Coalgebras  {o ℓ e} {C : Category o ℓ e}  where

open import Level
open import Categories.Functor hiding (id)
open import Categories.Functor.Algebra
open import Categories.Functor.Coalgebra
open import Categories.Object.Initial
open import Categories.Object.Terminal
import Categories.Morphism.Reasoning as MR
import Categories.Morphism as Mor using (_≅_; Iso)
open import Categories.Category.Construction.F-Algebras
open import Categories.Functor.Duality

F-Coalgebras :  Endofunctor C → Category (ℓ ⊔ o) (e ⊔ ℓ) e
F-Coalgebras F = record
  { Obj       = F-Coalgebra F
  ; _⇒_       = F-Coalgebra-Morphism
  ; _≈_       = λ α₁ α₂ → f α₁ ≈ f α₂
  ; _∘_       = λ α₁ α₂ → record
    { f = f α₁ ∘ f α₂
    ; commutes = F-Algebra-Morphism.commutes (F-Coalgebra-Morphism⇒coF-Algebra-Morphism α₁
       coF-Algebras.∘
       F-Coalgebra-Morphism⇒coF-Algebra-Morphism α₂)
    }
  ; id        = record { f = id; commutes = F-Algebra-Morphism.commutes coF-Algebras.id }
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv     = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  ; ∘-resp-≈  = ∘-resp-≈
  }
  where
    open Category C
    open MR C
    open HomReasoning
    open Equiv
    open F-Coalgebra-Morphism
    module coF-Algebras = Category (Category.op (F-Algebras (Functor.op F)))

module Initial/TerminalDuality {F : Endofunctor C} where
  open Functor F renaming (op to Fop)

  IsInitial⇒coIsTerminal : ∀ {T : Category.Obj (F-Algebras Fop) } →
    IsInitial (F-Algebras Fop) T →
    IsTerminal (F-Coalgebras F) (coF-Algebra⇒F-Coalgebra T)
  IsInitial⇒coIsTerminal is⊥ = record
    { !        = coF-Algebra-Morphism⇒F-Coalgebra-Morphism !
    ; !-unique = λ γ → !-unique (F-Coalgebra-Morphism⇒coF-Algebra-Morphism γ)
    }
    where open IsInitial is⊥

  ⊥⇒op⊤ : Initial (F-Algebras Fop) → Terminal (F-Coalgebras F)
  ⊥⇒op⊤ i = record
    { ⊤             = coF-Algebra⇒F-Coalgebra ⊥
    ; ⊤-is-terminal = IsInitial⇒coIsTerminal ⊥-is-initial
    }
    where open Initial i

  IsInitial⇒coIsTerminal2 : ∀ {T : Category.Obj (F-Coalgebras F) } →
    IsInitial (F-Coalgebras F) T →
    IsTerminal (F-Algebras Fop) (F-Coalgebra⇒coF-Algebra T)
  IsInitial⇒coIsTerminal2 is⊥ = record
    { !        = F-Coalgebra-Morphism⇒coF-Algebra-Morphism !
    ; !-unique = λ γ → !-unique (coF-Algebra-Morphism⇒F-Coalgebra-Morphism γ)
    }
    where open IsInitial is⊥

  ⊥⇒op⊤2 : Initial (F-Coalgebras F) → Terminal (F-Algebras Fop)
  ⊥⇒op⊤2 i = record
    { ⊤             = F-Coalgebra⇒coF-Algebra ⊥
    ; ⊤-is-terminal = IsInitial⇒coIsTerminal2 ⊥-is-initial
    }
    where open Initial i

  coIsTerminal⇒IsInitial : ∀ {T : Category.Obj (F-Coalgebras F) } →
    IsTerminal (F-Coalgebras F) T →
    IsInitial (F-Algebras Fop) (F-Coalgebra⇒coF-Algebra T)
  coIsTerminal⇒IsInitial is⊤ = record
    { ! = F-Coalgebra-Morphism⇒coF-Algebra-Morphism !
    ; !-unique = λ γ → !-unique (coF-Algebra-Morphism⇒F-Coalgebra-Morphism γ)
    }
    where
      open IsTerminal is⊤

  op⊤⇒⊥ : Terminal (F-Coalgebras F) → Initial (F-Algebras Fop)
  op⊤⇒⊥ t = record
    { ⊥            = F-Coalgebra⇒coF-Algebra ⊤
    ; ⊥-is-initial = coIsTerminal⇒IsInitial ⊤-is-terminal
    }
    where open Terminal t

open Initial/TerminalDuality public

module CoLambek {F : Endofunctor C} (T : Terminal (F-Coalgebras F)) where
  open Category C
  open Functor F using (F₀)
  open F-Coalgebra using (α)

  open Mor C
  open Terminal T

  private
    module F⊤ = F-Coalgebra ⊤
    A = F⊤.A
    a : A ⇒ F₀ A
    a = F⊤.α
    module coLambek = Lambek (op⊤⇒⊥ T)

  colambek : A ≅ F₀ A
  colambek = record
    { from = to coLambek.lambek
    ; to = from coLambek.lambek
    ; iso = record
      { isoˡ = isoˡ (iso coLambek.lambek)
      ; isoʳ = isoʳ (iso coLambek.lambek)
      }
    }
    where
      open HomReasoning
      open Mor._≅_
      open Mor.Iso
