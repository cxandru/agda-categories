{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Functor using (Functor; Endofunctor)
open import Categories.Functor.DistributiveLaw using (DistributiveLaw)
module Categories.Functor.Construction.LiftCoalgebras {o ℓ e} {C : Category o ℓ e} (T F : Endofunctor C) (μ : DistributiveLaw T F) where

open import Level
open import Function using (_$_)

open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Category.Construction.F-Algebras
open import Categories.Functor.Construction.LiftAlgebras using (LiftAlgebras)
open import Categories.Functor.Duality

open import Categories.Functor.Algebra
open import Categories.Functor.Coalgebra
open import Categories.Object.Initial
open import Categories.Object.Terminal

import Categories.Morphism.Reasoning as MR

LiftCoalgebras : Endofunctor (F-Coalgebras F)
LiftCoalgebras = record
  { F₀           = λ X → record { A = (T .F₀) (X .A);  α = (μ .η) (X .A) ∘ (F₁ T) (X .α) }
  ; F₁           = λ α₁ → record
    { f = (T .F₁) (α₁ .f)
    ; commutes = F-Algebra-Morphism.commutes
        (T̂ᵒᵖ.F₁ (F-Coalgebra-Morphism⇒coF-Algebra-Morphism α₁))
    }
  ; identity     = identity T
  ; homomorphism = homomorphism T
  ; F-resp-≈     = F-resp-≈ T
  }
  where
    open Category C
    open Functor
    open NaturalTransformation
    open F-Coalgebra
    open F-Coalgebra-Morphism
    private module T̂ᵒᵖ = Functor (LiftAlgebras (Functor.op F) (Functor.op T) (NaturalTransformation.op μ))

liftTerminal : Terminal (F-Coalgebras F) → Terminal (F-Algebras LiftCoalgebras)
liftTerminal νF = record
  { ⊤ = record
    { A = ⊤
    ; α = ⟦ F₀ ⊤ ⟧
    }
  ; ⊤-is-terminal = record
    { ! = λ {A = X} →
      let
        c = F-Algebra.A X
        a = F-Algebra.α X
      in record
      { f = ⟦ c ⟧
      ; commutes = !-unique₂ {f = (⟦ c ⟧ ∘ a)} {g = (⟦ F₀ ⊤ ⟧ ∘ F₁ ⟦ c ⟧)}
      }
    ; !-unique = λ {A = X} g → !-unique (F-Algebra-Morphism.f g)
    }
  }
  where
    open Terminal νF
    open Category (F-Coalgebras F)
    open Definitions (F-Coalgebras F)
    open MR (F-Coalgebras F)
    open HomReasoning
    open Equiv
    private
      ⟦_⟧ = λ X → ! {A = X}
    open Functor LiftCoalgebras

-- begin Coalgs(F̂)⇔Algs(T̂)

AlgebrasT̂⇒CoalgebrasF̂ : Functor (F-Algebras LiftCoalgebras) (F-Coalgebras (LiftAlgebras T F μ))
AlgebrasT̂⇒CoalgebrasF̂ = record
    { F₀           = λ X → record
      { A = to-Algebra $ F-Coalgebra-Morphism.f $ F-Algebra.α X
      ; α = record
        { f = F-Coalgebra.α $ F-Algebra.A X
        ; commutes = F-Coalgebra-Morphism.commutes (F-Algebra.α X) ○ sym-assoc
        }
      }
    ; F₁           = λ {X Y} β → record
      { f = record
        { f = F-Coalgebra-Morphism.f $ F-Algebra-Morphism.f β
        ; commutes = F-Algebra-Morphism.commutes β
        }
      ; commutes = F-Coalgebra-Morphism.commutes $ F-Algebra-Morphism.f β
      }
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ x → x
    }
    where
      open Category C
      open MR C
      open HomReasoning
      open Equiv

CoalgebrasF̂⇒AlgebrasT̂ : Functor (F-Coalgebras (LiftAlgebras T F μ)) (F-Algebras LiftCoalgebras)
CoalgebrasF̂⇒AlgebrasT̂ = record
    { F₀           = λ X → record
      { A = to-Coalgebra $ F-Algebra-Morphism.f $ F-Coalgebra.α X
      ; α = record
        { f = F-Algebra.α $ F-Coalgebra.A X
        ; commutes = F-Algebra-Morphism.commutes (F-Coalgebra.α X) ○ assoc
        }
      }
    ; F₁           = λ {X Y} β → record
      { f = record
        { f = F-Algebra-Morphism.f $ F-Coalgebra-Morphism.f β
        ; commutes = F-Coalgebra-Morphism.commutes β
        }
      ; commutes = F-Algebra-Morphism.commutes $ F-Coalgebra-Morphism.f β
      }
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ x → x
    }
    where
      open Category C
      open MR C
      open HomReasoning
      open Equiv

-- end Coalgs(F̂)⇔Algs(T̂)

{-
NB:
Below for `!` we cannot use `AlgebrasT̂⇒CoalgebrasF̂ .F₁ t-morph`, even
though syntactically we are constructing the same morphism.  This is
because `F₁ t-morph` would have type `(AlgebrasT̂⇒CoalgebrasF̂ ·
CoalgebrasF̂⇒AlgebrasT̂) .F₀ X ⇒ AlgebrasT̂⇒CoalgebrasF̂ .F₀ ⊤`, but we
need a morphism of type `X ⇒ AlgebrasT̂⇒CoalgebrasF̂ .F₀ ⊤`, which we
don't get because `(AlgebrasT̂⇒CoalgebrasF̂ · CoalgebrasF̂⇒AlgebrasT̂) .F₀
X` isn't `≡` to `X`.  This is because a `commutes` proof is different,
which is relevant for equality on objects, since the objects here are
Coalgebras of algebras, that is, their `α` component will be an
`F-Algebra-Morphism`, which have to have definitionally equal
`commutes` proofs. The error you get is:

```
Relation.Binary.Structures.IsEquivalence.trans (Category.equiv C)
(F-Coalgebra-Morphism.commutes
 (F-Algebra.α (CoalgebrasF̂⇒AlgebrasT̂ .F₀ X)))
(Category.sym-assoc C)
!= F-Algebra-Morphism.commutes (F-Coalgebra.α X)
```
-}
liftTerminalCoalgebrasF̂ : Terminal (F-Coalgebras F) → Terminal (F-Coalgebras (LiftAlgebras T F μ))
liftTerminalCoalgebrasF̂ νF = record
  { ⊤ = AlgebrasT̂⇒CoalgebrasF̂ .F₀ $ ⊤
  ; ⊤-is-terminal = record
    { ! = λ {A = X} → let
      t-morph = νF̂.! { A = CoalgebrasF̂⇒AlgebrasT̂ .F₀ X }
      in record
      { f = record
        { f = F-Coalgebra-Morphism.f (F-Algebra-Morphism.f t-morph)
        ; commutes = F-Algebra-Morphism.commutes t-morph
        }
      ; commutes = F-Coalgebra-Morphism.commutes (F-Algebra-Morphism.f t-morph)
      }
    ; !-unique = λ {A = X} g → νF̂.!-unique {A = CoalgebrasF̂⇒AlgebrasT̂ .F₀ X}
        record
        { f = record
          { f = F-Algebra-Morphism.f (F-Coalgebra-Morphism.f g)
          ; commutes = F-Coalgebra-Morphism.commutes g
          }
        ; commutes = F-Algebra-Morphism.commutes (F-Coalgebra-Morphism.f g)
        }
    }
  }
  where
    open Terminal (liftTerminal νF)
    open Functor
    private module νF̂ = IsTerminal ⊤-is-terminal
