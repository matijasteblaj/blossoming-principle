import Mathlib.LinearAlgebra.AffineSpace.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Field.Defs

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees

import Mathlib.Data.Fintype.Defs

open Affine
notation "VectorSpace" => Module

section PolynomialMaps

/-- A coordinate system on an affine space is a pair of a point (origin)
and vector space basis. -/
structure CoordinateSystem (ι F V P : Type) [Field F] [AddCommGroup V] [VectorSpace F V]
  [AffineSpace V P] where
  origin : P
  basis  : Module.Basis ι F V

variable {F : Type} [Field F]
variable {V : Type} [AddCommGroup V] [VectorSpace F V]
variable {P : Type} [AffineSpace V P]
variable {ι : Type}
variable {W : Type} [AddCommGroup W] [VectorSpace F W]
variable {R : Type} [AffineSpace W R]
variable {κ : Type}

/-- Returns coordinates of a given point in the given CoordinateSystem. -/
def CoordinateSystem.coordinates (cs: CoordinateSystem ι F V P) (p : P) : ι → F :=
  cs.basis.repr (p -ᵥ cs.origin)



/-- A polynomial map in coordinates is a map, that can be represented
with polynomials in the given coordinate systems.-/
structure PolynomialMapInCoords (map : P → R) (cs₁ : CoordinateSystem ι F V P)
  (cs₂ : CoordinateSystem κ F W R) where

  /-- The polynomials representing the map.-/
  polys : κ  → MvPolynomial ι F

  /-- The coordinates of a point mapped with `map` must be equal to values
  of the polynomials in `polys` in the coordinates of the initial point -/
  map_poly_eq: ∀ (p : P) (i : κ),
   (cs₂.coordinates (map p)) i = (polys i).eval (cs₁.coordinates p)

def PolynomialMapInCoords.degree [Fintype κ]
  {map : P → R}
  {cs₁ : CoordinateSystem ι F V P}
  {cs₂ : CoordinateSystem κ F W R}
  (M : PolynomialMapInCoords map cs₁ cs₂) : Nat :=
    Finset.univ.sup (fun i => (M.polys i).totalDegree)

def isPolyMapInCoords (map : P → R) (cs₁ : CoordinateSystem ι F V P)
 (cs₂ : CoordinateSystem κ F W R) : Prop :=
  Nonempty (PolynomialMapInCoords map cs₁ cs₂)

  variable {ι₁ ι₂ κ₁ κ₂ : Type}

theorem poly_in_one_poly_in_another (map : P → R) (cs₁ : CoordinateSystem ι₁ F V P)
 (cs₂ : CoordinateSystem κ₁ F W R) (cs₃ : CoordinateSystem ι₂ F V P)
 (cs₄ : CoordinateSystem κ₂ F W R):
   (isPolyMapInCoords map cs₁ cs₂) → (isPolyMapInCoords map cs₃ cs₄) := by
   sorry

theorem poly_in_one_poly_in_all (map : P → R) (cs₁ : CoordinateSystem ι F V P)
 (cs₂ : CoordinateSystem κ F W R):
  (isPolyMapInCoords map cs₁ cs₂) → ∀ (cs₃ : CoordinateSystem ι₂ F V P)
  (cs₄ : CoordinateSystem κ₂ F W R), (isPolyMapInCoords map cs₃ cs₄) := by
    intro h cs₃ cs₄
    apply (poly_in_one_poly_in_another map cs₁ cs₂)
    exact h

def isPolyMap (map: P → R) : Prop :=
  ∃ (cs₁ : CoordinateSystem ι F V P) (cs₂ : CoordinateSystem κ F W R),
    isPolyMapInCoords map cs₁ cs₂

end PolynomialMaps

section Blossom
