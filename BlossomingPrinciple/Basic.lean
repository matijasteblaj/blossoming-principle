import Mathlib.LinearAlgebra.AffineSpace.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Field.Defs

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees


open Affine
notation "VectorSpace" => Module

section PolynomialMaps

/- Define a coordinate system of an affine space as a pair
 of a point (origin) and vector space basis. -/
structure CoordinateSystem (F V P: Type*) [Field F] [AddCommGroup V] [VectorSpace F V]
  [AffineSpace V P] where
  ι : Type
  origin : P
  basis  : Basis ι F V

variable {F : Type*} [Field F]
variable {V : Type*} [AddCommGroup V] [VectorSpace F V]
variable {P : Type*} [AffineSpace V P]
variable {W : Type*} [AddCommGroup W] [VectorSpace F W]
variable {R : Type*} [AffineSpace W R]

namespace CoordinateSystem

def coordinates (cs: CoordinateSystem F V P) (p : P) : cs.ι → F :=
  cs.basis.repr (p -ᵥ cs.origin)

end CoordinateSystem

-- Define a polynomial map in specific coordinate systems
structure PolynomialMapInCoords (map : P → R) (cs₁ : CoordinateSystem F V P)
  (cs₂ : CoordinateSystem F W R) where
  --The polynomials representing the map
  polys : cs₂.ι → MvPolynomial cs₁.ι F
  --The coordinates of the mapped point must be values of polys of the coordinates of the initial point
  map_poly_eq: ∀(p : P)(i : cs₂.ι),
   (cs₂.coordinates (map p)) i = (polys i).eval (cs₁.coordinates p)
  --Degree of polynomial map is the smallest bound for degrees of polys
  degree : Nat
  deg_max: ∀(i : cs₂.ι), degree ≥ (polys i).totalDegree
  deg_exist: ∃(i : cs₂.ι), degree = (polys i).totalDegree

/-The property of being polynomial in given coordinate systems (existence
of the PolynomialMapInCoords structure for given systems)-/
def isPolyMapInCoords (map : P → R) (cs₁ : CoordinateSystem F V P)
 (cs₂ : CoordinateSystem F W R) : Prop :=
  Nonempty (PolynomialMapInCoords map cs₁ cs₂)

theorem polyInOnePolyInAnother (map : P → R) (cs₁ : CoordinateSystem F V P)
 (cs₂ : CoordinateSystem F W R)(cs₃ : CoordinateSystem F V P)(cs₄ : CoordinateSystem F W R):
   (isPolyMapInCoords map cs₁ cs₂) → (isPolyMapInCoords map cs₃ cs₄) := by
   sorry

theorem polyInOnePolyInAll (map : P → R) (cs₁ : CoordinateSystem F V P)
 (cs₂ : CoordinateSystem F W R):
  (isPolyMapInCoords map cs₁ cs₂) → ∀ (cs₃ : CoordinateSystem F V P)(cs₄ : CoordinateSystem F W R), (isPolyMapInCoords map cs₃ cs₄) := by
    intro h cs₃ cs₄
    apply (polyInOnePolyInAnother map cs₁ cs₂)
    exact h

/-Define the property of being a polynomial map (existence of two coordinate
  systems in which it is polynomial in coordinates)-/
def isPolyMap (map: P → R) : Prop :=
  ∃ (cs₁ : CoordinateSystem F V P) (cs₂ : CoordinateSystem F W R),
    isPolyMapInCoords map cs₁ cs₂
