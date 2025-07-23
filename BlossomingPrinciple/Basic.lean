import Mathlib.LinearAlgebra.AffineSpace.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Field.Defs

import Mathlib.Algebra.MvPolynomial.Basic


open Affine
notation "VectorSpace" => Module

section PolynomialMaps

/- Define a coordinate system of an affine space as a pair
 of a point (origin) and vector space basis. -/
structure CoordinateSystem (F V P: Type*) [Field F] [AddCommGroup V] [VectorSpace F V]
  [AffineSpace V P] where
  ι : Type*
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
structure PolynomialMapInCoords where
  cs₁ : CoordinateSystem F V P
  cs₂ : CoordinateSystem F W R
  map : P → R
  polys : cs₂.ι → MvPolynomial cs₁.ι F
  --map_poly_equality: ∀(p : P)(i : cs₂.ι)
