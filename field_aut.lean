import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs


open Matrix BigOperators
open scoped MatrixGroups
noncomputable section

abbrev SL3 (A : Type*) [CommRing A] :=
  Matrix.SpecialLinearGroup (Fin 3) A
  
/-
DO NOT CHANGE
-/
abbrev GL3 (A : Type*) [CommRing A] : Type _ :=
  GL (Fin 3) A

/-
DO NOT CHANGE
-/
variable (R : Type*) [CommRing R] [Invertible (2 : R)]

/-
DO NOT CHANGE
-/
abbrev AutSL3 : Type _ :=
  SL3 R ≃* SL3 R

/-
DO NOT CHANGE
-/
def ringAutMapSL3 (σ : R ≃+* R) (x : SL3 R) : SL3 R :=
  ⟨((x : Matrix (Fin 3) (Fin 3) R).map σ), by
    -- Need determinant compatibility with entrywise ring automorphisms.
   calc
      ((x : Matrix (Fin 3) (Fin 3) R).map ⇑σ).det
          = σ ((x : Matrix (Fin 3) (Fin 3) R).det) := by
              simpa only [RingEquiv.mapMatrix_apply] using
                (σ.map_det
                  (x : Matrix (Fin 3) (Fin 3) R)).symm
      _ = 1 := by simp [x.property]⟩


/-
DO NOT CHANGE
-/
def ringAutSL3 (σ : R ≃+* R) : AutSL3 R where
  toFun := ringAutMapSL3 R σ
  invFun := ringAutMapSL3 R σ.symm

  left_inv := by
    intro x
    apply Subtype.ext
    dsimp [ringAutMapSL3]
    simp
    ext i j
    dsimp [map]
    exact RingEquiv.symm_apply_apply σ _



  right_inv := by
    intro x
    apply Subtype.ext
    dsimp [ringAutMapSL3]
    simp
    ext i j
    dsimp [map]
    exact RingEquiv.symm_apply_apply σ.symm _


  map_mul' := by
    intro x y
    apply Subtype.ext
    ext i j
    simp [ringAutMapSL3, Matrix.mul_apply]


/-
DO NOT CHANGE
-/
def innerAutSL3byGL3 (g : GL3 R) : MulAut (SL3 R) where
  toFun := fun x => ⟨g * Matrix.SpecialLinearGroup.toGL x * g⁻¹, by
    simp [Matrix.det_mul,  Ring.mul_inverse_cancel]⟩
  invFun := fun x =>⟨g⁻¹ * Matrix.SpecialLinearGroup.toGL x * g, by
    simp [Matrix.det_mul, Ring.inverse_mul_cancel]⟩

  left_inv := by
    intro x
    simp [mul_assoc]

  right_inv := by
    intro x
    simp [mul_assoc]

  map_mul' := by
    intro x y
    apply Subtype.ext
    simp [mul_assoc]

def invTransposeMap (x : SL3 R) : SL3 R :=
  ⟨(((x⁻¹ : SL3 R) : Matrix (Fin 3) (Fin 3) R).transpose), by
    rw [Matrix.det_transpose]
    exact (x⁻¹ : SL3 R).property⟩

/-
DO NOT CHANGE
-/
def invTransposeAutSL3 : AutSL3 R where
  toFun := invTransposeMap R
  invFun := invTransposeMap R

  left_inv := by
    intro x
    apply Subtype.ext

    simp only [
    invTransposeMap,
    Matrix.SpecialLinearGroup.coe_mk,
    Matrix.SpecialLinearGroup.coe_inv
    ]
    rw [← Matrix.adjugate_transpose]
    simp only [Matrix.transpose_transpose]

    rw [Matrix.adjugate_adjugate _ (by decide)]
    simp [x.property]

  right_inv := by
    intro x
    apply Subtype.ext

    simp only [
    invTransposeMap,
    Matrix.SpecialLinearGroup.coe_mk,
    Matrix.SpecialLinearGroup.coe_inv
    ]
    rw [← Matrix.adjugate_transpose]
    simp only [Matrix.transpose_transpose]

    rw [Matrix.adjugate_adjugate _ (by decide)]
    simp [x.property]

  map_mul' := by
    intro x y
    apply Subtype.ext
    simp [invTransposeMap, Matrix.transpose_mul]





theorem zero_if_neg_eq {x : R} (h : -x = x) : 0 = x := by
  -- TODO: make sure group 4 uses those
  rw [← one_mul x, ← invOf_mul_self (2 : R), mul_assoc, two_mul]
  nth_rw 2 [h]
  rw [← sub_eq_add_neg, sub_self, mul_zero]

theorem zero_if_eq_neg {x : R} (h : x = -x) : 0 = x := zero_if_neg_eq R h.symm

namespace FieldAutomorpisms

/-
DO NOT CHANGE
-/
variable (F : Type*) [Field F] [Invertible (2 : F)]



set_option linter.unusedSectionVars false

def d1 : Matrix (Fin 3) (Fin 3) (R) :=
  Matrix.diagonal ![1, -1, -1]

private lemma d1Mat: (d1 R) = !![1, 0, 0; 0, -1, 0; 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

def d2 : Matrix (Fin 3) (Fin 3) (R) :=
  Matrix.diagonal ![-1, 1, -1]

private lemma d2Mat: (d2 R) = !![-1, 0, 0; 0, 1, 0; 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

def d3 : Matrix (Fin 3) (Fin 3) (R) :=
  Matrix.diagonal ![-1, -1, 1]

private lemma d3Mat: (d3 R) = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

def d1SL : SL3 R :=
  ⟨d1 R, by
    simp [d1, Matrix.det_diagonal, Fin.prod_univ_three]
  ⟩

def d2SL : SL3 R :=
  ⟨d2 R, by
    simp [d2, Matrix.det_diagonal, Fin.prod_univ_three]
  ⟩

def d3SL : SL3 R :=
  ⟨d3 R, by
    simp [d3, Matrix.det_diagonal, Fin.prod_univ_three]
  ⟩

theorem diag_preserved_after_change_of_basis
    (φ : AutSL3 F) :
    ∃ g : GL3 F,
      innerAutSL3byGL3 F g (φ (d1SL F)) = d1SL F ∧
      innerAutSL3byGL3 F g (φ (d2SL F)) = d2SL F ∧
      innerAutSL3byGL3 F g (φ (d3SL F)) = d3SL F := by
  sorry


def w1 : Matrix (Fin 3) (Fin 3) (R) :=
    !![0, 1, 0;
     -1, 0, 0;
     0, 0, 1]

def w2 : Matrix (Fin 3) (Fin 3) (R) :=
    !![1, 0, 0;
     0, 0, 1;
     0, -1, 0]

def w1SL : SL3 R :=
  ⟨w1 R, by
    simp [w1, Matrix.det_fin_three]
  ⟩

def w2SL : SL3 R :=
  ⟨w2 R, by
    simp [w2, Matrix.det_fin_three]
  ⟩

theorem w_preserved
    (φ : AutSL3 F) :
    ∃ g : GL3 F,
      innerAutSL3byGL3 F g (φ (d1SL F)) = d1SL F ∧
      innerAutSL3byGL3 F g (φ (d2SL F)) = d2SL F ∧
      innerAutSL3byGL3 F g (φ (d3SL F)) = d3SL F ∧
      innerAutSL3byGL3 F g (φ (w1SL F)) = w1SL F ∧
      innerAutSL3byGL3 F g (φ (w2SL F)) = w2SL F := by
  rcases diag_preserved_after_change_of_basis F φ with ⟨g, hd1, hd2, hd3⟩
  let v1 := (innerAutSL3byGL3 F g (φ (w1SL F))).val
  let v2 := (innerAutSL3byGL3 F g (φ (w2SL F))).val
  have hv1: ∃ l : F, IsUnit l ∧ v1 =
    !![0,    l, 0;
       -l⁻¹, 0, 0;
       0,    0, 1] := by
    use v1 0 1
    have first_rep:
          !![v1 0 0, v1 0 1, 0;
             v1 1 0, v1 1 1, 0;
             0,      0,      v1 2 2] = v1 := by
      have (i : Fin 3) (j : Fin 3):
           !![v1 0 0,  v1 0 1,  -v1 0 2;
              v1 1 0,  v1 1 1,  -v1 1 2;
              -v1 2 0, -v1 2 1, v1 2 2] i j = v1 i j := by
        have: (d3 F) * v1 * (d3 F) = v1 := by
          have: (d3SL F) * (w1SL F) * (d3SL F) = w1SL F := by
            have: (d3 F) * (w1 F) * (d3 F) = w1 F := by
              simp only [w1]
              rw [d3Mat, Matrix.mul_fin_three, Matrix.mul_fin_three]
              simp only [mul_zero, mul_neg, mul_one, neg_zero, add_zero, neg_neg, zero_add]
            apply Subtype.ext this
          have: (innerAutSL3byGL3 F g (φ ((d3SL F) * (w1SL F) * (d3SL F)))) = innerAutSL3byGL3 F g (φ (w1SL F)) := by
            rw [this]
          rw [map_mul, map_mul, map_mul, map_mul, hd3] at this
          simp only [v1]
          nth_rw 2 [← this]
          exact ext fun i => congrFun rfl
        rw [d3Mat] at this
        nth_rw 10 [← this]
        have: !![v1 0 0, v1 0 1, v1 0 2;
                 v1 1 0, v1 1 1, v1 1 2;
                 v1 2 0, v1 2 1, v1 2 2] = v1 := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp
        nth_rw 10 [← this]
        fin_cases i <;> fin_cases j <;> simp
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      · exact zero_if_neg_eq F (this 0 2)
      · exact zero_if_neg_eq F (this 1 2)
      · exact zero_if_neg_eq F (this 2 0)
      · exact zero_if_neg_eq F (this 2 1)
    have: v1 * (d1 F) = (d2 F) * v1 := by
      have: v1 * (d1SL F) = (d2SL F) * v1 := by
        have: (w1SL F) * (d1SL F) = (d2SL F) * (w1SL F) := by
          have: (w1 F) * (d1 F) = (d2 F) * (w1 F) := by
            simp only [w1]
            rw [d1Mat, d2Mat]
            simp only [add_zero, zero_add,
                       neg_zero, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
                       vecMul_cons, head_cons, neg_smul, one_smul, neg_cons,
                       neg_empty, tail_cons, zero_smul, empty_vecMul, empty_mul,
                       Equiv.symm_apply_apply]
          apply Subtype.ext this
        have: (innerAutSL3byGL3 F g (φ ((w1SL F) * (d1SL F)))) = innerAutSL3byGL3 F g (φ ((d2SL F) * (w1SL F))) := by
          rw [this]
        rw [map_mul, map_mul, map_mul, map_mul, hd2, hd1] at this
        simp only [v1]
        rw [← SpecialLinearGroup.coe_mul, this]
        rfl
      exact this
    rw [d1Mat, d2Mat] at this
    rw [← first_rep] at this
    simp only [Fin.isValue, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
               vecMul_cons, head_cons, smul_cons, smul_eq_mul,
               mul_one, mul_zero, smul_empty, tail_cons, mul_neg,
               zero_smul, empty_vecMul, add_zero, add_cons, zero_add,
               empty_add_empty, empty_mul, Equiv.symm_apply_apply,
               neg_smul, one_smul, neg_cons, neg_zero, neg_empty,
               EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true, true_and] at this
    have second_rep:
          !![0,      v1 0 1, 0;
             v1 1 0, 0,      0;
             0,      0,      v1 2 2] = v1 := by
      nth_rw 4 [← first_rep]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      · exact zero_if_eq_neg F this.left
      · exact zero_if_neg_eq F this.right
    have: v1 * v1 = d3 F := by
      have: (w1SL F) * (w1SL F) = (d3SL F) := by
        have: (w1 F) * (w1 F) = (d3 F) := by
          simp only [w1]
          rw [d3Mat, Matrix.mul_fin_three]
          simp only [mul_zero, mul_neg, mul_one, zero_add, add_zero, neg_zero]
        apply Subtype.ext this
      have: (innerAutSL3byGL3 F g (φ ((w1SL F) * (w1SL F)))) = innerAutSL3byGL3 F g (φ (d3SL F)) := by
        rw [this]
      rw [map_mul, map_mul, hd3] at this
      simp only [v1]
      rw [← SpecialLinearGroup.coe_mul, this]
      rfl
    have det_v1: det v1 = 1 := by
      -- have: det (v1 * v1) = 1 := by
      --   rw [this]
      --   simp only [d3]
      --   rw [Matrix.det_diagonal, Fin.prod_univ_three]
      --   simp
      -- rw [Matrix.det_mul, ← pow_two] at this
      -- sorry
      rw [SpecialLinearGroup.det_coe]
    have not_zero_v101: IsUnit (v1 0 1) := by
      apply IsUnit.mk0
      by_contra
      rw [← second_rep, this, Matrix.det_fin_three] at det_v1
      simp only [Fin.isValue, of_apply, cons_val', cons_val_zero,
                 cons_val_fin_one, cons_val_one, mul_zero, cons_val,
                 zero_mul, sub_self, add_zero, zero_ne_one] at det_v1
    rw [← second_rep, d3Mat] at this
    simp only [Fin.isValue, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
               vecMul_cons, head_cons, zero_smul, tail_cons,
               smul_cons, smul_eq_mul, mul_zero, smul_empty,
               empty_vecMul, add_zero, zero_add, empty_mul, Equiv.symm_apply_apply,
               EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true, true_and] at this
    have third_rep:
          !![0,           v1 0 1, 0;
             -(v1 0 1)⁻¹, 0,      0;
             0,           0,      1] = v1 := by
      nth_rw 3 [← second_rep]
      have det_calc: 1 = -((v1 0 1) * (v1 1 0)) * (v1 2 2) := by
        nth_rw 1 [← det_v1, ← second_rep]
        rw [Matrix.det_fin_three]
        simp only [Fin.isValue, of_apply, cons_val', cons_val_zero,
                   cons_val_fin_one, cons_val_one, mul_zero, cons_val,
                   zero_mul, sub_self, zero_sub, add_zero, sub_zero, neg_mul]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      · rw [neg_eq_neg_one_mul, ← this.right.left, mul_assoc, not_zero_v101.mul_inv_cancel, mul_one]
      · rw [this.left, neg_neg, one_mul] at det_calc
        exact det_calc
    split_ands
    · exact not_zero_v101
    · rw [third_rep]
  have hv2: ∃ l : F, IsUnit l ∧ v2 =
    !![1, 0,    0;
       0, 0,    l;
       0, -l⁻¹, 0] := by
    use v2 1 2
    have first_rep:
          !![v2 0 0, 0,      0;
             0,      v2 1 1, v2 1 2;
             0,      v2 2 1, v2 2 2] = v2 := by
      have (i : Fin 3) (j : Fin 3):
           !![v2 0 0,   -v2 0 1,  -v2 0 2;
              -v2 1 0,  v2 1 1,   v2 1 2;
              -v2 2 0,  v2 2 1,   v2 2 2] i j = v2 i j := by
        have: (d1 F) * v2 * (d1 F) = v2 := by
          have: (d1SL F) * (w2SL F) * (d1SL F) = w2SL F := by
            have: (d1 F) * (w2 F) * (d1 F) = w2 F := by
              simp only [w2]
              rw [d1Mat, Matrix.mul_fin_three, Matrix.mul_fin_three]
              simp only [mul_one, mul_zero, add_zero, mul_neg, neg_zero, zero_add, neg_neg]
            apply Subtype.ext this
          have: (innerAutSL3byGL3 F g (φ ((d1SL F) * (w2SL F) * (d1SL F)))) = innerAutSL3byGL3 F g (φ (w2SL F)) := by
            rw [this]
          rw [map_mul, map_mul, map_mul, map_mul, hd1] at this
          simp only [v2]
          nth_rw 2 [← this]
          simp only [SpecialLinearGroup.coe_mul]
          rfl
        rw [d1Mat] at this
        nth_rw 10 [← this]
        have: !![v2 0 0, v2 0 1, v2 0 2;
                 v2 1 0, v2 1 1, v2 1 2;
                 v2 2 0, v2 2 1, v2 2 2] = v2 := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp
        nth_rw 10 [← this]
        fin_cases i <;> fin_cases j <;> simp
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      · exact zero_if_neg_eq F (this 0 1)
      · exact zero_if_neg_eq F (this 0 2)
      · exact zero_if_neg_eq F (this 1 0)
      · exact zero_if_neg_eq F (this 2 0)
    have: v2 * (d3 F) = (d2 F) * v2 := by
      have: v2 * (d3SL F) = (d2SL F) * v2 := by
        have: (w2SL F) * (d3SL F) = (d2SL F) * (w2SL F) := by
          have: (w2 F) * (d3 F) = (d2 F) * (w2 F) := by
            simp only [w2]
            rw [d3Mat, d2Mat]
            simp only [add_zero, neg_zero,
                       zero_add, neg_neg, cons_mul, Nat.succ_eq_add_one,
                       Nat.reduceAdd, vecMul_cons, head_cons, neg_smul,
                       one_smul, neg_cons, neg_empty, tail_cons, zero_smul, empty_vecMul,
                       empty_mul, Equiv.symm_apply_apply]
          apply Subtype.ext this
        have: (innerAutSL3byGL3 F g (φ ((w2SL F) * (d3SL F)))) = innerAutSL3byGL3 F g (φ ((d2SL F) * (w2SL F))) := by
          rw [this]
        rw [map_mul, map_mul, map_mul, map_mul, hd2, hd3] at this
        simp only [v2]
        rw [← SpecialLinearGroup.coe_mul, this]
        rfl
      exact this
    rw [d3Mat, d2Mat] at this
    rw [← first_rep] at this
    simp only [Fin.isValue, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
               vecMul_cons, head_cons, smul_cons, smul_eq_mul,
               mul_neg, mul_one, mul_zero, smul_empty, tail_cons,
               zero_smul, empty_vecMul, add_zero, add_cons, zero_add,
               empty_add_empty, empty_mul, Equiv.symm_apply_apply,
               neg_smul, one_smul, neg_cons, neg_zero, neg_empty,
               EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true, true_and] at this
    have second_rep:
          !![v2 0 0, 0,      0;
             0,      0, v2 1 2;
             0,      v2 2 1, 0] = v2 := by
      nth_rw 4 [← first_rep]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      · exact zero_if_neg_eq F this.left
      · exact zero_if_eq_neg F this.right
    have: v2 * v2 = d1 F := by
      have: (w2SL F) * (w2SL F) = (d1SL F) := by
        have: (w2 F) * (w2 F) = (d1 F) := by
          simp only [w2]
          rw [d1Mat, Matrix.mul_fin_three]
          simp only [mul_one, mul_zero, add_zero, mul_neg, neg_zero, zero_add]
        apply Subtype.ext this
      have: (innerAutSL3byGL3 F g (φ ((w2SL F) * (w2SL F)))) = innerAutSL3byGL3 F g (φ (d1SL F)) := by
        rw [this]
      rw [map_mul, map_mul, hd1] at this
      simp only [v2]
      rw [← SpecialLinearGroup.coe_mul, this]
      rfl
    have det_v2: det v2 = 1 := by
      rw [SpecialLinearGroup.det_coe]
    have not_zero_v212: IsUnit (v2 1 2) := by
      apply IsUnit.mk0
      by_contra
      rw [← second_rep, this, Matrix.det_fin_three] at det_v2
      simp only [Fin.isValue, of_apply, cons_val', cons_val_zero,
                 cons_val_fin_one, cons_val_one, mul_zero, cons_val,
                 zero_mul, sub_self, add_zero, zero_ne_one] at det_v2
    rw [← second_rep, d1Mat] at this
    simp only [Fin.isValue, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
               vecMul_cons, head_cons, smul_cons, smul_eq_mul,
               mul_zero, smul_empty, tail_cons, zero_smul, empty_vecMul,
               add_zero, zero_add, empty_mul, Equiv.symm_apply_apply,
               EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true, true_and] at this
    have third_rep:
          !![1, 0,           0;
             0, 0,           v2 1 2;
             0, -(v2 1 2)⁻¹, 0] = v2 := by
      nth_rw 3 [← second_rep]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      have det_calc: 1 = - (v2 0 0) * (v2 1 2) * (v2 2 1) := by
        nth_rw 1 [← det_v2, ← second_rep]
        rw [Matrix.det_fin_three]
        simp only [Fin.isValue, of_apply, cons_val', cons_val_zero,
                   cons_val_fin_one, cons_val_one, mul_zero, cons_val,
                   zero_sub, sub_zero, zero_mul, add_zero, neg_mul]
      · rw [mul_assoc, this.right.left, neg_mul_neg, mul_one] at det_calc
        exact det_calc
      · rw [neg_eq_neg_one_mul, ← this.right.right, mul_assoc, not_zero_v212.mul_inv_cancel, mul_one]
    split_ands
    · exact not_zero_v212
    · rw [third_rep]
  rcases hv1 with ⟨l1, l1unit, hl1⟩
  rcases hv2 with ⟨l2, l2unit, hl2⟩
  use ⟨!![l1⁻¹, 0, 0;
          0,   1, 0;
          0,   0, l2] * g,
      g⁻¹ * !![l1, 0, 0;
                0,   1, 0;
                0,   0, l2⁻¹],
      by
        simp only [cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
                   empty_mul, Equiv.symm_apply_apply, coe_units_inv,
                   vecMul_vecMul, mul_inv_cancel_left_of_invertible,
                   vecMul_cons, head_cons, smul_cons, smul_eq_mul, mul_zero,
                   smul_empty, tail_cons, zero_smul, empty_vecMul, add_zero, one_smul, zero_add]
        rw [l1unit.inv_mul_cancel, l2unit.mul_inv_cancel]
        ext i j
        fin_cases i <;> fin_cases j <;> simp,
      by
        rw [← mul_assoc, mul_assoc _ !![l1, 0, 0; 0, 1, 0; 0, 0, l2⁻¹]]
        simp only [coe_units_inv, cons_mul, Nat.succ_eq_add_one,
                   Nat.reduceAdd, vecMul_cons, head_cons, smul_cons,
                   smul_eq_mul, mul_zero, smul_empty, tail_cons,
                   zero_smul, empty_vecMul, add_zero, one_smul, zero_add, empty_mul,
                   Equiv.symm_apply_apply]
        rw [l1unit.mul_inv_cancel, l2unit.inv_mul_cancel]
        have: (!![1, 0, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) = 1 := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp
        rw [this, mul_one]
        simp only [inv_mul_of_invertible]
      ⟩
  simp only [innerAutSL3byGL3, MulEquiv.coe_mk, Equiv.coe_fn_mk, Units.inv_mk]
  split_ands
  · congr
    rw [← mul_assoc, mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2], mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2]]
    have: g * SpecialLinearGroup.toGL (φ (d1SL F)) * g⁻¹ = d1 F := congrArg Subtype.val hd1
    rw [this, d1Mat]
    simp only [cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons,
               head_cons, smul_cons, smul_eq_mul, mul_one,
               mul_zero, smul_empty, tail_cons, zero_smul,empty_vecMul,
               add_zero, one_smul, zero_add, mul_neg, empty_mul,
               Equiv.symm_apply_apply, neg_smul, neg_cons, neg_zero,
               neg_empty, EmbeddingLike.apply_eq_iff_eq, vecCons_inj,
               and_true, neg_inj, true_and]
    exact ⟨ l1unit.inv_mul_cancel, l2unit.mul_inv_cancel ⟩
  · congr
    rw [← mul_assoc, mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2], mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2]]
    have: g * SpecialLinearGroup.toGL (φ (d2SL F)) * g⁻¹ = d2 F := congrArg Subtype.val hd2
    rw [this, d2Mat]
    simp only [cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons,
               head_cons, smul_cons, smul_eq_mul, mul_one,
               mul_zero, smul_empty, tail_cons, zero_smul,empty_vecMul,
               add_zero, one_smul, zero_add, mul_neg, empty_mul,
               Equiv.symm_apply_apply, neg_smul, neg_cons, neg_zero,
               neg_empty, EmbeddingLike.apply_eq_iff_eq, vecCons_inj,
               and_true, neg_inj, true_and]
    exact ⟨ l1unit.inv_mul_cancel, l2unit.mul_inv_cancel ⟩
  · congr
    rw [← mul_assoc, mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2], mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2]]
    have: g * SpecialLinearGroup.toGL (φ (d3SL F)) * g⁻¹ = d3 F := congrArg Subtype.val hd3
    rw [this, d3Mat]
    simp only [cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons,
               head_cons, smul_cons, smul_eq_mul, mul_one,
               mul_zero, smul_empty, tail_cons, zero_smul,empty_vecMul,
               add_zero, one_smul, zero_add, mul_neg, empty_mul,
               Equiv.symm_apply_apply, neg_smul, neg_cons, neg_zero,
               neg_empty, EmbeddingLike.apply_eq_iff_eq, vecCons_inj,
               and_true, neg_inj, true_and]
    exact ⟨ l1unit.inv_mul_cancel, l2unit.mul_inv_cancel ⟩
  · congr
    simp only [v1, innerAutSL3byGL3, MulEquiv.coe_mk, Equiv.coe_fn_mk] at hl1
    rw [← mul_assoc, mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2], mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2]]
    rw [hl1]
    simp only [w1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · rw [l1unit.inv_mul_cancel]
    · rw [l1unit.inv_mul_cancel]
    · rw [l2unit.mul_inv_cancel]
  · congr
    simp only [v2, innerAutSL3byGL3, MulEquiv.coe_mk, Equiv.coe_fn_mk] at hl2
    rw [← mul_assoc, mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2], mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2]]
    rw [hl2]
    simp only [w2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · rw [l1unit.inv_mul_cancel]
    · rw [l2unit.mul_inv_cancel]
    · rw [l2unit.mul_inv_cancel]


def x12 : Matrix (Fin 3) (Fin 3) (R) :=
    !![1, 1, 0;
     0, 1, 0;
     0, 0, 1]

def x12SL : SL3 R :=
  ⟨x12 R, by
    simp [x12, Matrix.det_fin_three]
  ⟩



def graphChoiceSL3 (ε : Bool) : AutSL3 R :=
  if ε then invTransposeAutSL3 R else (1 : AutSL3 R)


theorem x12_preserved (φ : AutSL3 (F)) : ∃ (g : GL3 F) (ε : Bool),
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (d1SL F))) = d1SL F ∧
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (d2SL F))) = d2SL F ∧
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (d3SL F))) = d3SL F ∧
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (w1SL F))) = w1SL F ∧
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (w2SL F))) = w2SL F ∧
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (x12SL F))) = x12SL F := by
  sorry


def IsTransvectionSL3 (x : SL3 R) : Prop :=
  ∃ i j : Fin 3, ∃ c : R,
    i ≠ j ∧
    (x : Matrix (Fin 3) (Fin 3) R) =
      Matrix.transvection i j c

theorem transv_to_transv_same_coeff (φ : AutSL3 (R)) :
(φ (d1SL R)  = d1SL R ∧
φ (d2SL R)  = d2SL R ∧
φ (d3SL R)  = d3SL R ∧
φ (w1SL R) = w1SL R ∧
φ (w2SL R) = w2SL R ∧
φ (x12SL R) = x12SL R) → ∃ (f : R ≃+* R), ∀ (E : SL3 R) , (IsTransvectionSL3 R E) → φ E = E.map f:= by sorry



/-
DO NOT CHANGE
-/
theorem field_class
    (φ : AutSL3 F) :
    ∃ (σ : F ≃+* F) (ε : Bool) (g : GL (Fin 3) F),
      ∀ (x : SL3 F),
        φ x =
            ringAutSL3 F σ ((graphChoiceSL3 F ε) (innerAutSL3byGL3 F g x))
             := by
  sorry

end FieldAutomorpisms
