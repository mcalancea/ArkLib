/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Data.ENat.Lattice

/-!
  # Basics of Coding Theory

  We define a general code `C` to be a subset of `n → R` for some finite index set `n` and some
  target type `R`.

  We can then specialize this notion to various settings. For `[CommSemiring R]`, we define a linear
  code to be a linear subspace of `n → R`. We also define the notion of generator matrix and
  (parity) check matrix.

  ## Main Definitions

  - `codeDist C`: The Hamming distance of a code `C`, defined as the infimum (in `ℕ∞`) of the
    Hamming distances between any two distinct elements of `C`. This is noncomputable.

  - `codeDist' C`: A computable version of `codeDist C`, assuming `C` is a `Fintype`.

  We define the block length, rate, and distance of `C`. We prove simple properties of linear codes
  such as the singleton bound.
-/


variable {n : Type*} [Fintype n] {R : Type*} [DecidableEq R]

section Distance

-- Notation for Hamming distance
notation "Δ₀(" u ", " v ")" => hammingDist u v

notation "‖" u "‖₀" => hammingNorm u

/-- The Hamming distance of a code `C` is the minimum Hamming distance between any two distinct
  elements of the code.
cd
We formalize this as the infimum `sInf` over all `d : ℕ` such that there exist `u v : n → R` in the
code with `u ≠ v` and `hammingDist u v ≤ d`. If none exists, then we define the distance to be `0`.
-/
noncomputable def codeDist (C : Set (n → R)) : ℕ :=
  sInf {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ Δ₀( u, v ) ≤ d}

-- TODO: rewrite this file using existing `(e)infsep` definitions

instance : EDist (n → R) where
  edist := fun u v => hammingDist u v

instance : Dist (n → R) where
  dist := fun u v => hammingDist u v

noncomputable def eCodeDistNew (C : Set (n → R)) : ENNReal := C.einfsep

noncomputable def codeDistNew (C : Set (n → R)) : ℝ := C.infsep

notation "‖" C "‖₀" => codeDist C

/-- The distance from a vector `u` to a code `C` is the minimum Hamming distance between `u`
and any element of `C`. -/
noncomputable def distFromCode (u : n → R) (C : Set (n → R)) : ℕ∞ :=
  sInf {d | ∃ v ∈ C, hammingDist u v ≤ d}

notation "Δ₀(" u ", " C ")" => distFromCode u C

@[simp]
theorem codeDist_empty : ‖ (∅ : Set (n → R) ) ‖₀ = 0 := by simp [codeDist]

@[simp]
theorem codeDist_subsingleton {C : Set (n → R)} [Subsingleton C] : ‖C‖₀ = 0 := by
  simp only [codeDist]
  have {d : ℕ} : (∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ d) = False := by
    have h := @Subsingleton.allEq C _
    simp_all; intro a ha b hb hab
    have hEq : a = b := h a ha b hb
    simp_all
  have : {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ d} = (∅ : Set ℕ) := by
    apply Set.eq_empty_iff_forall_not_mem.mpr
    simp [this]
  simp [this]

@[simp]
theorem codeDist_le_card (C : Set (n → R)) : codeDist C ≤ Fintype.card n := by
  by_cases h : Subsingleton C
  · simp
  · simp at h
    unfold Set.Nontrivial at h
    obtain ⟨u, hu, v, hv, huv⟩ := h
    refine Nat.sInf_le ?_
    simp
    refine ⟨u, And.intro hu ⟨v, And.intro hv ⟨huv, hammingDist_le_card_fintype⟩⟩⟩

/-- If `u` and `v` are two codewords of `C` with distance less than `codeDist C`,
then they are the same. -/
theorem eq_of_lt_codeDist {C : Set (n → R)} {u v : n → R} (hu : u ∈ C) (hv : v ∈ C)
    (huv : Δ₀(u, v) < ‖C‖₀) : u = v := by
  simp only [codeDist] at huv
  by_contra hNe
  push_neg at hNe
  revert huv
  simp
  refine Nat.sInf_le ?_
  simp only [Set.mem_setOf_eq]
  refine ⟨u, And.intro hu ⟨v, And.intro hv ⟨hNe, le_rfl⟩⟩⟩

@[simp]
theorem distFromCode_of_empty (u : n → R) : Δ₀(u, (∅ : Set (n → R))) = ⊤ := by
  simp [distFromCode]

theorem distFromCode_eq_top_iff_empty (u : n → R) (C : Set (n → R)) : Δ₀(u, C) = ⊤ ↔ C = ∅ := by
  apply Iff.intro
  · simp only [distFromCode]
    intro h
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro v hv
    apply sInf_eq_top.mp at h
    revert h
    simp
    refine ⟨Fintype.card n, v, And.intro hv ⟨?_, ?_⟩⟩
    · norm_num; exact hammingDist_le_card_fintype
    · norm_num
  · intro h; subst h; simp

@[simp]
theorem distFromCode_of_mem (C : Set (n → R)) {u : n → R} (h : u ∈ C) : Δ₀(u, C) = 0 := by
  simp only [distFromCode]
  apply ENat.sInf_eq_zero.mpr
  simp [h]

theorem distFromCode_eq_zero_iff_mem (C : Set (n → R)) (u : n → R) : Δ₀(u, C) = 0 ↔ u ∈ C := by
  apply Iff.intro
  · simp only [distFromCode]
    intro h
    apply ENat.sInf_eq_zero.mp at h
    revert h
    simp
  · intro h; exact distFromCode_of_mem C h

theorem distFromCode_eq_of_lt_half_codeDist (C : Set (n → R)) (u : n → R) {v w : n → R}
    (hv : v ∈ C) (hw : w ∈ C) (huv : Δ₀(u, v) < ‖C‖₀ / 2) (hvw : Δ₀(u, w) < ‖C‖₀ / 2) : v = w := by
  apply eq_of_lt_codeDist hv hw
  calc
    Δ₀(v, w) ≤ Δ₀(v, u) + Δ₀(u, w) := by exact hammingDist_triangle v u w
    _ = Δ₀(u, v) + Δ₀(u, w) := by simp only [hammingDist_comm]
    _ < ‖C‖₀ / 2 + ‖C‖₀ / 2 := by omega
    _ ≤ ‖C‖₀ := by omega

section Computable

/-- Computable version of the Hamming distance of a code `C`, assuming `C` is a `Fintype`.

The return type is `ℕ∞` since we use `Finset.min`. -/
def codeDist' (C : Set (n → R)) [Fintype C] : ℕ∞ :=
  Finset.min <| ((@Finset.univ (C × C) _).filter (fun p => p.1 ≠ p.2)).image
    (fun ⟨u, v⟩ => hammingDist u.1 v.1)

notation "‖" C "‖₀'" => codeDist' C

variable {C : Set (n → R)} [Fintype C]

@[simp]
theorem codeDist'_empty : ‖(∅ : Set (n → R))‖₀' = ⊤ := by
  simp [codeDist']

@[simp]
theorem codeDist'_subsingleton [Subsingleton C] : ‖C‖₀' = ⊤ := by
  simp [codeDist']
  apply Finset.min_eq_top.mpr
  simp [Finset.filter_eq_empty_iff]
  have h := @Subsingleton.elim C _
  simp_all
  exact h

theorem codeDist'_eq_codeDist : ‖C‖₀'.toNat = ‖C‖₀ := by
  by_cases h : Subsingleton C
  · simp
  · simp [codeDist, codeDist']
    have : codeDist' C ≠ ⊤ := by sorry
    sorry
    -- apply (ENat.toNat_eq_iff this).mp
    -- apply Finset.min_eq_top.mp
    -- simp [this]

/-- Computable version of the distance from a vector `u` to a code `C`, assuming `C` is a `Fintype`.
  -/
def distFromCode' (C : Set (n → R)) [Fintype C] (u : n → R) : ℕ∞ :=
  Finset.min <| (@Finset.univ C _).image (fun v => hammingDist u v.1)

notation "Δ₀'(" u ", " C ")" => distFromCode' C u

end Computable

end Distance

section Linear

variable {k : Type*} [Fintype k] [CommSemiring R]

/-- Define a linear code from its generator matrix -/
def codeByGenMatrix (G : Matrix k n R) : Submodule R (n → R) :=
  LinearMap.range G.vecMulLinear
  -- Submodule.span R (Set.range G)

/-- Define a linear code from its (parity) check matrix -/
def codeByCheckMatrix (H : Matrix k n R) : Submodule R (n → R) :=
  LinearMap.ker H.mulVecLin

/-- The Hamming distance of a linear code can also be defined as the minimum Hamming norm of a
  non-zero vector in the code -/
noncomputable def linearCodeDist (C : Submodule R (n → R)) : ℕ :=
  sInf {d | ∃ u ∈ C, u ≠ 0 ∧ hammingNorm u ≤ d}

-- Require `[CommRing R]`
theorem codeDist_eq_linearCodeDist (C : Submodule R (n → R)) :
    codeDist C.carrier = linearCodeDist C := by
  simp [codeDist, linearCodeDist]
  congr; unfold setOf; funext d
  apply Eq.propIntro <;> intro h
  · obtain ⟨u, hu, v, hv, huv, hDist⟩ := h
    -- let w := u - v
    -- have hw : w ∈ C := by simp [Submodule.add_mem]
    -- refine ⟨w, And.intro hw ⟨v, And.intro hv ⟨huv, ?_⟩⟩⟩
    sorry
  · obtain ⟨u, hu, hNorm, hDist⟩ := h
    -- refine ⟨u, And.intro hu ⟨v, And.intro hv ⟨huv, ?_⟩⟩⟩
    sorry

section Computable

variable [DecidableEq n] [Fintype R]

/-- A computable version of the Hamming distance of a linear code `C`. -/
def linearCodeDist' (C : Submodule R (n → R)) [DecidablePred (· ∈ C)] : ℕ∞ :=
  Finset.min <| ((Finset.univ (α := C)).filter (fun v => v ≠ 0)).image (fun v => hammingNorm v.1)

end Computable

/-- The interleaving of a linear code `C` over index set `ι` is the submodule spanned by
`ι × n`-matrices whose rows are elements of `C`. -/
def interleaveCode (C : Submodule R (n → R)) (ι : Type*) : Submodule R ((ι × n) → R) :=
  Submodule.span R {v | ∀ i, ∃ c ∈ C, c = fun j => v (i, j)}

notation:20 C "^⋈" ι => interleaveCode C ι

-- instance : Fintype (interleaveCode C ι) := sorry

/-- Interleave two functions `u v : α → β`. -/
def Function.interleave₂ {α β : Type*} (u v : α → β) : (Fin 2) × α → β :=
  Function.uncurry (fun a => if a = 0 then u else v)

notation:20 u "⋈" v => Function.interleave₂ u v

end Linear

variable [Finite R]

open Fintype

def projection (S : Finset n) (w : n → R) : S → R :=
  fun i => w i.val


theorem projection_injective
    (C : Set (n → R))
    (nontriv: ‖C‖₀ ≥ 1)
    (S : Finset n)
    (hS : card S = card n - ‖C‖₀ + 1)
    (u v : n → R)
    (hu : u ∈ C)
    (hv : v ∈ C) : projection S u = projection S v → u = v := by
  -- We need to show that if π_S(u) = π_S(v), then u = v
  intro proj_agree

  -- Prove by contradiction: assume u ≠ v and derive a contradiction
  by_contra hne

  -- Since u and v are distinct codewords, they differ in at least d = ‖C‖₀ positions
  have hdiff : hammingDist u v ≥ ‖C‖₀ := by {
    simp [codeDist]
    refine Nat.sInf_le ?_
    refine Set.mem_setOf.mpr ?_
    use u
    refine exists_and_left.mp ?_
    use v
  }

  -- Let D be the set of positions where u and v differ
  let D := {i : n | u i ≠ v i}

  -- -- The cardinality of D is the Hamming distance between u and v
  have hD : card D = hammingDist u v := by {
    simp
    exact rfl
  }

  -- -- By our assumption, π_S(u) = π_S(v), so u and v agree on all positions in S
  have hagree : ∀ i ∈ S, u i = v i := by {
    intros i hi
    unfold projection at proj_agree
    let i' : {x // x ∈ S} := ⟨i, hi⟩
    have close: u i' = v i' := by {
      apply congr_fun at proj_agree
      apply proj_agree
    }
    exact close
  }

  -- -- This means D and S are disjoint
  have hdisjoint : D ∩ S = ∅ := by {
    by_contra hinter
    have hinter' : (D ∩ S).Nonempty := by {
      exact Set.nonempty_iff_ne_empty.mpr hinter
    }
    apply Set.inter_nonempty.1 at hinter'
    obtain ⟨x, hx_in_D, hx_in_S⟩ := hinter'
    apply hagree at hx_in_S
    contradiction
  }

  let diff : Set n := {i : n | ¬i ∈ S}
  let hdiff : Fintype diff := by {
    exact ofFinite diff
  }

  -- -- So D must be contained in the complement of S
  have hsub : D ⊆ diff  := by {
    unfold diff
    refine Set.subset_setOf.mpr ?_
    intro x hxd
    solve_by_elim
  }

  -- But |D| ≥ d and |Sᶜ| = n - |S| = n - (n - (d-1)) = d-1
  have hcard_compl : card diff = ‖C‖₀ - 1 := by {
    unfold diff
    simp at *
    rw[hS]
    have stronger :  ‖C‖₀ ≤ card n := by {
      apply codeDist_le_card
    }
    omega
  }

  have hsizes: card D ≤ card diff := by {
    exact Set.card_le_card hsub
  }

  rw[hcard_compl] at hsizes
  rw[hD] at hsizes

  omega



lemma granular (k : ℕ) (hk: k ≤ card n) : exists S : Finset n, (card S) = k := by
  induction k with
  | zero =>
    use ∅
    simp
  | succ k ih =>
    have temp: ∃ S: Finset n, card S = k := by
      apply ih
      omega
    obtain ⟨S, hS⟩ := temp

    have temp2: ∃ x, ¬ x ∈ S := by
      sorry

    obtain ⟨x, hX⟩ := temp2

    let S' := (Set.singleton x) ∪ (Finset.toSet S)
    have temp3: (ofFinite S').card = card S + 1 := by
      unfold S'
      simp
      have dis: Disjoint (Set.singleton x) S := by
        sorry
      let h:= @Finset.card_union_of_disjoint _ (Set.singleton x).toFin S dis
    rw[hS] at temp3
    use (ofFinite S').elems
    simp [hS]

/-- **Singleton bound** for arbitrary codes -/
theorem singleton_bound (C : Set (n → R)) :
    (ofFinite C).card ≤ (ofFinite R).card ^ (card n - ‖C‖₀ + 1) := by

  -- have fin_r : Fintype R := by
  --   exact ofFinite R

  by_cases non_triv : ‖C‖₀ ≥ 1
  · have ax_proj: ∃ (S : Finset n), card S = card n - ‖C‖₀ + 1 := by
      let elems := @Fintype.elems n _
      let sample := elems.val
      sorry

    obtain ⟨S, hS⟩ := ax_proj
    have dec_eq: DecidableEq S := by
      exact Classical.typeDecidableEq { x // x ∈ S }

    let C_proj := {w | ∃ code ∈ C, projection S code = w}
    let C_proj' := Set.image (projection S) C

    -- have extra: Fintype C := by
    --   exact ofFinite ↑C

    -- have extra2: Fintype C_proj := by
    --   exact ofFinite ↑C_proj

    have temp : @card C_proj (ofFinite C_proj) = @card C_proj' (ofFinite C_proj') := by
      exact rfl

    have something1 : @card C_proj (ofFinite C_proj) ≤ @card R (ofFinite R) ^ (card n - ‖C‖₀ + 1) := by
      let huniv := @set_fintype_card_le_univ (S → R) (ofFinite (S → R)) C_proj (ofFinite C_proj)

      have fun_card_1: @card (S → R) ?_ = @card R (ofFinite R) ^ card S := by
        let inst := @card_fun S R ?_ ?_ ?_
        exact inst
        exact dec_eq
      sorry
      -- --swap
      -- -- exact ofFinite ({ x // x ∈ S } → R)
      -- rw[fun_card_1] at huniv
      -- rw[hS] at huniv
      -- exact huniv


    have something2: @card C (ofFinite C) ≤ @card C_proj' (ofFinite C_proj') := by
      -- unfold C_proj'
      -- refine @Fintype.card_le_of_injective ?_ ?_ ?_ ?_ (ofFinite C)  ?_ ?_
      apply @Fintype.card_le_of_injective C C_proj' (ofFinite C) (ofFinite C_proj') ?f
      swap
      exact Set.imageFactorization (projection S) C
      refine Set.imageFactorization_injective_iff.mpr ?_
      intro u hu v hv heq

      apply projection_injective (nontriv := non_triv) (S := S) (u := u) (v := v)
      exact hS
      exact hu
      exact hv
      exact heq

    rw[←temp] at something2
    rw[temp] at something1
    apply le_trans (b := @card C_proj' (ofFinite C_proj'))
    exact something2
    exact something1
  · simp at non_triv
    rw[non_triv]
    simp
    let huniv := @set_fintype_card_le_univ (n → R) (ofFinite (n → R)) C (ofFinite C)
    -- let card_fun := @card_fun n R ?_ ?_ ?_
    sorry
variable [DivisionRing R]

/-- **Singleton bound** for linear codes -/
theorem singleton_bound_linear (C : Submodule R (n → R)) :
    Module.finrank R C ≤ card n - (codeDist C.carrier) + 1 := by sorry
  -- have : (ofFinite C).card = (ofFinite R).card ^ (Module.finrank R C) := by

-- #check card_eq_pow_finrank

-- #check cardinal_mk_eq_cardinal_mk_field_pow_rank
