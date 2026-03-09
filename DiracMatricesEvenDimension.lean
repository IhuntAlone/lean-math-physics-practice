import Mathlib

open Matrix Complex

noncomputable section

abbrev Mat (n : Type*) [Fintype n] [DecidableEq n] :=
  Matrix n n ℂ

structure DiracData (m : ℕ) (n : Type*) [Fintype n] [DecidableEq n] where
  α : Fin m → Mat n
  β : Mat n
  hαsq : ∀ i : Fin m, α i * α i = (1 : Mat n)
  hβsq : β * β = (1 : Mat n)
  hαanti : ∀ i j : Fin m, i ≠ j → α i * α j + α j * α i = (0 : Mat n)
  hαβanti : ∀ i : Fin m, α i * β + β * α i = (0 : Mat n)

structure GammaFamily (m : ℕ) (n : Type*) [Fintype n] [DecidableEq n] where
  γ : Fin m → Mat n
  hsq : ∀ i : Fin m, γ i * γ i = (1 : Mat n)
  hanti : ∀ i j : Fin m, i ≠ j → γ i * γ j + γ j * γ i = (0 : Mat n)
  hHerm : ∀ i : Fin m, IsHermitian (γ i)

theorem trace_zero_of_anticommute
  {n : Type*} [Fintype n] [DecidableEq n]
  (A B : Mat n)
  (hB : B * B = 1)
  (hanti : A * B + B * A = 0) :
  Matrix.trace A = 0 := by
  have hAB : A * B = -(B * A) := by
    apply eq_neg_of_add_eq_zero_left
    simpa [add_comm] using hanti
  have hBAB : B * A * B = -A := by
    calc
      B * A * B = B * (A * B) := by simp [mul_assoc]
      _ = B * (-(B * A)) := by rw [hAB]
      _ = -(B * (B * A)) := by simp
      _ = -((B * B) * A) := by simp [mul_assoc]
      _ = -((1 : Mat n) * A) := by rw [hB]
      _ = -A := by simp
  have htrBAB : Matrix.trace (B * A * B) = Matrix.trace A := by
    calc
      Matrix.trace (B * A * B)
          = Matrix.trace ((B * A) * B) := by simp [mul_assoc]
      _ = Matrix.trace (B * (B * A)) := by
            simpa using Matrix.trace_mul_comm (B * A) B
      _ = Matrix.trace ((B * B) * A) := by simp [mul_assoc]
      _ = Matrix.trace ((1 : Mat n) * A) := by rw [hB]
      _ = Matrix.trace A := by simp
  have htrace_eq_neg : Matrix.trace A = -Matrix.trace A := by
    calc
      Matrix.trace A = Matrix.trace (B * A * B) := by symm; exact htrBAB
      _ = Matrix.trace (-A) := by rw [hBAB]
      _ = -Matrix.trace A := by simp
  have hzero := congrArg (fun z => z + Matrix.trace A) htrace_eq_neg
  simpa using hzero

theorem trace_gamma_zero
    {m : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (D : GammaFamily m n)
    (i j : Fin m)
    (hij : i ≠ j) :
    Matrix.trace (D.γ i) = 0 := by
  apply trace_zero_of_anticommute (A := D.γ i) (B := D.γ j)
  · simpa using D.hsq j
  · simpa [add_comm] using D.hanti i j hij

theorem det_gamma_pmone
    {m : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (D : GammaFamily m n)
    (i : Fin m) :
    Matrix.det (D.γ i) = 1 ∨ Matrix.det (D.γ i) = -1 := by
  have hsq := D.hsq i
  have hdet_sq := congrArg Matrix.det hsq
  simp only [Matrix.det_one, Matrix.det_mul] at hdet_sq
  rw [ mul_self_eq_one_iff ] at hdet_sq
  simpa using hdet_sq

theorem gamma_eigen_sq_one
    {m : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (D : GammaFamily m n)
    (i : Fin m)
    (μ : ℂ)
    (v : n → ℂ)
    (hv0 : v ≠ 0)
    (hv : Matrix.mulVec (D.γ i) v = μ • v) :
    μ^2 = 1 := by
  have hsq := D.hsq i

  have h1 : Matrix.mulVec (D.γ i) (Matrix.mulVec (D.γ i) v) = μ^2 • v := by
    rw [hv, Matrix.mulVec_smul, hv]
    simp [pow_two, smul_smul, mul_assoc]

  have h2 : Matrix.mulVec (D.γ i) (Matrix.mulVec (D.γ i) v) = v := by
    rw [ Matrix.mulVec_mulVec, hsq]
    simp

  have hEq : μ^2 • v = v := by
    rw [h2] at h1
    exact h1.symm

  have hnonzero : ∃ x : n, v x ≠ 0 := by
    by_contra h
    apply hv0
    ext x
    by_contra hx
    exact h ⟨x, hx⟩

  rcases hnonzero with ⟨x, hx⟩

  have hxeq : μ^2 * v x = v x := by
    have h := congrFun hEq x
    simpa using h

  have hxeq' : μ^2 * v x = 1 * v x := by
    simpa using hxeq

  exact mul_right_cancel₀ hx hxeq'

theorem exists_ne_fin
    {m : ℕ} (hm : 2 ≤ m) (i : Fin m) :
    ∃ j : Fin m, j ≠ i := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  rcases exists_ne i with ⟨j, hj⟩
  exact ⟨j, hj⟩

theorem gamma_dim_even
    {m : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (D : GammaFamily m n)
    (hm : 2 ≤ m) :
    Even (Fintype.card n) := by
  let i : Fin m := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hm⟩
  rcases exists_ne_fin hm i with ⟨j, hj⟩

  have hanti' : D.γ i * D.γ j = -(D.γ j * D.γ i) := by
    apply eq_neg_of_add_eq_zero_left
    simpa [add_comm] using D.hanti j i hj

  let a : ℂ := Matrix.det (D.γ i) * Matrix.det (D.γ j)

  have hdet : a = ((-1 : ℂ) ^ Fintype.card n) * a := by
    dsimp [a]
    have hdet0 := congrArg Matrix.det hanti'
    simpa [Matrix.det_mul, Matrix.det_neg, mul_comm, mul_left_comm, mul_assoc] using hdet0

  have hdeti_ne : Matrix.det (D.γ i) ≠ 0 := by
    rcases det_gamma_pmone D i with hi | hi
    · rw [hi]
      norm_num
    · rw [hi]
      norm_num

  have hdetj_ne : Matrix.det (D.γ j) ≠ 0 := by
    rcases det_gamma_pmone D j with hj' | hj'
    · rw [hj']
      norm_num
    · rw [hj']
      norm_num

  have ha_ne : a ≠ 0 := by
    dsimp [a]
    exact mul_ne_zero hdeti_ne hdetj_ne

  have hpow_eq : ((-1 : ℂ) ^ Fintype.card n) = 1 := by
    have hmul : ((-1 : ℂ) ^ Fintype.card n) * a = 1 * a := by
      simpa [one_mul] using hdet.symm
    exact mul_right_cancel₀ ha_ne hmul

  by_contra hEven
  have hOdd : Odd (Fintype.card n) := Nat.not_even_iff_odd.mp hEven
  rcases hOdd with ⟨k, hk⟩
  have hneg : ((-1 : ℂ) ^ Fintype.card n) = -1 := by
    rw [hk, pow_add, pow_mul]
    norm_num
  rw [hneg] at hpow_eq
  norm_num at hpow_eq
