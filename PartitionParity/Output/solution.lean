import Mathlib

open PowerSeries BigOperators

namespace PartitionParity

def pFun (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

noncomputable def P : PowerSeries ℤ := PowerSeries.mk (fun n => (pFun n : ℤ))

noncomputable def qPoch (m : ℕ) : PowerSeries ℤ := ∏ j ∈ Finset.Icc 1 m, (1 - X ^ j)

theorem qPoch_const (m : ℕ) : PowerSeries.constantCoeff (qPoch m) = 1 := by
  unfold qPoch
  rw [map_prod]
  apply Finset.prod_eq_one
  intro j hj
  simp only [Finset.mem_Icc] at hj
  have hj0 : j ≠ 0 := by omega
  have : PowerSeries.constantCoeff (X ^ j : PowerSeries ℤ) = 0 := by
    rw [map_pow, constantCoeff_X, zero_pow hj0]
  simp [map_sub, this]

noncomputable def piSeries (m : ℕ) : PowerSeries ℤ := (qPoch m).invOfUnit 1

theorem piSeries_mul (m : ℕ) : qPoch m * piSeries m = 1 := by
  unfold piSeries
  rw [PowerSeries.mul_invOfUnit]
  simpa using qPoch_const m

noncomputable def qPochPlus (m : ℕ) : PowerSeries ℤ := ∏ j ∈ Finset.Icc 1 m, (1 + X ^ j)

theorem qPochPlus_const (m : ℕ) : PowerSeries.constantCoeff (qPochPlus m) = 1 := by
  unfold qPochPlus
  rw [map_prod]
  apply Finset.prod_eq_one
  intro j hj
  simp only [Finset.mem_Icc] at hj
  have hj0 : j ≠ 0 := by omega
  have : PowerSeries.constantCoeff (X ^ j : PowerSeries ℤ) = 0 := by
    rw [map_pow, constantCoeff_X, zero_pow hj0]
  simp [map_add, this]

noncomputable def piPlusSeries (m : ℕ) : PowerSeries ℤ := (qPochPlus m).invOfUnit 1

theorem piPlusSeries_mul (m : ℕ) : qPochPlus m * piPlusSeries m = 1 := by
  unfold piPlusSeries
  rw [PowerSeries.mul_invOfUnit]
  simpa using qPochPlus_const m

noncomputable def fSeries : PowerSeries ℤ :=
  PowerSeries.mk (fun N =>
    coeff N (1 + ∑ n ∈ Finset.Icc 1 N, X ^ (n ^ 2) * piPlusSeries n ^ 2))

noncomputable def af (n : ℕ) : ℤ := coeff n fSeries

theorem coeff_fSeries_stable (N M : ℕ) (hNM : N ≤ M) :
    coeff N fSeries =
      coeff N (1 + ∑ n ∈ Finset.Icc 1 M, X ^ (n ^ 2) * piPlusSeries n ^ 2) := by
  have hzero : ∀ n : ℕ, N < n →
      coeff N (X ^ (n ^ 2) * piPlusSeries n ^ 2 : PowerSeries ℤ) = 0 := by
    intro n hn
    rw [coeff_X_pow_mul']
    have : ¬ (n ^ 2 ≤ N) := by nlinarith [hn]
    rw [if_neg this]
  rw [fSeries, coeff_mk]
  simp only [map_add]
  congr 1
  rw [map_sum, map_sum]
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right hNM)]
  intro n hnM hnN
  simp only [Finset.mem_Icc] at hnM hnN
  exact hzero n (by omega)

noncomputable def Theta {R : Type*} [CommRing R] (f : PowerSeries R) : PowerSeries R :=
  X * (derivative R f)

theorem coeff_Theta {R : Type*} [CommRing R] (f : PowerSeries R) (n : ℕ) :
    coeff n (Theta f) = n * coeff n f := by
  unfold Theta
  cases n with
  | zero => simp
  | succ m => rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

theorem constantCoeff_Theta {R : Type*} [CommRing R] (f : PowerSeries R) :
    PowerSeries.constantCoeff (Theta f) = 0 := by
  simp [Theta]

def kroneckerAtTwo (a : ℤ) : ℤ :=
  if a % 2 = 0 then 0
  else if a % 8 = 1 ∨ a % 8 = 7 ∨ a % 8 = -1 ∨ a % 8 = -7 then 1 else -1

def kroneckerSym (a : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then (if a = 1 ∨ a = -1 then 1 else 0)
  else (kroneckerAtTwo a) ^ (n.factorization 2) * jacobiSym a (n / 2 ^ (n.factorization 2))

def chi (D : ℕ) (n : ℕ) : ℤ := kroneckerSym (-(D : ℤ)) n

theorem kroneckerAtTwo_odd {a : ℤ} (ha : Odd a) :
    kroneckerAtTwo a = 1 ∨ kroneckerAtTwo a = -1 := by
  unfold kroneckerAtTwo
  have : a % 2 ≠ 0 := by rcases ha with ⟨k, hk⟩; omega
  rw [if_neg this]; split <;> simp

theorem coprime_ordCompl_two (D n : ℕ) (hD : Odd D) :
    Nat.Coprime D (n / 2 ^ (n.factorization 2)) ↔ Nat.Coprime D n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Nat.factorization_zero]
  constructor
  · intro h
    have hsplit : 2 ^ (n.factorization 2) * (n / 2 ^ (n.factorization 2)) = n :=
      Nat.ordProj_mul_ordCompl_eq_self n 2
    have hcop2 : Nat.Coprime D (2 ^ (n.factorization 2)) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hD)
    rw [← hsplit]; exact Nat.Coprime.mul_right hcop2 h
  · intro h
    exact Nat.Coprime.coprime_dvd_right (Nat.ordCompl_dvd n 2) h

theorem chi_trichotomy (D n : ℕ) (hD : Odd D) :
    chi D n = 0 ∨ chi D n = 1 ∨ chi D n = -1 := by
  unfold chi kroneckerSym
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [if_pos rfl]; split
    · right; left; rfl
    · left; rfl
  rw [if_neg hn0]
  have hDodd : Odd (-(D:ℤ)) := by
    rcases hD with ⟨k, hk⟩; exact ⟨-(k+1), by push_cast [hk]; ring⟩
  have hkat := kroneckerAtTwo_odd hDodd
  have hpow : kroneckerAtTwo (-(D:ℤ)) ^ (n.factorization 2) = 1 ∨
      kroneckerAtTwo (-(D:ℤ)) ^ (n.factorization 2) = -1 := by
    rcases hkat with h | h
    · left; rw [h]; simp
    · rw [h]; rcases Nat.even_or_odd (n.factorization 2) with he | ho
      · left; exact he.neg_one_pow
      · right; exact ho.neg_one_pow
  rcases jacobiSym.trichotomy (-(D:ℤ)) (n / 2 ^ (n.factorization 2)) with hj | hj | hj
  · left; rw [hj]; ring
  · rcases hpow with hp | hp <;> rw [hp, hj] <;> simp
  · rcases hpow with hp | hp <;> rw [hp, hj] <;> simp

theorem chi_eq_zero_iff (D n : ℕ) (hD : Odd D) (hn : 0 < n) :
    chi D n = 0 ↔ Nat.gcd D n ≠ 1 := by
  unfold chi kroneckerSym
  rw [if_neg hn.ne']
  set m := n / 2 ^ (n.factorization 2) with hm
  have hDodd : Odd (-(D:ℤ)) := by
    rcases hD with ⟨k, hk⟩; exact ⟨-(k+1), by push_cast [hk]; ring⟩
  have hk2 : kroneckerAtTwo (-(D:ℤ)) ≠ 0 := by
    rcases kroneckerAtTwo_odd hDodd with h | h <;> rw [h] <;> norm_num
  have hkpow : kroneckerAtTwo (-(D:ℤ)) ^ (n.factorization 2) ≠ 0 := pow_ne_zero _ hk2
  have hoc : 0 < m := Nat.ordCompl_pos 2 hn.ne'
  have hne : NeZero m := ⟨hoc.ne'⟩
  have hgcd : Int.gcd (-(D:ℤ)) (↑m) = Nat.gcd D m := by
    simp only [Int.gcd, Int.natAbs_neg, Int.natAbs_natCast]
  have hcopequiv : Nat.gcd D m = 1 ↔ Nat.gcd D n = 1 := coprime_ordCompl_two D n hD
  rw [mul_eq_zero]
  constructor
  · rintro (hpow | hj)
    · exact absurd hpow hkpow
    · rw [jacobiSym.eq_zero_iff_not_coprime, hgcd] at hj
      exact fun hc => hj (hcopequiv.mpr hc)
  · intro hc
    right
    rw [jacobiSym.eq_zero_iff_not_coprime, hgcd]
    exact fun hcop => hc (hcopequiv.mp hcop)

theorem chi_mod2 (D n : ℕ) (hD : Odd D) (hn : 0 < n) :
    (chi D n : ZMod 2) = if Nat.gcd n D = 1 then 1 else 0 := by
  by_cases hc : Nat.gcd n D = 1
  · rw [if_pos hc]
    have hc' : ¬ (Nat.gcd D n ≠ 1) := by rw [Nat.gcd_comm]; simpa using hc
    have hnz : chi D n ≠ 0 := fun h => hc' ((chi_eq_zero_iff D n hD hn).mp h)
    rcases chi_trichotomy D n hD with h | h | h
    · exact absurd h hnz
    · rw [h]; norm_num
    · rw [h]; decide
  · rw [if_neg hc]
    have hc' : Nat.gcd D n ≠ 1 := by rw [Nat.gcd_comm]; exact hc
    have : chi D n = 0 := (chi_eq_zero_iff D n hD hn).mpr hc'
    rw [this]; simp

theorem odd_of_mod24 {D : ℕ} (hD24 : D % 24 = 23) : Odd D := by
  rw [Nat.odd_iff]; omega

noncomputable def redMod (M : ℕ) : PowerSeries ℤ →+* PowerSeries (ZMod M) :=
  PowerSeries.map (Int.castRingHom (ZMod M))

def PSCongr (M : ℕ) (A B : PowerSeries ℤ) : Prop := redMod M A = redMod M B

def sigma1 (n : ℕ) : ℤ := (ArithmeticFunction.sigma 1 n : ℤ)

def Ecoeff (n : ℕ) : ℤ :=
  sigma1 n
    - 4 * (if 2 ∣ n then sigma1 (n / 2) else 0)
    + 3 * (if 3 ∣ n then sigma1 (n / 3) else 0)

noncomputable def E : PowerSeries ℤ := PowerSeries.mk Ecoeff

noncomputable def ED (D : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => ∑ δ ∈ D.divisors, if δ ∣ n then Ecoeff (n / δ) else 0)

noncomputable def singleFactorLog (A : Type*) [CommRing A] (ζ : ℕ → A) (m b : ℕ) :
    PowerSeries A :=
  PowerSeries.mk (fun N => if m ∣ N ∧ N ≠ 0 then -(m : A) * ζ (b * (N / m)) else 0)

theorem coeff_singleFactorLog {A : Type*} [CommRing A] (ζ : ℕ → A) (m b N : ℕ) :
    coeff N (singleFactorLog A ζ m b) =
      if m ∣ N ∧ N ≠ 0 then -(m : A) * ζ (b * (N / m)) else 0 := by
  simp [singleFactorLog, coeff_mk]

noncomputable def psiFactorLog (A : Type*) [CommRing A] (D : ℕ) (C : ℕ → ℕ → ℤ)
    (ζ : ℕ → A) (m : ℕ) : PowerSeries A :=
  (C (m % 12) (D * m ^ 2) : A) •
    ∑ b ∈ Finset.range D, (chi D b : A) • singleFactorLog A ζ m b

theorem coeff_psiFactorLog_zero (A : Type*) [CommRing A] (D : ℕ) (C : ℕ → ℕ → ℤ)
    (ζ : ℕ → A) (m N : ℕ) (h : ¬ (m ∣ N ∧ N ≠ 0)) :
    coeff N (psiFactorLog A D C ζ m) = 0 := by
  simp only [psiFactorLog, map_smul, map_sum]
  rw [Finset.sum_eq_zero, smul_zero]
  intro b hb
  rw [coeff_singleFactorLog, if_neg h, smul_zero]

theorem coeff_psiFactorLog_pos (A : Type*) [CommRing A] (D : ℕ) (C : ℕ → ℕ → ℤ)
    (ζ : ℕ → A) (m N : ℕ) (hdvd : m ∣ N) (hN : N ≠ 0) :
    coeff N (psiFactorLog A D C ζ m) =
      (C (m % 12) (D * m ^ 2) : A) * (-(m : A)) *
        (∑ b ∈ Finset.range D, (chi D b : A) * ζ (b * (N / m))) := by
  simp only [psiFactorLog, map_smul, map_sum, Finset.mul_sum, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [coeff_singleFactorLog, if_pos ⟨hdvd, hN⟩]
  ring

noncomputable def psiLogDeriv (A : Type*) [CommRing A] (D : ℕ) (C : ℕ → ℕ → ℤ)
    (ζ : ℕ → A) : PowerSeries A :=
  PowerSeries.mk (fun N => coeff N (∑ m ∈ Finset.Icc 1 N, psiFactorLog A D C ζ m))

theorem psiLogDeriv_stable (A : Type*) [CommRing A] (D : ℕ) (C : ℕ → ℕ → ℤ)
    (ζ : ℕ → A) (N M : ℕ) (hNM : N ≤ M) :
    coeff N (psiLogDeriv A D C ζ) =
      coeff N (∑ m ∈ Finset.Icc 1 M, psiFactorLog A D C ζ m) := by
  simp only [psiLogDeriv, coeff_mk, map_sum]
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right hNM)]
  intro m hmM hmN
  simp only [Finset.mem_Icc] at hmM hmN
  apply coeff_psiFactorLog_zero
  rintro ⟨hdvd, hN0⟩
  exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdvd) (by omega)

noncomputable def preLogDeriv (A : Type*) [CommRing A] (D : ℕ) (C : ℕ → ℕ → ℤ)
    (ζ : ℕ → A) : PowerSeries A :=
  PowerSeries.mk (fun N =>
    ∑ m ∈ N.divisors,
      (C (m % 12) (D * m ^ 2) : A) * (-(m : A)) *
        (∑ b ∈ Finset.range D, (chi D b : A) * ζ (b * (N / m))))

theorem psiLogDeriv_eq_preLogDeriv (A : Type*) [CommRing A] (D : ℕ) (C : ℕ → ℕ → ℤ)
    (ζ : ℕ → A) : psiLogDeriv A D C ζ = preLogDeriv A D C ζ := by
  ext N
  simp only [psiLogDeriv, preLogDeriv, coeff_mk, map_sum]
  rcases eq_or_ne N 0 with rfl | hN
  · simp only [Nat.divisors_zero, Finset.sum_empty]
    apply Finset.sum_eq_zero
    intro m hm
    apply coeff_psiFactorLog_zero
    rintro ⟨_, h0⟩; exact h0 rfl
  · have hsub : N.divisors ⊆ Finset.Icc 1 N := by
      intro m hm
      rw [Nat.mem_divisors] at hm
      rw [Finset.mem_Icc]
      exact ⟨Nat.pos_of_dvd_of_pos hm.1 (Nat.pos_of_ne_zero hN),
        Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hm.1⟩
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro m hm
      rw [Nat.mem_divisors] at hm
      exact coeff_psiFactorLog_pos A D C ζ m N hm.1 hN
    · intro m hmIcc hmnd
      rw [Finset.mem_Icc] at hmIcc
      apply coeff_psiFactorLog_zero
      rintro ⟨hdvd, _⟩
      exact hmnd (Nat.mem_divisors.mpr ⟨hdvd, hN⟩)

noncomputable def dlogU {L : Type*} [CommRing L] (Θ : Derivation ℤ L L) (x : Lˣ) : L :=
  Θ x * (↑x⁻¹ : L)

theorem dlogU_mul {L : Type*} [CommRing L] (Θ : Derivation ℤ L L) (x y : Lˣ) :
    dlogU Θ (x * y) = dlogU Θ x + dlogU Θ y := by
  unfold dlogU
  have h1 : ((x * y : Lˣ) : L) = (x : L) * (y : L) := rfl
  have h2 : (((x * y)⁻¹ : Lˣ) : L) = (↑x⁻¹ : L) * (↑y⁻¹ : L) := by
    push_cast [mul_inv]; ring
  rw [h1, h2, Θ.leibniz]
  have hx : (x : L) * (↑x⁻¹ : L) = 1 := by rw [← Units.val_mul]; simp
  have hy : (y : L) * (↑y⁻¹ : L) = 1 := by rw [← Units.val_mul]; simp
  simp only [smul_eq_mul]
  linear_combination (Θ (↑y : L) * (↑y⁻¹ : L)) * hx + (Θ (↑x : L) * (↑x⁻¹ : L)) * hy

theorem dlogU_one {L : Type*} [CommRing L] (Θ : Derivation ℤ L L) :
    dlogU Θ (1 : Lˣ) = 0 := by unfold dlogU; simp

theorem dlogU_inv {L : Type*} [CommRing L] (Θ : Derivation ℤ L L) (x : Lˣ) :
    dlogU Θ x⁻¹ = - dlogU Θ x := by
  have h := dlogU_mul Θ x x⁻¹
  rw [mul_inv_cancel, dlogU_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem dlogU_zpow {L : Type*} [CommRing L] (Θ : Derivation ℤ L L) (x : Lˣ) (n : ℤ) :
    dlogU Θ (x ^ n) = n • dlogU Θ x := by
  induction n using Int.induction_on with
  | zero => simp [dlogU_one]
  | succ k ih => rw [zpow_add_one, dlogU_mul, ih]; ring
  | pred k ih => rw [zpow_sub_one, dlogU_mul, dlogU_inv, ih]; ring

theorem isUnit_tau {A : Type*} [CommRing A] (tau : A) (D : ℕ)
    (hGauss : tau ^ 2 = -(D : A)) (hD : IsUnit (D : A)) : IsUnit tau := by
  have h : tau * (-tau) = (D : A) := by ring_nf; linear_combination -hGauss
  exact isUnit_of_mul_isUnit_left (by rw [h]; exact hD)

theorem odd_isUnit_zmod_two_pow (D k : ℕ) (hD : Odd D) : IsUnit ((D : ZMod (2 ^ k))) := by
  rw [ZMod.isUnit_iff_coprime]
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  have := Nat.odd_iff.mp hD
  omega

section Statements

variable {D : ℕ}

variable (C : ℕ → ℕ → ℤ) (FD : PowerSeries ℤ)

theorem coeff_redMod (M : ℕ) (A : PowerSeries ℤ) (N : ℕ) :
    coeff N (redMod M A) = ((coeff N A : ℤ) : ZMod M) := by
  simp [redMod, coeff_map]

theorem pscongr_iff (M : ℕ) (A B : PowerSeries ℤ) :
    PSCongr M A B ↔ ∀ N, ((coeff N A : ℤ) : ZMod M) = ((coeff N B : ℤ) : ZMod M) := by
  unfold PSCongr
  constructor
  · intro h N
    have := congrArg (coeff N) h
    rwa [coeff_redMod, coeff_redMod] at this
  · intro h
    ext N
    rw [coeff_redMod, coeff_redMod]; exact h N

theorem sq_congr_mod4 (A B : PowerSeries ℤ) (h : PSCongr 2 A B) :
    PSCongr 4 (A ^ 2) (B ^ 2) := by
  rw [pscongr_iff] at h ⊢
  have heven : ∀ N, (2 : ℤ) ∣ (coeff N A - coeff N B) := by
    intro N
    have hh := h N
    rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd] at hh
    exact hh
  intro N
  rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hAB : coeff N (A ^ 2) - coeff N (B ^ 2)
      = coeff N ((A - B) * (A + B)) := by
    have : (A - B) * (A + B) = A ^ 2 - B ^ 2 := by ring
    rw [this, map_sub]
  rw [hAB, PowerSeries.coeff_mul]
  apply Finset.dvd_sum
  intro p hp
  have h1 : (2 : ℤ) ∣ coeff p.1 (A - B) := by
    rw [map_sub]; exact heven p.1
  have h2 : (2 : ℤ) ∣ coeff p.2 (A + B) := by
    have : coeff p.2 (A + B) = coeff p.2 (A - B) + 2 * coeff p.2 B := by
      rw [map_add, map_sub]; ring
    rw [this]
    exact Dvd.dvd.add (heven p.2) ⟨coeff p.2 B, rfl⟩
  have hmul := mul_dvd_mul h1 h2
  have : (2 : ℤ) * 2 = ((4 : ℕ) : ℤ) := by norm_num
  rwa [this] at hmul

theorem qPoch_congr_qPochPlus_mod2 (m : ℕ) : PSCongr 2 (qPoch m) (qPochPlus m) := by
  unfold PSCongr redMod qPoch qPochPlus
  rw [map_prod, map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  ext N
  rw [coeff_map, coeff_map, map_sub, map_add]
  simp only [map_one, map_pow, PowerSeries.coeff_one]
  by_cases hN : N = 0
  · subst hN
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
    simp [map_pow, constantCoeff_X]
    rcases eq_or_ne j 0 with rfl | hj0
    · simp; decide
    · simp [zero_pow hj0]
  · simp only [if_neg hN]
    have hXj : PowerSeries.coeff N (X ^ j : PowerSeries ℤ)
        = if N = j then 1 else 0 := by
      rw [PowerSeries.coeff_X_pow]
    rw [hXj]
    split <;> simp <;> decide

theorem piSeries_congr_piPlus_mod2 (m : ℕ) : PSCongr 2 (piSeries m) (piPlusSeries m) := by
  unfold PSCongr
  have h1 : redMod 2 (qPoch m) * redMod 2 (piSeries m) = 1 := by
    rw [← map_mul, piSeries_mul]; simp [redMod]
  have h2 : redMod 2 (qPochPlus m) * redMod 2 (piPlusSeries m) = 1 := by
    rw [← map_mul, piPlusSeries_mul]; simp [redMod]
  have hbase : redMod 2 (qPoch m) = redMod 2 (qPochPlus m) := qPoch_congr_qPochPlus_mod2 m
  rw [hbase] at h1
  have := left_inv_eq_right_inv (a := redMod 2 (qPochPlus m))
    (b := redMod 2 (piSeries m)) (c := redMod 2 (piPlusSeries m))
    (by rw [mul_comm]; exact h1) h2
  exact this

theorem statement1_mod4
    (hDurfee : ∀ N : ℕ,
      coeff N P =
        coeff N (1 + ∑ m ∈ Finset.Icc 1 N, X ^ (m ^ 2) * piSeries m ^ 2)) :
    PSCongr 4 P fSeries := by
  rw [pscongr_iff]
  intro N
  rw [hDurfee N]
  have hf : coeff N fSeries
      = coeff N (1 + ∑ n ∈ Finset.Icc 1 N, X ^ (n ^ 2) * piPlusSeries n ^ 2) := by
    rw [fSeries, coeff_mk]
  rw [hf]
  have hcong : PSCongr 4
      (1 + ∑ m ∈ Finset.Icc 1 N, X ^ (m ^ 2) * piSeries m ^ 2)
      (1 + ∑ n ∈ Finset.Icc 1 N, X ^ (n ^ 2) * piPlusSeries n ^ 2) := by
    unfold PSCongr
    rw [map_add, map_add, map_sum, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    rw [map_mul, map_mul]
    congr 1
    have hsq := sq_congr_mod4 (piSeries m) (piPlusSeries m) (piSeries_congr_piPlus_mod2 m)
    unfold PSCongr redMod at hsq
    exact hsq
  rw [pscongr_iff] at hcong
  exact hcong N

theorem statement1_mod2_consequence
    (hDurfee : ∀ N : ℕ,
      coeff N P =
        coeff N (1 + ∑ m ∈ Finset.Icc 1 N, X ^ (m ^ 2) * piSeries m ^ 2)) :
    ∀ n : ℕ, (af n : ZMod 2) = (pFun n : ZMod 2) := by
  intro n
  have h4 := statement1_mod4 hDurfee
  rw [pscongr_iff] at h4
  have hn := h4 n
  have hP : coeff n P = (pFun n : ℤ) := by rw [P, coeff_mk]
  have hf : coeff n fSeries = af n := rfl
  rw [hP, hf] at hn
  have hdvd : (2 : ℕ) ∣ 4 := by norm_num
  have := congrArg (ZMod.castHom hdvd (ZMod 2)) hn
  simpa using this.symm

noncomputable def FDexpansion (D : ℕ) (C : ℕ → ℕ → ℤ) : PowerSeries ℤ :=
  PowerSeries.mk (fun N =>
    ∑ m ∈ N.divisors, (m : ℤ) * C (m % 12) (D * m ^ 2) * chi D (N / m))

noncomputable def FDexpansionOver (A : Type*) [CommRing A] (D : ℕ) (C : ℕ → ℕ → ℤ) :
    PowerSeries A :=
  PowerSeries.mk (fun N =>
    ∑ m ∈ N.divisors, (m : A) * (C (m % 12) (D * m ^ 2) : A) * (chi D (N / m) : A))

theorem statement2_collapse
    {A : Type*} [CommRing A] (tau : A) (ζ : ℕ → A)
    (hGauss : tau ^ 2 = -(D : A))
    (hGaussSum : ∀ k : ℕ,
      (∑ b ∈ Finset.range D, (chi D b : A) * ζ (b * k)) = -(chi D k : A) * tau) :
    preLogDeriv A D C ζ = tau • FDexpansionOver A D C := by
  ext N
  simp only [preLogDeriv, FDexpansionOver, coeff_mk, map_smul, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.mul_sum, hGaussSum (N / m)]
  ring

theorem statement2_logderiv
    {A : Type*} [CommRing A] (tau : A) (ζ : ℕ → A)
    (hD1 : 1 < D) (hDsf : Squarefree D) (hD24 : D % 24 = 23)
    (hGauss : tau ^ 2 = -(D : A))
    (hGaussSum : ∀ k : ℕ,
      (∑ b ∈ Finset.range D, (chi D b : A) * ζ (b * k)) = -(chi D k : A) * tau)
    (hτ : ∀ x y : A, tau * x = tau * y → x = y)
    (hEmbed : Function.Injective (PowerSeries.map (Int.castRingHom A)))
    (hNorm :
      tau • (PowerSeries.map (Int.castRingHom A) FD) = psiLogDeriv A D C ζ) :
    FD = FDexpansion D C := by
  have hmapeq : PowerSeries.map (Int.castRingHom A) (FDexpansion D C)
      = FDexpansionOver A D C := by
    ext N
    simp only [FDexpansion, FDexpansionOver, coeff_map, coeff_mk, Int.coe_castRingHom]
    push_cast
    rfl
  have hkey : tau • PowerSeries.map (Int.castRingHom A) FD
      = tau • PowerSeries.map (Int.castRingHom A) (FDexpansion D C) := by
    rw [hNorm, psiLogDeriv_eq_preLogDeriv,
      statement2_collapse C tau ζ hGauss hGaussSum, hmapeq]
  have hcancel : PowerSeries.map (Int.castRingHom A) FD
      = PowerSeries.map (Int.castRingHom A) (FDexpansion D C) := by
    ext N
    have := congrArg (coeff N) hkey
    simp only [map_smul, smul_eq_mul] at this
    exact hτ _ _ this
  exact hEmbed hcancel

noncomputable def lambertF (D : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun N =>
    ∑ m ∈ N.divisors,
      if Nat.gcd m 6 = 1 ∧ Nat.gcd (N / m) D = 1 then (pFun ((D * m ^ 2 + 1) / 24) : ℤ)
      else 0)

theorem statement3_lambert
    (hD1 : 1 < D) (hDsf : Squarefree D) (hD24 : D % 24 = 23)
    (hFD : FD = FDexpansion D C)
    (hC : ∀ m : ℕ, Nat.gcd m 6 = 1 →
      C (m % 12) (D * m ^ 2) =
        (if m % 12 = 1 ∨ m % 12 = 7 then (1 : ℤ) else -1) *
          af ((D * m ^ 2 + 1) / 24))
    (hC3 : ∀ m : ℕ, 3 ∣ m → C (m % 12) (D * m ^ 2) = 0)
    (hAfP : ∀ k : ℕ, (af k : ZMod 2) = (pFun k : ZMod 2)) :
    PSCongr 2 FD (lambertF D) := by
  have hDodd : Odd D := odd_of_mod24 hD24
  have hg6equiv : ∀ m : ℕ, Nat.gcd m 6 = 1 ↔ (¬ 2 ∣ m ∧ ¬ 3 ∣ m) := by
    intro m
    constructor
    · intro hg
      refine ⟨?_, ?_⟩
      · intro h2
        have : (2 : ℕ) ∣ Nat.gcd m 6 := Nat.dvd_gcd h2 (by norm_num)
        rw [hg] at this; omega
      · intro h3
        have : (3 : ℕ) ∣ Nat.gcd m 6 := Nat.dvd_gcd h3 (by norm_num)
        rw [hg] at this; omega
    · rintro ⟨h2, h3⟩
      have hc2 : Nat.Coprime m 2 :=
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2).symm
      have hc3 : Nat.Coprime m 3 :=
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
      show Nat.Coprime m 6
      rw [show (6 : ℕ) = 2 * 3 from rfl]
      exact Nat.Coprime.mul_right hc2 hc3
  rw [hFD, pscongr_iff]
  intro N
  simp only [FDexpansion, lambertF, coeff_mk]
  rw [Int.cast_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Nat.mem_divisors] at hm
  obtain ⟨hmdvd, hN0⟩ := hm
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | hp
    · subst h0; simp at hmdvd; exact absurd hmdvd hN0
    · exact hp
  have hpos : 0 < N / m :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hmdvd) hmpos
  have hchi := chi_mod2 D (N / m) hDodd hpos
  by_cases h3 : 3 ∣ m
  · have hC0 := hC3 m h3
    rw [hC0]
    rw [if_neg (show ¬ (Nat.gcd m 6 = 1 ∧ Nat.gcd (N / m) D = 1) by
      rw [hg6equiv]; tauto)]
    push_cast; ring
  · by_cases h2 : 2 ∣ m
    · rw [if_neg (show ¬ (Nat.gcd m 6 = 1 ∧ Nat.gcd (N / m) D = 1) by
        rw [hg6equiv]; tauto)]
      have hmeven : ((m : ℤ) : ZMod 2) = 0 := by
        obtain ⟨k, hk⟩ := h2
        subst hk
        push_cast
        rw [show ((2 : ZMod 2) * (k : ZMod 2)) = 0 by
          rw [show (2 : ZMod 2) = 0 by decide]; ring]
      push_cast at hmeven ⊢
      rw [hmeven]
      simp
    · have hg6 : Nat.gcd m 6 = 1 := (hg6equiv m).mpr ⟨h2, h3⟩
      rw [hC m hg6]
      have hmodd : ((m : ℤ) : ZMod 2) = 1 := by
        rcases Nat.odd_iff.mpr (by omega : m % 2 = 1) with ⟨k, hk⟩
        subst hk
        push_cast
        rw [show (2 : ZMod 2) = 0 by decide]; ring
      have hsign : ((if m % 12 = 1 ∨ m % 12 = 7 then (1 : ℤ) else -1 : ℤ) : ZMod 2) = 1 := by
        split <;> decide
      have hAf := hAfP ((D * m ^ 2 + 1) / 24)
      push_cast
      push_cast at hmodd hsign
      rw [hmodd, hchi, hsign, hAf]
      by_cases hcop : Nat.gcd (N / m) D = 1
      · rw [if_pos hcop, if_pos ⟨hg6, hcop⟩]
        ring
      · rw [if_neg hcop, if_neg (show ¬ (Nat.gcd m 6 = 1 ∧ Nat.gcd (N / m) D = 1) from
          fun h => hcop h.2)]
        ring

theorem statement4_residue
    {L : Type*} [CommRing L] {A : Type*} [CommRing A]
    (Θ : Derivation ℤ L L) (res : L →ₗ[ℤ] A)
    (t Ψ u : Lˣ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hFact : Ψ = t ^ ε * u)
    (hres_t : res (dlogU Θ t) = 1)
    (hres_u : res (dlogU Θ u) = 0)
    (tau : A) (hGauss : tau ^ 2 = -(D : A)) (hDunit : IsUnit (D : A)) :
    dlogU Θ Ψ = ε • dlogU Θ t + dlogU Θ u
      ∧ res (dlogU Θ Ψ) = (ε : A)
      ∧ ∃ hτ : IsUnit tau,
          res (dlogU Θ Ψ) * (↑hτ.unit⁻¹ : A) = (ε : A) * (↑hτ.unit⁻¹ : A)
            ∧ IsUnit (res (dlogU Θ Ψ) * (↑hτ.unit⁻¹ : A)) := by
  have hdecomp : dlogU Θ Ψ = ε • dlogU Θ t + dlogU Θ u := by
    rw [hFact, dlogU_mul, dlogU_zpow]
  have hres : res (dlogU Θ Ψ) = (ε : A) := by
    rw [hdecomp, map_add, map_zsmul, hres_t, hres_u]; simp
  refine ⟨hdecomp, hres, ?_⟩
  have hτ : IsUnit tau := isUnit_tau tau D hGauss hDunit
  refine ⟨hτ, by rw [hres], ?_⟩
  rw [hres]
  apply IsUnit.mul
  · rcases hε with h | h <;> subst h <;> simp
  · exact Units.isUnit _

theorem statement5_coeff (n : ℕ) :
    coeff n E = sigma1 n
      - 4 * (if 2 ∣ n then sigma1 (n / 2) else 0)
      + 3 * (if 3 ∣ n then sigma1 (n / 3) else 0) := by
  simp [E, Ecoeff, coeff_mk]

theorem sigma1_odd_mod2 (u : ℕ) (hu : Odd u) :
    ((ArithmeticFunction.sigma 1 u : ℕ) : ZMod 2)
      = ((ArithmeticFunction.sigma 0 u : ℕ) : ZMod 2) := by
  rw [ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
  push_cast
  apply Finset.sum_congr rfl
  intro d hd
  have hdodd : Odd d := hu.of_dvd_nat (Nat.dvd_of_mem_divisors hd)
  obtain ⟨k, hk⟩ := hdodd
  subst hk
  rw [pow_one, pow_zero]
  push_cast
  rw [show ((2 : ZMod 2)) = 0 by decide]
  ring

theorem sigma1_two_pow_odd (a : ℕ) :
    ((ArithmeticFunction.sigma 1 (2 ^ a) : ℕ) : ZMod 2) = 1 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
  push_cast
  rw [Finset.sum_range_succ']
  simp
  induction a with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    rw [show ((2:ZMod 2)) = 0 by decide]
    simp

theorem sigma1_three_pow_mod2 (b : ℕ) :
    ((ArithmeticFunction.sigma 1 (3 ^ b) : ℕ) : ZMod 2) = ((b + 1 : ℕ) : ZMod 2) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
  push_cast
  rw [show ((3:ZMod 2)) = 1 by decide]
  simp

theorem sigma1_key_mod2 (m : ℕ) (hm : 0 < m) :
    ((ArithmeticFunction.sigma 1 m : ℕ) : ZMod 2)
      = (((m.factorization 3 + 1 : ℕ) : ZMod 2)
          * ((ArithmeticFunction.sigma 0
              (m / 2 ^ (m.factorization 2) / 3 ^ (m.factorization 3)) : ℕ) : ZMod 2)) := by
  set a := m.factorization 2 with ha
  set b := m.factorization 3 with hb
  set w := m / 2 ^ a with hw
  have hmne : m ≠ 0 := hm.ne'
  have hwne : w ≠ 0 := by
    rw [hw]; exact Nat.ordCompl_pos 2 hmne |>.ne'
  have hmw : m = 2 ^ a * w := by
    rw [hw, ha]; exact (Nat.ordProj_mul_ordCompl_eq_self m 2).symm
  have hwfac3 : w.factorization 3 = b := by
    rw [hw, ha, Nat.factorization_ordCompl, Finsupp.erase_ne (by decide : (3:ℕ) ≠ 2), hb]
  have hcop2 : Nat.Coprime (2 ^ a) w := by
    rw [hw, ha]
    exact (Nat.coprime_ordCompl (by norm_num) hmne).pow_left a
  set u := w / 3 ^ b with hu
  have hune : u ≠ 0 := by
    rw [hu, ← hwfac3]; exact (Nat.ordCompl_pos 3 hwne).ne'
  have hwu : w = 3 ^ b * u := by
    rw [hu, ← hwfac3]; exact (Nat.ordProj_mul_ordCompl_eq_self w 3).symm
  have hcop3 : Nat.Coprime (3 ^ b) u := by
    have hc : Nat.Coprime 3 u := by
      rw [hu, ← hwfac3]
      exact Nat.coprime_ordCompl (by norm_num) hwne
    exact hc.pow_left b
  have hmult := ArithmeticFunction.isMultiplicative_sigma (k := 1)
  have hstep1 : ArithmeticFunction.sigma 1 m
      = ArithmeticFunction.sigma 1 (2 ^ a) * ArithmeticFunction.sigma 1 w := by
    rw [hmw]; exact hmult.map_mul_of_coprime hcop2
  have hstep2 : ArithmeticFunction.sigma 1 w
      = ArithmeticFunction.sigma 1 (3 ^ b) * ArithmeticFunction.sigma 1 u := by
    rw [hwu]; exact hmult.map_mul_of_coprime hcop3
  rw [hstep1, hstep2]
  push_cast
  rw [sigma1_two_pow_odd a, sigma1_three_pow_mod2 b]
  have huodd : Odd u := by
    rw [Nat.odd_iff]
    have : ¬ (2 ∣ u) := by
      intro hdvd
      have : (2:ℕ) ∣ w := hwu ▸ (Dvd.dvd.mul_left hdvd (3^b))
      have h2w : (2:ℕ).Coprime w := (Nat.coprime_ordCompl (by norm_num) hmne)
      have hd1 : (2:ℕ) ∣ 1 := by
        have := Nat.dvd_gcd (dvd_refl 2) this
        rwa [h2w] at this
      omega
    omega
  have := sigma1_odd_mod2 u huodd
  push_cast at this ⊢
  rw [this]
  ring

theorem statement5_coeff_mod2 (n : ℕ) (hn : 0 < n) :
    (Ecoeff n : ZMod 2) =
      ((ArithmeticFunction.sigma 0
          (n / 2 ^ (n.factorization 2) / 3 ^ (n.factorization 3)) : ℕ) : ZMod 2) := by
  set u := n / 2 ^ (n.factorization 2) / 3 ^ (n.factorization 3) with hu
  have hEc : (Ecoeff n : ZMod 2)
      = ((ArithmeticFunction.sigma 1 n : ℕ) : ZMod 2)
        + (if 3 ∣ n then ((ArithmeticFunction.sigma 1 (n / 3) : ℕ) : ZMod 2) else 0) := by
    simp only [Ecoeff, sigma1]
    push_cast
    rw [show ((4 : ZMod 2)) = 0 by decide, show ((3 : ZMod 2)) = 1 by decide]
    split_ifs with h3 <;> ring
  rw [hEc]
  have hkeyn := sigma1_key_mod2 n hn
  rw [← hu] at hkeyn
  rw [hkeyn]
  by_cases h3 : 3 ∣ n
  · simp only [h3, if_true]
    have hn3 : 0 < n / 3 := Nat.div_pos (Nat.le_of_dvd hn h3) (by norm_num)
    have hkey3 := sigma1_key_mod2 (n / 3) hn3
    have hfac3 : (n / 3).factorization 3 = n.factorization 3 - 1 := by
      rw [Nat.factorization_div h3]
      simp [Nat.Prime.factorization_self (by norm_num : Nat.Prime 3)]
    have hpart : (n / 3) / 2 ^ ((n / 3).factorization 2) / 3 ^ ((n / 3).factorization 3) = u := by
      have hfac2 : (n / 3).factorization 2 = n.factorization 2 := by
        rw [Nat.factorization_div h3]
        simp [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (2:ℕ) ∣ 3)]
      rw [hfac2, hfac3, hu]
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
      congr 1
      have hb1 : 1 ≤ n.factorization 3 := by
        rw [← Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 3) hn.ne']
        simpa using h3
      have h33 : (3 : ℕ) * 3 ^ (n.factorization 3 - 1) = 3 ^ (n.factorization 3) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [show (3 : ℕ) * (2 ^ n.factorization 2 * 3 ^ (n.factorization 3 - 1))
            = 2 ^ n.factorization 2 * (3 * 3 ^ (n.factorization 3 - 1)) by ring, h33]
    rw [hpart] at hkey3
    rw [hkey3, hfac3]
    have hb1 : 1 ≤ n.factorization 3 := by
      rw [← Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 3) hn.ne']
      simpa using h3
    have hbb : n.factorization 3 - 1 + 1 = n.factorization 3 := Nat.sub_add_cancel hb1
    rw [hbb]
    push_cast
    ring_nf
    rw [show ((2 : ZMod 2)) = 0 by decide]
    ring
  · simp only [h3, if_false, add_zero]
    have hb0 : n.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd h3
    rw [hb0]
    push_cast
    ring

noncomputable def eisF : PowerSeries ℤ :=
  PowerSeries.mk (fun N => ∑ m ∈ N.divisors, if Nat.gcd m 6 = 1 then (1 : ℤ) else 0)

theorem statement5_mod2 : PSCongr 2 E eisF := by
  rw [pscongr_iff]
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [E, eisF, coeff_mk, Ecoeff, sigma1]
  have hg6equiv : ∀ m : ℕ, Nat.gcd m 6 = 1 ↔ (¬ 2 ∣ m ∧ ¬ 3 ∣ m) := by
    intro m
    constructor
    · intro hg
      refine ⟨?_, ?_⟩
      · intro h2
        have : (2 : ℕ) ∣ Nat.gcd m 6 := Nat.dvd_gcd h2 (by norm_num)
        rw [hg] at this; omega
      · intro h3
        have : (3 : ℕ) ∣ Nat.gcd m 6 := Nat.dvd_gcd h3 (by norm_num)
        rw [hg] at this; omega
    · rintro ⟨h2, h3⟩
      have hc2 : Nat.Coprime m 2 :=
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2).symm
      have hc3 : Nat.Coprime m 3 :=
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
      show Nat.Coprime m 6
      rw [show (6 : ℕ) = 2 * 3 from rfl]
      exact Nat.Coprime.mul_right hc2 hc3
  set a := N.factorization 2 with ha
  set b := N.factorization 3 with hb
  set u := N / 2 ^ a / 3 ^ b with hu
  have hNne : N ≠ 0 := hN.ne'
  set w := N / 2 ^ a with hwdef
  have hwne : w ≠ 0 := by rw [hwdef]; exact (Nat.ordCompl_pos 2 hNne).ne'
  have hwfac3 : w.factorization 3 = b := by
    rw [hwdef, ha, Nat.factorization_ordCompl,
      Finsupp.erase_ne (by decide : (3:ℕ) ≠ 2), hb]
  have hune : u ≠ 0 := by
    rw [hu, ← hwfac3]; exact (Nat.ordCompl_pos 3 hwne).ne'
  have huw : u ∣ w := by rw [hu, ← hwfac3]; exact Nat.ordCompl_dvd w 3
  have hwN : w ∣ N := by rw [hwdef]; exact Nat.ordCompl_dvd N 2
  have huN : u ∣ N := huw.trans hwN
  have hu_no2 : ¬ (2 ∣ u) := by
    intro h2
    have hdw : (2:ℕ) ∣ w := h2.trans huw
    have hcop : (2:ℕ).Coprime w := Nat.coprime_ordCompl (by norm_num) hNne
    have : (2:ℕ) ∣ 1 := by
      have := Nat.dvd_gcd (dvd_refl 2) hdw; rwa [hcop] at this
    omega
  have hu_no3 : ¬ (3 ∣ u) := by
    have hcop : (3:ℕ).Coprime u := by
      rw [hu, ← hwfac3]
      exact Nat.coprime_ordCompl (by norm_num) hwne
    intro h3
    have : (3:ℕ) ∣ 1 := by
      have := Nat.dvd_gcd (dvd_refl 3) h3; rwa [hcop] at this
    omega
  have hwu : w = 3 ^ b * u := by
    rw [hu, ← hwfac3]
    exact (Nat.ordProj_mul_ordCompl_eq_self w 3).symm
  have hNfac : N = 2 ^ a * (3 ^ b * u) := by
    rw [← hwu, hwdef, ha]; exact (Nat.ordProj_mul_ordCompl_eq_self N 2).symm
  have hfilter : N.divisors.filter (fun m => Nat.gcd m 6 = 1) = u.divisors := by
    ext m
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hmN, _⟩, hg⟩
      rw [hg6equiv] at hg
      obtain ⟨hm2, hm3⟩ := hg
      refine ⟨?_, hune⟩
      have hcm2 : Nat.Coprime m (2 ^ a) := by
        apply Nat.Coprime.pow_right
        rw [Nat.coprime_comm]
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm2
      have hcm3 : Nat.Coprime m (3 ^ b) := by
        apply Nat.Coprime.pow_right
        rw [Nat.coprime_comm]
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3
      rw [hNfac] at hmN
      have hstep1 : m ∣ 3 ^ b * u := Nat.Coprime.dvd_of_dvd_mul_left hcm2 hmN
      exact Nat.Coprime.dvd_of_dvd_mul_left hcm3 hstep1
    · rintro ⟨hmu, _⟩
      refine ⟨⟨hmu.trans huN, hNne⟩, ?_⟩
      rw [hg6equiv]
      exact ⟨fun h => hu_no2 (h.trans hmu), fun h => hu_no3 (h.trans hmu)⟩
  have hLHS : ((coeff N E : ℤ) : ZMod 2) = ((ArithmeticFunction.sigma 0 u : ℕ) : ZMod 2) := by
    rw [show coeff N E = Ecoeff N by simp [E, coeff_mk]]
    have := statement5_coeff_mod2 N hN
    rw [← hu] at this
    exact this
  rw [hLHS]
  have hRHS : ((coeff N eisF : ℤ) : ZMod 2) =
      ((N.divisors.filter (fun m => Nat.gcd m 6 = 1)).card : ZMod 2) := by
    rw [show coeff N eisF = ∑ m ∈ N.divisors, if Nat.gcd m 6 = 1 then (1 : ℤ) else 0 by
      simp [eisF, coeff_mk]]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
    simp
  rw [hRHS, hfilter, ArithmeticFunction.sigma_zero_apply]

noncomputable def eisFD (D : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun N =>
    ∑ m ∈ N.divisors, if Nat.gcd m 6 = 1 ∧ Nat.gcd (N / m) D = 1 then (1 : ℤ) else 0)

theorem card_divisors_squarefree {s : ℕ} (hs0 : s ≠ 0) (hsf : Squarefree s) :
    s.divisors.card = 2 ^ s.primeFactors.card := by
  rw [Nat.card_divisors hs0, ← Finset.prod_const]
  apply Finset.prod_congr rfl
  intro p hp
  have hp1 : 1 ≤ s.factorization p := by
    rw [Nat.one_le_iff_ne_zero, ← Finsupp.mem_support_iff, Nat.support_factorization]
    exact hp
  have hple : s.factorization p ≤ 1 :=
    (Nat.squarefree_iff_factorization_le_one hs0).mp hsf p
  omega

theorem card_divisors_squarefree_mod2 {s : ℕ} (hs0 : s ≠ 0) (hsf : Squarefree s) :
    (s.divisors.card : ZMod 2) = if s = 1 then 1 else 0 := by
  rw [card_divisors_squarefree hs0 hsf]
  by_cases h1 : s = 1
  · subst h1; simp
  · rw [if_neg h1]
    have hne : s.primeFactors.Nonempty := by
      rw [Nat.nonempty_primeFactors]; omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
      (Finset.card_ne_zero_of_mem hne.choose_spec)
    rw [hk]
    push_cast
    rw [pow_succ, show ((2 : ZMod 2)) = 0 by decide]
    ring

theorem statement6_twist (hD1 : 1 < D) (hDsf : Squarefree D) :
    PSCongr 2 (ED D) (eisFD D) := by
  have hDne : D ≠ 0 := by omega
  have h5 : ∀ k : ℕ, (Ecoeff k : ZMod 2)
      = ((k.divisors.filter (fun m => Nat.gcd m 6 = 1)).card : ZMod 2) := by
    intro k
    have hstmt := (pscongr_iff 2 E eisF).mp statement5_mod2 k
    rw [show coeff k E = Ecoeff k by simp [E, coeff_mk],
        show coeff k eisF = ∑ m ∈ k.divisors, if Nat.gcd m 6 = 1 then (1 : ℤ) else 0 by
          simp [eisF, coeff_mk]] at hstmt
    rw [hstmt]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
    push_cast
    simp
  rw [pscongr_iff]
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [ED, eisFD, coeff_mk, Ecoeff, sigma1]
  have hNne : N ≠ 0 := hN.ne'
  rw [show coeff N (ED D) = ∑ δ ∈ D.divisors, if δ ∣ N then Ecoeff (N / δ) else 0 by
        simp [ED, coeff_mk],
      show coeff N (eisFD D)
          = ∑ m ∈ N.divisors,
              if Nat.gcd m 6 = 1 ∧ Nat.gcd (N / m) D = 1 then (1 : ℤ) else 0 by
        simp [eisFD, coeff_mk]]
  push_cast
  have hLHS : (∑ δ ∈ D.divisors,
        (if δ ∣ N then (Ecoeff (N / δ) : ZMod 2) else 0))
      = ∑ δ ∈ D.divisors.filter (fun δ => δ ∣ N),
          (((N / δ).divisors.filter (fun m => Nat.gcd m 6 = 1)).card : ZMod 2) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro δ hδ
    split_ifs with hd
    · rw [h5]
    · rfl
  have hRHS : (∑ m ∈ N.divisors,
        (if Nat.gcd m 6 = 1 ∧ Nat.gcd (N / m) D = 1 then (1 : ZMod 2) else 0))
      = ∑ m ∈ N.divisors.filter (fun m => Nat.gcd m 6 = 1),
          (((Nat.gcd D (N / m)).divisors).card : ZMod 2) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    have hgsf : Squarefree (Nat.gcd D (N / m)) :=
      hDsf.squarefree_of_dvd (Nat.gcd_dvd_left D (N / m))
    have hgne : Nat.gcd D (N / m) ≠ 0 := by
      simp only [ne_eq, Nat.gcd_eq_zero_iff, not_and]
      intro h; exact absurd h hDne
    rw [card_divisors_squarefree_mod2 hgne hgsf]
    by_cases hg6 : Nat.gcd m 6 = 1
    · simp only [hg6, true_and, if_true, Nat.gcd_comm D (N / m)]
    · simp [hg6]
  rw [hLHS, hRHS]
  have hLcard : (∑ δ ∈ D.divisors.filter (fun δ => δ ∣ N),
        (((N / δ).divisors.filter (fun m => Nat.gcd m 6 = 1)).card : ZMod 2))
      = (((D.divisors.filter (fun δ => δ ∣ N)).sigma
            (fun δ => (N / δ).divisors.filter (fun m => Nat.gcd m 6 = 1))).card : ZMod 2) := by
    rw [Finset.card_sigma]
    push_cast
    rfl
  have hRcard : (∑ m ∈ N.divisors.filter (fun m => Nat.gcd m 6 = 1),
        (((Nat.gcd D (N / m)).divisors).card : ZMod 2))
      = (((N.divisors.filter (fun m => Nat.gcd m 6 = 1)).sigma
            (fun m => (Nat.gcd D (N / m)).divisors)).card : ZMod 2) := by
    rw [Finset.card_sigma]
    push_cast
    rfl
  rw [hLcard, hRcard]
  congr 1
  apply Finset.card_nbij' (fun p => ⟨p.2, p.1⟩) (fun p => ⟨p.2, p.1⟩)
  · rintro ⟨δ, m⟩ hp
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors] at hp ⊢
    obtain ⟨⟨⟨hδD, _⟩, hδN⟩, ⟨hmdvd, _⟩, hm6⟩ := hp
    have hmN : m ∣ N := hmdvd.trans (Nat.div_dvd_of_dvd hδN)
    refine ⟨⟨⟨hmN, hNne⟩, hm6⟩, ?_, ?_⟩
    · apply Nat.dvd_gcd hδD
      rw [Nat.dvd_div_iff_mul_dvd hmN]
      rw [Nat.dvd_div_iff_mul_dvd hδN] at hmdvd
      rw [mul_comm]; exact hmdvd
    · simp only [ne_eq, Nat.gcd_eq_zero_iff, not_and]
      intro h; exact absurd h hDne
  · rintro ⟨m, δ⟩ hp
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors] at hp ⊢
    obtain ⟨⟨⟨hmN, _⟩, hm6⟩, hδg, _⟩ := hp
    have hδD : δ ∣ D := hδg.trans (Nat.gcd_dvd_left D (N / m))
    have hδNm : δ ∣ N / m := hδg.trans (Nat.gcd_dvd_right D (N / m))
    have hδN : δ ∣ N := hδNm.trans (Nat.div_dvd_of_dvd hmN)
    refine ⟨⟨⟨hδD, hDne⟩, hδN⟩, ⟨?_, ?_⟩, hm6⟩
    · rw [Nat.dvd_div_iff_mul_dvd hδN]
      rw [Nat.dvd_div_iff_mul_dvd hmN] at hδNm
      rw [mul_comm]; exact hδNm
    · have : 0 < N / δ :=
        Nat.div_pos (Nat.le_of_dvd hN hδN) (Nat.pos_of_dvd_of_pos hδD (by omega))
      omega
  · rintro ⟨δ, m⟩ _; rfl
  · rintro ⟨m, δ⟩ _; rfl

theorem statement7_FeqE
    (hD1 : 1 < D) (hDsf : Squarefree D) (hD24 : D % 24 = 23)
    (hFD : FD = FDexpansion D C)
    (hC : ∀ m : ℕ, Nat.gcd m 6 = 1 →
      C (m % 12) (D * m ^ 2) =
        (if m % 12 = 1 ∨ m % 12 = 7 then (1 : ℤ) else -1) *
          af ((D * m ^ 2 + 1) / 24))
    (hC3 : ∀ m : ℕ, 3 ∣ m → C (m % 12) (D * m ^ 2) = 0)
    (hAfP : ∀ k : ℕ, (af k : ZMod 2) = (pFun k : ZMod 2))
    (hAllOdd : ∀ m : ℕ, Nat.gcd m 6 = 1 → Odd (pFun ((D * m ^ 2 + 1) / 24))) :
    PSCongr 2 FD (ED D) := by
  have h3 : PSCongr 2 FD (lambertF D) :=
    statement3_lambert C FD hD1 hDsf hD24 hFD hC hC3 hAfP
  have h6 : PSCongr 2 (ED D) (eisFD D) := statement6_twist hD1 hDsf
  have h37 : PSCongr 2 (lambertF D) (eisFD D) := by
    rw [pscongr_iff]
    intro N
    simp only [lambertF, eisFD, coeff_mk]
    rw [Int.cast_sum, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro m hm
    split_ifs with hcond
    · obtain ⟨k, hk⟩ := hAllOdd m hcond.1
      rw [hk]
      push_cast
      rw [show (2 : ZMod 2) = 0 by decide]
      ring
    · rfl
  unfold PSCongr at h3 h6 h37 ⊢
  rw [h3, h37, ← h6]

end Statements

end PartitionParity
