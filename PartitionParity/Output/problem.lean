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

theorem statement1_mod4
    (hDurfee : ∀ N : ℕ,
      coeff N P =
        coeff N (1 + ∑ m ∈ Finset.Icc 1 N, X ^ (m ^ 2) * piSeries m ^ 2)) :
    PSCongr 4 P fSeries := by
  sorry

theorem statement1_mod2_consequence
    (hDurfee : ∀ N : ℕ,
      coeff N P =
        coeff N (1 + ∑ m ∈ Finset.Icc 1 N, X ^ (m ^ 2) * piSeries m ^ 2)) :
    ∀ n : ℕ, (af n : ZMod 2) = (pFun n : ZMod 2) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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

theorem statement5_coeff_mod2 (n : ℕ) (hn : 0 < n) :
    (Ecoeff n : ZMod 2) =
      ((ArithmeticFunction.sigma 0
          (n / 2 ^ (n.factorization 2) / 3 ^ (n.factorization 3)) : ℕ) : ZMod 2) := by
  sorry

noncomputable def eisF : PowerSeries ℤ :=
  PowerSeries.mk (fun N => ∑ m ∈ N.divisors, if Nat.gcd m 6 = 1 then (1 : ℤ) else 0)

theorem statement5_mod2 : PSCongr 2 E eisF := by
  sorry

noncomputable def eisFD (D : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun N =>
    ∑ m ∈ N.divisors, if Nat.gcd m 6 = 1 ∧ Nat.gcd (N / m) D = 1 then (1 : ℤ) else 0)

theorem statement6_twist (hD1 : 1 < D) (hDsf : Squarefree D) :
    PSCongr 2 (ED D) (eisFD D) := by
  sorry

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
  sorry

end Statements

end PartitionParity
