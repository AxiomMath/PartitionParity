Please read `KeyFormulasPartitionFunction.tex`.

Formalize and prove ALL seven Key Formulas of that file:
`KF:mod4`, `KF:logderiv`, `KF:lambert`, `KF:residue`, `KF:eis-mod2`, `KF:ED-mod2`, `KF:FeqE`.

GOAL AND SCOPE. The objective is to have Lean verify that each Key Formula holds *as an
implication from the paper's classical data* — i.e. that, given the designated hypotheses
(`hDurfee`, `hGauss`, `hSingle`, `hFD`, the coefficient/character data, etc.), the stated identity
follows. Lean thereby checks the algebra, signs, exponents, and normalizations of each derivation.
This does NOT independently certify the classical inputs themselves (the Durfee identity, the
Gauss-sum value, the single-factor log-derivative), which are cited and assumed per the paper's
conventions C1/C4/C6. Full detailed proof strategies are supplied below; discovering the proofs is
not the objective — verifying the implications is.

The entire run MUST be sorry-free and axiom-free. Do NOT use `sorry`, `admit`, or `axiom`
anywhere, including in comments.

## What is assumed vs. proved (read first)

The paper's conventions C1/C4/C6 permit introducing the paper's *classical data*,�� never the
Key Formulas themselves as named hypotheses. This run honors that split as follows.

TWO classical inputs are the ONLY assumed identities, each a designated hypothesis:

1. `hDurfee` is�� the Durfee-square identity for `P` (spec Lemma 3). Mathlib has no partition
   generating-function API; reproving the bijection is out of scope. It enters `KF_mod4` as a
   hypothesis and is never proved, sorried, or axiomatized.

2. `hGauss` is the Gauss-sum value, packaged purely algebraically as in spec C6.
     This is a cited classical input, not a Key Formula. It enters `KF_logderiv` as a
    hypothesis.

Everything else is to be PROVED from Mathlib. The PRIMARY target for `KF:logderiv` is a genuine
proof: its log-derivative expansion is derived from a finite-truncation formal-log-derivative
construction (see the LOGDERIV MODULE below), collapsed through `hGauss`. The classical *data* it
consumes (the single-factor log-derivative identity, the character/Gauss data) are hypotheses per
C1/C4/C6; the *assembly into the double sum* is proved. A marked re-export fallback for
`KF_logderiv` ONLY is permitted if that assembly cannot be closed in budget — see FALLBACK below;
if used it must be explicitly labelled as recorded-not-derived. No other formula may be re-exported.

Classical *data* hypotheses permitted (C1/C4/C6), never proved: the coefficient-table parity
`hTable`, the Legendre-mod-2 collapse `hLeg`, the Eisenstein coefficient formula as the definition
of `E` (`hEformula`), the local factorization triple for the residue (`ε∈{±1}`, `s²=−D`, `s≠0`),
and the all-odd side condition `hAllOdd`. Each theorem carries only the data hypotheses in its row.

| KF | Label        | Status                        | Data hypotheses it takes            |
|----|--------------|-------------------------------|-------------------------------------|
| 3  | `KF:mod4`    | proved from `hDurfee`         | `hDurfee` (assumed identity)        |
| 4  | `KF:logderiv`| **proved** via LOGDERIV module| `hFD` (binds FD to logDeriv of truncation), `hSingle` (pre-Gauss single-factor, C1), `hGauss` (C6 collapse) |
| 5  | `KF:lambert` | **proved** from KF 4          | `hTable` (C4), `hLeg`               |
| 6  | `KF:residue` | **proved**                    | `ε∈{±1}`, `s²=−D`, `s≠0`            |
| 7  | `KF:eis-mod2`| **proved**                    | `hEformula` (def of E's coeff)      |
| 8  | `KF:ED-mod2` | **proved**                    | `Squarefree D`                      |
| 9  | `KF:FeqE`    | **proved** from KF 5, KF 8    | `hAllOdd` (side condition)          |

## Structural model

Work in the reduced-coefficient reading. Every congruence Key Formula is an equality in
`PowerSeries (ZMod N)` for `N ∈ {2,4}`, via the coefficientwise map
`PowerSeries.map (Int.castRingHom (ZMod N))`. One formal variable, `PowerSeries.X`. Do NOT build
any `LaurentSeries` ambient; the only residue object (`KF:residue`) is finite algebra in a
fraction field over `ℤ[√-D]` and needs no series.

```lean
import Mathlib
set_option linter.unusedVariables false
open Finset PowerSeries

/-- Coefficientwise reduction `PowerSeries ℤ → PowerSeries (ZMod N)`. -/
noncomputable def redN (N : ℕ) : PowerSeries ℤ →+* PowerSeries (ZMod N) :=
  PowerSeries.map (Int.castRingHom (ZMod N))
-- N2 := ZMod 2, N4 := ZMod 4, red2 := redN 2, red4 := redN 4.

/-- `(q;q)_m = ∏_{j=1}^m (1 - X^j)`. -/
noncomputable def qPoch (m : ℕ) : PowerSeries ℤ := ∏ j ∈ Finset.Icc 1 m, (1 - PowerSeries.X ^ j)

/-- `πₘ = 1/(q;q)_m`. -/
noncomputable def piSeries (m : ℕ) : PowerSeries ℤ := Ring.inverse (qPoch m)

/-- Constant-term-one predicate. -/
def ConstOne {R : Type*} [CommRing R] (A : PowerSeries R) : Prop := PowerSeries.constantCoeff R A = 1

/-- Admissibility `(m,6)=1`. -/
def Admissible (m : ℕ) : Prop := Nat.Coprime m 6

/-- The {2,3}-free part of `n`. -/
def oddCoprime6part (n : ℕ) : ℕ := n / (2 ^ (n.factorization 2) * 3 ^ (n.factorization 3))
```

`P f F_D E E_D : PowerSeries ℤ` and `AD Cst chiD Ecoeff : ℕ → ℤ` are theorem ARGUMENTS
(opaque parameters), constrained only by the hypotheses each theorem lists. Locate uncertain
Mathlib names with `exact?`/`#check`; none is load-bearing (each has equivalent spellings).

## LOGDERIV MODULE — the one genuinely new piece (finite-truncation log-derivative)

Do NOT assume `KF:logderiv`, and do NOT assume the product-to-sum law as a hypothesis. Prove it,
staying finite throughout. This section is now fully concrete: `FD` is BOUND to the log-derivative
of the truncated products, `hSingle` is the genuine PRE-Gauss single-factor identity, `hGauss`
performs the character collapse, and `hCoeff` is exponent-table data only. There are no
placeholders and no `True` hypotheses — produce the signatures exactly as written below.

Key finiteness fact: the `k`-th coefficient of `logDeriv (∏_{m=1}^{N} f m)` is independent of `N`
once `N ≥ k`, because each `f m ∈ 1 + X^m·ℤ[[X]]` contributes nothing to `logDeriv` below degree
`m`. So define `FD` via any truncation past the coefficient being read; the object is well-defined
coefficientwise without any infinite product.

### Definitions to add (concrete; no `tsum`, no infinite product)

```lean
/-- Formal `Θ = X · d/dX` on `PowerSeries ℤ`. Locate the derivation as
`PowerSeries.derivativeFun`/`PowerSeries.d⁄dX` with `exact?`; call the chosen one `Dser`. -/
noncomputable def Theta (A : PowerSeries ℤ) : PowerSeries ℤ := PowerSeries.X * (Dser A)

/-- Formal logarithmic derivative on the unit subgroup `1 + X·ℤ[[X]]`. -/
noncomputable def logDeriv (A : PowerSeries ℤ) : PowerSeries ℤ := (Theta A) * Ring.inverse A

/-- The `m`-th Borcherds factor to the power given by the exponent table `Cst m`.
`base m : PowerSeries ℤ` is the single Borcherds factor `P_D(q^m)` as an opaque parameter with
`ConstOne (base m)`; its ONLY assumed property is `hSingle` below. -/
noncomputable def Psi (base : ℕ → PowerSeries ℤ) (Cst : ℕ → ℤ) (m : ℕ) : PowerSeries ℤ :=
  (base m) ^ (Cst m).toNat * Ring.inverse ((base m) ^ (Cst m).natAbs - (base m) ^ (Cst m).toNat + 1)
  -- NOTE: if signed powers are awkward, instead carry `base` already raised: let `fac m := base m`
  -- and fold `Cst m` into `hSingle`'s RHS. Prefer whichever typechecks; the exponent must appear
  -- as a factor of the coefficient, matching `hCoeff`.

/-- Truncated product of the first `N` factors. -/
noncomputable def PsiProd (base : ℕ → PowerSeries ℤ) (Cst : ℕ → ℤ) (N : ℕ) : PowerSeries ℤ :=
  ∏ m ∈ Finset.Icc 1 N, Psi base Cst m
```

### Lemmas to PROVE (this is the genuinely new content — full skeletons supplied)

The verification target is the IMPLICATION: given the classical data hypotheses, the expansion
follows. You are NOT required to discover these proofs; the strategy below is authoritative.
Transcribe it, then repair only where a Mathlib name or a coercion differs from what is written
(use `exact?`/`#check`/`rw?` to find the true names). Keep the statements verbatim.

Supporting facts to establish first (all elementary, coefficientwise):

```lean
-- F0: Theta is additive and satisfies the Leibniz rule (Theta is X * derivative).
lemma Theta_add (A B : PowerSeries ℤ) : Theta (A + B) = Theta A + Theta B := by
  unfold Theta; rw [map_add]; ring            -- `Dser` additive; `mul_add`
lemma Theta_mul (A B : PowerSeries ℤ) : Theta (A * B) = Theta A * B + A * Theta B := by
  unfold Theta
  -- `Dser (A*B) = Dser A * B + A * Dser B` is the derivation law: find it as
  -- `PowerSeries.derivativeFun_mul` / `Derivation.leibniz`; then distribute `X *` and `ring`.
  sorry_PLAN  -- replace: rw [<derivation_mul_lemma>]; ring

-- F1: on the unit subgroup, Ring.inverse is multiplicative.
lemma inverse_mul_of_unit (A B : PowerSeries ℤ) (hA : ConstOne A) (hB : ConstOne B) :
    Ring.inverse (A * B) = Ring.inverse A * Ring.inverse B := by
  have uA : IsUnit A := by
    rw [PowerSeries.isUnit_iff_constantCoeff_isUnit]; rw [hA]; exact isUnit_one
  have uB : IsUnit B := by
    rw [PowerSeries.isUnit_iff_constantCoeff_isUnit]; rw [hB]; exact isUnit_one
  rw [Ring.mul_inverse_rev]           -- or `Ring.inverse_mul_eq...`; commutative ring, so reorder
  rw [mul_comm]
```

L1 (`logDeriv_mul`): for `ConstOne A`, `ConstOne B`,
`logDeriv (A * B) = logDeriv A + logDeriv B`.
```lean
lemma logDeriv_mul (A B : PowerSeries ℤ) (hA : ConstOne A) (hB : ConstOne B) :
    logDeriv (A * B) = logDeriv A + logDeriv B := by
  unfold logDeriv
  rw [Theta_mul, inverse_mul_of_unit A B hA hB]
  have uA : IsUnit A := by rw [PowerSeries.isUnit_iff_constantCoeff_isUnit, hA]; exact isUnit_one
  have uB : IsUnit B := by rw [PowerSeries.isUnit_iff_constantCoeff_isUnit, hB]; exact isUnit_one
  -- (ΘA·B + A·ΘB) · (A⁻¹·B⁻¹) = ΘA·A⁻¹ + ΘB·B⁻¹, using A·A⁻¹=1, B·B⁻¹=1.
  have hAinv : A * Ring.inverse A = 1 := Ring.mul_inverse_cancel A uA
  have hBinv : B * Ring.inverse B = 1 := Ring.mul_inverse_cancel B uB
  ring_nf
  -- After ring_nf the goal is a polynomial identity in A,B,ΘA,ΘB,A⁻¹,B⁻¹ modulo hAinv,hBinv.
  -- Close by rewriting the two cancellation facts then `ring`. If `ring` alone does not see the
  -- cancellations, `rw`/`simp only [hAinv, hBinv]` first, then `ring`.
  sorry_PLAN
```

L2 (`logDeriv_prod`): `logDeriv (PsiProd base Cst N) = ∑ m ∈ Icc 1 N, logDeriv (Psi base Cst m)`.
```lean
-- First: each factor and every partial product is ConstOne.
lemma constOne_Psi (m : ℕ) : ConstOne (Psi base Cst m) := by
  -- constant term of base m is 1 (hbase), powers/inverse preserve constant term 1.
  sorry_PLAN
lemma constOne_PsiProd (N : ℕ) : ConstOne (PsiProd base Cst N) := by
  unfold PsiProd ConstOne
  rw [map_prod]                    -- constantCoeff of a Finset.prod
  apply Finset.prod_eq_one
  intro m _; exact constOne_Psi m  -- each factor's constant coeff is 1
lemma logDeriv_prod (N : ℕ) :
    logDeriv (PsiProd base Cst N) = ∑ m ∈ Finset.Icc 1 N, logDeriv (Psi base Cst m) := by
  unfold PsiProd
  induction N with
  | zero => simp [PsiProd, logDeriv, Theta]      -- empty product = 1; logDeriv 1 = 0
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega)]     -- ∏_{1..n+1} = (∏_{1..n}) * Psi (n+1)
    rw [logDeriv_mul _ _ (constOne_PsiProd n) (constOne_Psi (n+1))]
    rw [ih, Finset.sum_Icc_succ_top (by omega)]
-- NOTE: `logDeriv 1 = 0` because Theta 1 = 0 (derivative of a constant). Prove `Theta_one` if
-- needed: `Theta 1 = X * Dser 1 = X * 0 = 0`.
```

L3 (`coeff_stable`): for `k ≤ N`,
`coeff ℤ k (logDeriv (PsiProd base Cst N)) = coeff ℤ k (logDeriv (PsiProd base Cst (k+1)))`.
```lean
-- Key input: Psi base Cst m ∈ 1 + X^m·(…), so logDeriv (Psi … m) has coeff j = 0 for j < m.
lemma logDeriv_Psi_low_vanish (m j : ℕ) (hj : j < m) :
    PowerSeries.coeff ℤ j (logDeriv (Psi base Cst m)) = 0 := by
  -- base m ∈ 1 + X·…, so base m raised & inverted stays 1 + X^{≥1}; Theta multiplies by X.
  -- The single-factor identity `hSingle` already encodes this (its `if m ∣ n ∧ 1 ≤ n/m` guard is
  -- false for 0 < j < m). PREFER to derive this FROM `hSingle` at the point of use rather than
  -- reprove it structurally.
  sorry_PLAN
lemma coeff_stable (k N : ℕ) (hk : k ≤ N) :
    PowerSeries.coeff ℤ k (logDeriv (PsiProd base Cst N))
      = PowerSeries.coeff ℤ k (logDeriv (PsiProd base Cst (k+1))) := by
  -- Both equal ∑_{m=1}^{min} coeff k (logDeriv (Psi m)); factors with m > k contribute 0 by
  -- logDeriv_Psi_low_vanish, so the sums over Icc 1 N and Icc 1 (k+1) agree.
  rw [logDeriv_prod, logDeriv_prod, map_sum, map_sum]
  -- reduce both sums to Icc 1 k (drop m>k terms as zero), then rfl.
  sorry_PLAN
```

`sorry_PLAN` is a MARKER in this SPEC only, showing exactly where a short tactic step remains; it
is NOT Lean syntax and MUST NOT appear in the delivered file. Each marks a ≤5-line obligation whose
method is stated in the adjacent comment. The delivered `problem.lean` contains no `sorry`,
`sorry_PLAN`, `admit`, or `axiom`.

### Concrete hypotheses (produce VERBATIM — no placeholders)

`hSingle` is the PRE-Gauss single-factor identity of Definition~\ref{def:psi}(i): the log-derivative
of factor `m`, before the character sum is collapsed, has `q^{mk}`-coefficient given by the
root-of-unity sum `-(Cst m) * m * (∑ b in range D, ζ b (m*k))`, where `ζ : ℕ → ℕ → ℤ` packages the
integer real/imaginary data of `e(-b·/D)` in `Zsqrtd (-(D:ℤ))`. `hGauss` then collapses
`∑ b, ζ b n = -(chiD n) * (the √-D component)`, and dividing by `√-D` (via `hGauss : √-D squared = -D`)
yields the `chiD (k/m)` factor. State them as:

```lean
-- packaged character/root-of-unity data (opaque integer coefficients), C1
(zeta : ℕ → ℕ → ℤ)
-- hSingle: pre-Gauss single-factor log-derivative, coefficientwise (C1 data)
(hSingle : ∀ m n : ℕ, 1 ≤ m →
    PowerSeries.coeff ℤ n (logDeriv (Psi base Cst m))
      = (if m ∣ n ∧ 1 ≤ n / m then - Cst m * (m : ℤ) * (∑ b ∈ Finset.range D, zeta b (n / m)) else 0))
-- hGauss: the Gauss-sum collapse of the character data to chiD, using √-D squared = -D (C6 data)
(hGauss : ∀ n : ℕ, 1 ≤ n → (∑ b ∈ Finset.range D, zeta b n) = - chiD n)
```

There is deliberately NO `hCoeff` hypothesis. `Cst : ℕ → ℤ` is already a free parameter of the
theorem (the paper's exponent table `C(m̄; D m²)`), and it enters the conclusion directly through
`hSingle`. A separate `hCoeff` naming-constraint would be either vacuous (`Cst m = Cst m`) or a
smuggled binding; both are rejected. Do not add one.

Note the collapse: substituting `hGauss` into `hSingle` gives coefficient `n` of each factor's
`logDeriv` as `Cst m * chiD (n/m) * [m ∣ n ∧ 1 ≤ n/m]`. This is where `hGauss` is genuinely USED
(GPT-5.5's second rejection point); `hSingle` must stay in pre-collapse `zeta` form so `hGauss` is
not redundant.

### The theorem (produce VERBATIM)

```lean
theorem KF_logderiv
    (D : ℕ) (hD : 1 < D)
    (base : ℕ → PowerSeries ℤ) (hbase : ∀ m, ConstOne (base m))
    (Cst chiD : ℕ → ℤ) (zeta : ℕ → ℕ → ℤ)
    (FD : PowerSeries ℤ)
    -- FD is BOUND (not arbitrary): its k-th coefficient is that of the truncation past k.
    (hFD : ∀ k : ℕ, PowerSeries.coeff ℤ k FD
              = PowerSeries.coeff ℤ k (logDeriv (PsiProd base Cst (k + 1))))
    (hSingle : ∀ m n : ℕ, 1 ≤ m →
        PowerSeries.coeff ℤ n (logDeriv (Psi base Cst m))
          = (if m ∣ n ∧ 1 ≤ n / m then
                - Cst m * (m : ℤ) * (∑ b ∈ Finset.range D, zeta b (n / m)) else 0))
    (hGauss : ∀ n : ℕ, 1 ≤ n → (∑ b ∈ Finset.range D, zeta b n) = - chiD n) :
    FD = PowerSeries.mk (fun k =>
        ∑ m ∈ (k + 1).divisors, Cst m * chiD (k / m) *
          (if k % m = 0 ∧ 1 ≤ m ∧ 1 ≤ k / m then 1 else 0)) := by
  ext k                                            -- PowerSeries.ext: reduce to coeff k
  rw [PowerSeries.coeff_mk, hFD k, logDeriv_prod]  -- FD's coeff = coeff of truncated log-deriv
  rw [map_sum]                                     -- coeff k (∑_m …) = ∑_m coeff k (…)
  -- Now: ∑_{m ∈ Icc 1 (k+1)} coeff k (logDeriv (Psi m)) = ∑_{m ∈ (k+1).divisors} Cst m · χ(k/m) · guard
  -- Step A: rewrite each summand by hSingle (m ≥ 1 on Icc 1 (k+1)).
  rw [Finset.sum_congr rfl (fun m hm => by
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      rw [hSingle m k hm1])]
  -- Step B: only m ∣ k (with 1 ≤ k/m) survive the `if`; collapse ∑_b zeta via hGauss.
  --   For surviving m: - Cst m * m * (∑_b zeta b (k/m)) = - Cst m * m * (- chiD (k/m))
  --                    = Cst m * m * chiD (k/m).   [hGauss needs 1 ≤ k/m, which the guard gives]
  -- Step C: reindex the divisor set. `Icc 1 (k+1)` restricted to `m ∣ k` equals `k.divisors`;
  --   note the RHS uses `(k+1).divisors` with guard `k % m = 0`, i.e. m ∣ k. Bridge with
  --   `Nat.mem_divisors`, `Nat.divisor_le`, and `Finset.sum_filter`/`Finset.sum_subset` to match
  --   supports. The `m` factor from Θ combines with `Cst m · chiD` — CHECK the RHS carries the
  --   `m` weight: if the displayed RHS lacks the `* m`, fold it into `Cst` via the paper's
  --   normalization OR add the `(m:ℤ)*` to the RHS (allowed refinement; state a bridging eq).
  -- Close each surviving coefficient with `ring`; vanishing terms by the false `if` guard.
  sorry_PLAN  -- Steps B+C: finite reindex + hGauss substitution + ring. NOT an assumption.
```

IMPORTANT normalization check for Step C: the single-factor `hSingle` carries a factor `(m : ℤ)`
(from `Θ = X·d/dX` acting on `q^{mk}` giving `mk`, then `/k` … — verify against
Definition~\ref{def:psi}(i)). The displayed RHS must carry the matching weight. If the paper's
`C(m̄; Dm²)` already absorbs the `m`, drop the extra `(m:ℤ)*` from `hSingle`; otherwise add
`(m:ℤ)*` to the RHS and record the equality as a one-line bridging lemma. Either way the two sides
must be DEFINITIONALLY the same series — do not leave a silent mismatch.

The proof above is a SKELETON with `sorry_PLAN` marking the two remaining finite steps; the shipped
file replaces it and contains no `sorry`/`sorry_PLAN`/`admit`/`axiom`. This is NOT `:= hExpansion`;
the product-to-sum law is L2 (proved), never a hypothesis. The `1 ≤ k / m` guard closes the
`k = 0` leak (guard false at k=0 ⇒ no `chiD 0`); the SAME guard is in the KF 5 / KF 9 RHS below.

FALLBACK (permitted, for `KF_logderiv` ONLY — must be explicit and marked):
First attempt the genuine proof via L1–L3 and the assembly above; that is the primary target.
If, and only if, L2 or L3 cannot be closed within budget, you MAY close `KF_logderiv` by the
re-export route below, so the file still ships sorry-free. This trades a genuine derivation for a
tautology on this one formula; it MUST be labelled so no reader mistakes it for a proof.

Re-export form (use ONLY as fallback):
```lean
theorem KF_logderiv_reexport
    (D : ℕ) (hD : 1 < D) (Cst chiD : ℕ → ℤ) (FD : PowerSeries ℤ)
    -- FALLBACK: the expansion is ASSUMED as `hExpansion`, not derived. This formula is RECORDED,
    -- not proved. Used only because the L1–L3 finite-truncation assembly did not close in budget.
    (hExpansion : FD = PowerSeries.mk (fun k =>
        ∑ m ∈ (k + 1).divisors, Cst m * chiD (k / m) *
          (if k % m = 0 ∧ 1 ≤ m ∧ 1 ≤ k / m then 1 else 0))) :
    FD = PowerSeries.mk (fun k =>
        ∑ m ∈ (k + 1).divisors, Cst m * chiD (k / m) *
          (if k % m = 0 ∧ 1 ≤ m ∧ 1 ≤ k / m then 1 else 0)) := hExpansion
```
Rules for the fallback, all mandatory:
- It applies to `KF_logderiv` and NOTHING ELSE. Never `sorry` or re-export any other theorem.
- CRITICAL — no orphaned sorries: taking the fallback means the genuine-proof apparatus is NOT
  needed, so you MUST DELETE it entirely from the delivered file: `Theta_mul` (its sorry_PLAN
  step), `inverse_mul_of_unit`, L1 `logDeriv_mul`, L2 `logDeriv_prod`, L3 `coeff_stable`,
  `constOne_Psi`, `constOne_PsiProd`, `logDeriv_Psi_low_vanish`, and the `Psi`/`PsiProd`/`logDeriv`
  defs IF nothing else uses them. The re-export needs ONLY `hExpansion`. Do NOT leave L1–L3 in the
  file with `sorry`/`sorry_PLAN` bodies — that would make the file NOT sorry-free and defeat the
  fallback. The file must compile with zero `sorry` regardless of which path is taken.
- Equivalently: the delivered file is ALL-OR-NOTHING on the log-derivative apparatus. Either
  (genuine path) L1–L3 are all present AND fully closed with no sorries, OR (fallback path) L1–L3
  are entirely ABSENT and `KF_logderiv_reexport` stands alone. There is no in-between state where
  L1–L3 exist but carry sorries.
- If used, the delivered file must contain a top-of-file comment
  `-- NOTE: KF_logderiv is RECORDED via hExpansion re-export (fallback), not derived from L1–L3.`
  and a `#print axioms KF_logderiv_reexport` line so the status is auditable.
- Report in the run summary WHICH lemma (L2 or L3, or the assembly) forced the fallback.
- KF 5 still takes the (identical) conclusion as its `hExp` argument and builds either way.
- Do NOT use the fallback pre-emptively. Attempt L1–L3 first; fall back only on genuine failure.

## Theorem statements (produce verbatim; only proofs open)

```lean
-- KF 3. P ≡ f (mod 4), from the assumed Durfee identity + reciprocal stability (proved inline).
theorem KF_mod4
    (P f : PowerSeries ℤ) (hPunit : ConstOne P) (hfunit : ConstOne f)
    (hDurfee : P = 1 + ∑' m : ℕ, (if m = 0 then 0 else
        PowerSeries.X ^ (m ^ 2) * (piSeries m) ^ 2))
    (hf : f = 1 + ∑' m : ℕ, (if m = 0 then 0 else
        PowerSeries.X ^ (m ^ 2) * (Ring.inverse (∏ j ∈ Finset.Icc 1 m,
            (1 + PowerSeries.X ^ j))) ^ 2)) :
    red4 P = red4 f
-- Reciprocal stability mod 4 (old KF 2) is PROVED inline as a private lemma:
--   ConstOne A → ConstOne B → red4 A = red4 B → red4 (Ring.inverse A) = red4 (Ring.inverse B)
-- via `PowerSeries.isUnit_iff_constantCoeff_isUnit` + `Ring.inverse` commuting with the ring map.
-- Core congruence: red4 ((1-X^j)^2) = red4 ((1+X^j)^2) since (1∓X^j)^2 differ by 4X^j ≡ 0.
-- If `tsum` over PowerSeries is awkward, restate both sides coefficientwise with `PowerSeries.mk`
-- (the integer identity still comes from hDurfee).

-- KF 4. See LOGDERIV MODULE above.

-- KF 5. Mod-2 Lambert reduction, PROVED from KF 4's conclusion.
theorem KF_lambert
    (D : ℕ)
    (FD : PowerSeries ℤ) (Cst chiD AD : ℕ → ℤ)
    (hExp : FD = PowerSeries.mk (fun k =>
        ∑ m ∈ (k+1).divisors, Cst m * chiD (k / m) *
          (if k % m = 0 ∧ 1 ≤ m ∧ 1 ≤ k / m then 1 else 0)))
    (hTable : ∀ m : ℕ, 1 ≤ m →
        ((Cst m : ZMod 2) = (if Admissible m then (AD m : ZMod 2) else 0)))
    (hLeg : ∀ n : ℕ, (chiD n : ZMod 2) = (if Nat.Coprime n D then 1 else 0)) :
    red2 FD = PowerSeries.mk (fun k =>
        ∑ m ∈ (k+1).divisors, (if Admissible m then (AD m : ZMod 2) else 0) *
          (if Nat.Coprime (k / m) D ∧ k % m = 0 ∧ 1 ≤ m ∧ 1 ≤ k / m then 1 else 0))
-- `hExp` is KF 4's PROVED conclusion (guard `1 ≤ k/m` matches KF_logderiv verbatim), passed in —
-- not an independent assumption. `D` is now explicitly bound.

-- KF 6. Residue over ℤ[√-D], in its fraction field. Finite algebra, no series.
theorem KF_residue
    (D : ℕ) (hDodd : Odd D) (hD1 : 1 < D)
    (eps : ℤ) (heps : eps = 1 ∨ eps = -1)
    (K : Type*) [Field K] [Algebra (Zsqrtd (-(D:ℤ))) K]
    (s : K) (hs : s * s = algebraMap _ K (⟨-(D:ℤ), 0⟩ : Zsqrtd (-(D:ℤ)))) (hs0 : s ≠ 0) :
    ((eps : K) / s = 1 / s ∨ (eps : K) / s = -(1 / s)) ∧ s ≠ 0
-- `rcases heps` then `simp`/`ring`; conjunct is `hs0`.

-- KF 7. Eisenstein coefficient mod-2 collapse. `hEformula` DEFINES E's coefficient.
theorem KF_eis_mod2
    (E : PowerSeries ℤ) (Ecoeff : ℕ → ℤ)
    (hEcoeff : ∀ n : ℕ, (PowerSeries.coeff ℤ n) E = Ecoeff n)
    (hEformula : ∀ n : ℕ, Ecoeff n =
        (Nat.ArithmeticFunction.sigma 1 n : ℤ)
        - 4 * (if 2 ∣ n then (Nat.ArithmeticFunction.sigma 1 (n/2) : ℤ) else 0)
        + 3 * (if 3 ∣ n then (Nat.ArithmeticFunction.sigma 1 (n/3) : ℤ) else 0)) :
    ∀ n : ℕ, 1 ≤ n →
      ((Ecoeff n : ZMod 2) = (Nat.ArithmeticFunction.sigma 0 (oddCoprime6part n) : ZMod 2))
-- Proof: (4:ZMod2)=0 kills the middle term, 3≡1; factor n=2^a·3^b·u by multiplicativity of σ₁;
-- σ₁(2^a) odd; σ₁(3^b)+[3∣n]σ₁(3^{b-1}) ≡ 1; σ₁(u) ≡ σ₀(u) since divisors of odd u are odd.
-- Track parities in ZMod 2 from the start (avoid ℕ subtraction). Give `maxHeartbeats 800000`.
-- Fallback lemma if the 3-collapse is fiddly: `(σ₁(3^b) : ZMod 2) = 1` by induction on b.

-- KF 8. D-twist multiplier: squarefree divisor-count parity.
theorem KF_ED_mod2
    (D : ℕ) (hDsqf : Squarefree D) (n : ℕ) :
    Odd (∑ δ ∈ (Nat.gcd D n).divisors, 1) ↔ Nat.Coprime D n
-- ∑_{δ|g}1 = d(g); g=gcd D n | D squarefree ⇒ g squarefree ⇒ d(g)=2^ω(g); Odd(2^ω)↔ω=0↔g=1↔coprime.
-- NOTE: this proves the arithmetic core (the (n,D)=1 survival). If you also want the full
-- E_D SERIES identity of the displayed KF:ED-mod2, add a wrapper theorem concluding
-- `red2 E_D = mk (…(n,D)=1 indicator…)` from KF 7 and this multiplier; keep BOTH.

-- KF 9. All-odd ⇒ F_D ≡ E_D (mod 2), PROVED from KF 5 and KF 8's series RHS's.
theorem KF_FeqE
    (D : ℕ)
    (FD ED : PowerSeries ℤ) (AD : ℕ → ℤ)
    (hF : red2 FD = PowerSeries.mk (fun k =>
        ∑ m ∈ (k+1).divisors, (if Admissible m then (AD m : ZMod 2) else 0) *
          (if Nat.Coprime (k / m) D ∧ k % m = 0 ∧ 1 ≤ m ∧ 1 ≤ k / m then 1 else 0)))
    (hE : red2 ED = PowerSeries.mk (fun k =>
        ∑ m ∈ (k+1).divisors, (if Admissible m then (1 : ZMod 2) else 0) *
          (if Nat.Coprime (k / m) D ∧ k % m = 0 ∧ 1 ≤ m ∧ 1 ≤ k / m then 1 else 0)))
    (hAllOdd : ∀ m : ℕ, Admissible m → (AD m : ZMod 2) = 1) :
    red2 FD = red2 ED
-- `D` explicitly bound; guards match KF_lambert/KF_ED_mod2 verbatim.
-- `by_cases Admissible m`; true branch uses `hAllOdd`, false branch `rfl`; `Finset.sum_congr rfl`.
```

## Conventions (binding)

- Congruence formulas live in `PowerSeries (ZMod N)` via `redN`; never `LaurentSeries`. Close
  series equalities by `PowerSeries.ext` unless a structural `rw` suffices.
- ASSUMED DATA (never proved/axiomatized/sorried), each a concrete named hypothesis, none of them
  a Key Formula and none the product-to-sum law: `hDurfee` (KF 3), `hGauss` (the Gauss-sum
  collapse, C6), `hSingle` (pre-Gauss single-factor identity, C1), `hFD` (binds `FD` to the
  log-derivative of the truncation — a definition of `FD`, not an identity between series),
  `hTable`, `hLeg` (C4), `hEformula`/`hEcoeff` (define `E`'s coefficient), the residue triple
  (`ε∈{±1}`, `s²=−D`, `s≠0`), `hAllOdd` (side condition).
- PROVED from Mathlib (NOT assumed as hypotheses): the reciprocal-stability lemma; the LOGDERIV
  lemmas L1 (`logDeriv_mul`), L2 (`logDeriv_prod`, the product-to-sum law), L3 (`coeff_stable`);
  the `KF_logderiv` assembly (rewrite by `hFD`, L2, `hSingle`, collapse by `hGauss`, reindex);
  KF_lambert, KF_residue, KF_eis_mod2, KF_ED_mod2, KF_FeqE. The product-to-sum law must NOT appear
  as a hypothesis of any theorem — if it does, the run is rejected (this was GPT-5.5's finding).
- No `axiom`, no `sorry`, no `admit`, anywhere. The shipped file must compile clean.
- You MAY refine a coefficient encoding to typecheck, but a refined form must be PROVABLY equal to
  the displayed one (add a bridging lemma) and parity conclusions must be unchanged.

## Build hygiene

- `set_option linter.unusedVariables false` at file top; prefix unused binders with `_`.
- Budget only the heavy theorems: `KF_eis_mod2` (`maxHeartbeats 800000`) and, if needed,
  `KF_mod4` and the LOGDERIV assembly (`maxHeartbeats 400000`). The rest run under default.
- Lint warnings are non-fatal.

## Feasibility

Five formulas (KF 5,6,7,8,9) are short, robust Mathlib proofs over `ZMod`, `Finset`,
`Nat.ArithmeticFunction`, and unit/ring-map API. KF 3 consumes the one assumed identity `hDurfee`
plus an inline reciprocal-stability lemma. The single genuinely new construction is the
finite-truncation log-derivative for KF 4; it is finite at every coefficient (only factors
`m ≤ k` contribute), so it carries no unbounded obligation. Attempt it genuinely first via L1–L3.
If it does not close in budget, the marked `hExpansion` re-export (FALLBACK) closes `KF_logderiv`
sorry-free while recording — visibly, via the required NOTE comment and `#print axioms` — that this
one formula is recorded rather than derived. Either way the file ships sorry-free and axiom-free
with all seven formulas closed; the only variable is whether formula 4 is genuinely proved or
flagged as a re-export. Every failure path must be reported in the run summary, never hidden.
