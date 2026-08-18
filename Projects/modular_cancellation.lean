import Mathlib.Tactic

/-
We will be proving the following theorem from year 1 number theory:
# Main Theorem : Modular Cancellation
If `m > 0` and `d = gcd(a, m)`, then `a * x ≡ a * y [mod m] ↔ x ≡ y [mod (m / d)]`
-/

-- Definitions

/-- a is congruent to b modulo m (mod a b m) is defined as `a - b = m * k` for some integer k -/
def mod (a b m : ℤ)  : Prop :=
  ∃ k : ℤ , a - b = m * k

/-- d is the gcd of a and b (is_gcd d a b) if it is nonnegative, it divides both a and b and
any other integer c that divides both and and b also divides d -/
def is_gcd (d a b : ℤ) : Prop :=
  (d > 0) ∧
  (d ∣ a) ∧
  (d ∣ b) ∧
  (∀ c : ℤ, (c ∣ a ∧ c ∣ b) → c ∣ d)

-- Lemmas

/-- The gcd of a and b, by its definition, divides both a and b. Lemma included for readability
in later theorems, though it could be omitted by its simplicity -/
lemma gcd_divides_both (d a b : ℤ) (hd : is_gcd d a b) : d ∣ a ∧ d ∣ b := by
  rcases hd with ⟨_, hda, hdb, _⟩
  exact ⟨hda, hdb⟩

/-- If d is the gcd of a and m, and we have `a = d * a'` and `m = d * m'`, with `d ≠ 0`,
then 1 is the gcd of a' and m'-/
lemma gcd_divided
  (d a m a' m' : ℤ)
  (hgcd : is_gcd d a m)
  (ha : a = d * a')
  (hm : m = d * m') :
  is_gcd 1 a' m' := by
  unfold is_gcd
  refine ⟨?h1, ?h2, ?h3, ?h4⟩
  · decide
  · exact one_dvd a'
  · exact one_dvd m'
  · intro c hc
    rcases hc with ⟨ha', hm'⟩

    -- rewrite divisibility as `a' = c * x` and `m' = c * y` and substitute
    rcases ha' with ⟨x, rfl⟩
    rcases hm' with ⟨y, rfl⟩

    -- now we show `(c * d)` divides a and m, using x and y
    have hcda : c * d ∣ a := by
      refine ⟨x, ?_⟩
      -- using ha, re arrange with commutative property : `a = d * (c * x) = (c * d) * x`
      simp [ha, mul_comm, mul_left_comm]

    have hcdm : c * d ∣ m := by
      refine ⟨y, ?_⟩
      simp [hm, mul_comm, mul_left_comm]

    -- since `(c * d)` divides both, it divides their gcd by definition : `(c * d) | d`
    rcases hgcd with ⟨hdg0, _, _, hdiv⟩
    have hcdd : c * d ∣ d := by
      exact hdiv (c * d) ⟨hcda, hcdm⟩

    -- using the fact that `c * d | d` and `d ≠ 0`, we can show `c | 1`
    rcases hcdd with ⟨k, hk⟩
    have h1 : 1 = c * k := by
      have hdneq0 : d ≠ 0 := ne_of_gt hdg0
      apply mul_left_cancel₀ hdneq0
      calc
        d * 1 = d := by
          exact mul_one d
        _ = c * d * k := hk
        _ = d * (c * k) := by ring
    exact ⟨k, h1⟩

/-- If 1 is the gcd of a and b (by is_gcd), then a and b are coprime using Lean's definition of
coprimality IsCoprime. We first show equivalence between is_gcd and Int.gcd when gcd = 1,
leading to Lean's IsCoprime -/
lemma gcd_to_coprime (a b : ℤ) :
  is_gcd 1 a b → IsCoprime a b := by
  intro hgcd
  rcases hgcd with ⟨_, _, _, hc⟩

  -- Int.gcd a b by definition divides both a and b, so it divides 1, the gcd of a and b by is_gcd
  have hint1 : (Int.gcd a b : ℤ) ∣ (1 : ℤ) :=
    hc (Int.gcd a b) ⟨Int.gcd_dvd_left a b, Int.gcd_dvd_right a b⟩

  -- Int.gcd a b = +- 1 because it divides 1
  have h1 : (Int.gcd a b : ℤ) = 1 ∨ (Int.gcd a b : ℤ) = -1 :=
    have hunit : IsUnit (Int.gcd a b : ℤ) := by
      exact (isUnit_iff_dvd_one).2 hint1
    Int.isUnit_eq_one_or hunit

  -- rule out -1 by contradiction since (Int.gcd a b : ℤ) is ≥ 0
  have h2 : (Int.gcd a b : ℤ) = 1 := by
    rcases h1 with hpos | hneg
    · exact hpos
    · have hnonneg : 0 ≤ (Int.gcd a b : ℤ) :=
        Int.natCast_nonneg (Int.gcd a b)

      simp [hneg] at hnonneg

  -- cast back to naturals
  have hgcdnat : Int.gcd a b = 1 := by
    exact Int.ofNat.inj h2

  exact (Int.isCoprime_iff_gcd_eq_one).2 hgcdnat

-- Main Theorem

/-- Modular Cancellation :
If `m > 0` and `d = gcd(a, m)`, then `a * x ≡ a * y [mod m] ↔ x ≡ y [mod (m / d)]` -/
theorem modular_cancellation
  (a m d: ℤ) (hgcd : is_gcd d a m):
  ∀ x y : ℤ,
    mod (a * x) (a * y) m ↔
    ∃ q : ℤ, m = d * q ∧ mod x y q := by
  intro x y
  constructor

  -- (a) → (b)
  · intro h1
    rcases h1 with ⟨k, hk⟩

    -- express divisibility as `m = d * q` and `a = d * a'`
    have hdm : d ∣ m := (gcd_divides_both d a m hgcd).2
    rcases hdm with ⟨q, hq⟩
    refine ⟨q, hq, ?_⟩

    have hda : d ∣ a := (gcd_divides_both d a m hgcd).1
    rcases hda with ⟨a', ha'⟩

    -- re-arrange hk substituting in hq and ha'
    have hk1 : d * (a' * (x - y)) = d * (q * k) := by
      calc
        d * (a' * (x - y)) = (d * a') * (x - y) := by ring
        _ = a * (x - y) := by rw [ha']
        _ = a * x - a * y := by ring
        _ = m * k := hk
        _ = (d * q) * k := by rw [hq]
        _ = d * (q * k) := by ring

    -- by definition of gcd, deduce `d ≠ 0` hence allowing to divide by d
    have hdneq0 : d ≠ 0 := ne_of_gt hgcd.1
    have hk2 : a' * (x - y) = q * k := mul_left_cancel₀ hdneq0 hk1

    have hdiv : q ∣ a' * (x - y) := by
      refine ⟨k, ?_⟩
      exact hk2

    -- using gcd_divided, we show 1 is the gcd of a' and q, hence they are coprime
    have hgcd1 : is_gcd 1 a' q := by
      exact gcd_divided d a m a' q hgcd ha' hq

    have hcop : IsCoprime q a' := (gcd_to_coprime a' q hgcd1).symm

    -- apply Euclid's Lemma
    have hq_div_xy : q ∣ (x - y) :=
      hcop.dvd_of_dvd_mul_left hdiv

    rcases hq_div_xy with ⟨t, ht⟩
    exact ⟨t, ht⟩

  -- (b) → (a)
  · rintro ⟨q, hq, ⟨k, hk⟩⟩

    -- d | a by property of the gcd
    have hda : d ∣ a := (gcd_divides_both d a m hgcd).1
    rcases hda with ⟨a', ha'⟩

    refine ⟨a' * k, ?_⟩

    -- re-arranging and substituting terms, obtain a * x ≡ a * y (mod m)
    calc
      a * x - a * y = a * (x - y) := by ring
      _ = a * (q * k) := by rw [hk]
      _ = (d * a') * (q * k) := by rw [ha']
      _ = (d * q) * (a' * k) := by ring
      _ = m * (a' * k) := by rw [hq]
