import Mathlib.Tactic

/-
We will be proving the following theorem and corollary from year 2 analysis:
# Main Theorem : Intermediate Value Theorem
If `f : ℝ → ℝ` is continuous on `[a, b]`, `a ≤ b`, and `f(a) ≤ k ≤ f(b)`,
then there exists `c ∈ [a, b]` such that `f(c) = k`

# Corollary : Bolzano's Theorem
If `f : ℝ → ℝ` is continuous on `[a, b]`, `a ≤ b`, and `f(a)f(b) < 0`
then there exists `c ∈ [a, b]` such that `f(c) = 0`
-/

-- DEFINITIONS

/-- Definition of continuity of f at a point a -/
def continuous_at_point (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, |x - a| < δ → |f x - f a| < ε

/-- Definition of continuity of f on a closed interval `[a, b]`
(f is continuous at every point of the closed interval) -/
def continuous_on_int (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ k : ℝ, k ∈ Set.Icc a b → continuous_at_point f k

/-- Definition of set S which we will use in our proof of the IVT containing
all points `x ∈ [a, b]` such that `f(x) ≤ k` where k is some specified real -/
def set_s (f : ℝ → ℝ) (a b k : ℝ) : Set ℝ :=
  {x ∈ Set.Icc a b | f x ≤ k}

-- LEMMAS

/-- Prove that the set S we defined `S = {x ∈ Set.Icc a b | f x ≤ k}` is bounded above -/
lemma set_s_upper_bound
  (f : ℝ → ℝ) (a b k : ℝ) :
  BddAbove (set_s f a b k) := by
  -- use b as our upper bound of S
  refine ⟨b, ?_⟩

  -- prove b is an upper bound of S : any x ∈ S is in `[a,b]` by definition
  intro x hx
  exact hx.1.2

/-- Prove that the set S is non-empty -/
lemma s_non_empty
  (f : ℝ → ℝ) (a b k : ℝ) (hab : a ≤ b) (hfa : f a ≤ k): (set_s f a b k).Nonempty := by
  -- by definition, a ∈ S
  exact ⟨a, ⟨⟨le_refl a, hab⟩, hfa⟩⟩

/-- Prove that the supremum of S is in `[a, b]` -/
lemma sup_s_ab
  (f : ℝ → ℝ) (a b k : ℝ) (hfa : f a ≤ k) (hab : a ≤ b):
  sSup (set_s f a b k) ∈ Set.Icc a b := by
  constructor
  -- prove a ≤ sup S
  · apply le_csSup (set_s_upper_bound f a b k)
    exact ⟨⟨le_refl a, hab⟩, hfa⟩
  -- prove sup S ≤ b : using that sup S ≤ any upper bound of S
  · apply csSup_le (s_non_empty f a b k hab hfa)
  -- every element in S is ≤ b by definition so b is an upper bound
    intro x hx
    exact hx.1.2

/-- Prove if f is continuous at point a, so is -f at a-/
lemma continuous_at_point_neg (f : ℝ → ℝ) (a : ℝ) :
  continuous_at_point f a → continuous_at_point (-f) a := by
  intro h ε he
  obtain ⟨δ, hpos, hdel⟩ := h ε he
  refine ⟨δ, hpos, ?_⟩
  intro x hx
  -- goal: |-f(x) - -f(a)| < ε
  --     = |f(a) - f(x)| = |f(x) - f(a)|
  calc |(-f) x - (-f) a| = |-f x + f a| := by simp
    _ = |f a - f x| := by ring_nf
    _ = |f x - f a| := by simp[abs_sub_comm]
    _ < ε := hdel x hx

/-- Prove if f is continuous on interval `[a, b]`, so is -f -/
lemma continuous_on_int_neg (f : ℝ → ℝ) (a b : ℝ) :
  continuous_on_int f a b → continuous_on_int (-f) a b := by
  intro h k hk
  exact continuous_at_point_neg f k (h k hk)

-- THEOREMS

/-- Proof of the Intermediate Value Theorem : If `f : ℝ → ℝ` is continuous on `[a, b]`,
`a ≤ b`, and `f(a) ≤ k ≤ f(b)`, then there exists `c ∈ [a, b]` such that `f(c) = k`-/
theorem intermediate_value_theorem
  (f : ℝ → ℝ) (a b k : ℝ) (hab : a ≤ b) (hfa : f a ≤ k) (hfb : k ≤ f b)
  (hcont : continuous_on_int f a b):
  ∃ c : ℝ, a ≤ c ∧ c ≤ b ∧ f c = k := by

  -- denote sup S = c, which we use as our witness
  let c := sSup (set_s f a b k)
  refine ⟨c, ?_, ?_, ?_⟩

  -- using our lemma, we know a ≤ sup S ≤ b
  · exact (sup_s_ab f a b k hfa hab).1
  · exact (sup_s_ab f a b k hfa hab).2
  · -- now we prove f(c) = k by showing k ≤ f(c) ≤ k
    have hfc : continuous_at_point f c := hcont c (sup_s_ab f a b k hfa hab)
    -- begin by proving f(c) ≤ k
    have hle : f c ≤ k := by
      -- by contradiction : suppose f(c) > k
      by_contra hgk
      push_neg at hgk
      -- choose ε = f(c) - k > 0 and apply it to obtain δ
      set ε := f c - k
      have he : ε > 0 := by grind
      obtain ⟨δ, hpos, hdel⟩ := hfc ε he
      -- show c - δ/2 is an upper bound of S
      have h4 : ∀ x ∈ (set_s f a b k), x ≤ c - δ/2 := by
        intro x hx
        have hxc : x ≤ c := le_csSup (set_s_upper_bound f a b k) hx
        -- again by contradiction, suppose x > c - δ/2
        by_contra hxx
        push_neg at hxx
        have habs : |x - c| < δ := by
          rw [abs_lt]
          constructor
          · linarith -- uses hxx : -δ < -δ / 2 < x - c since δ > 0
          · linarith -- uses hxc : x - c ≤ 0 < δ
        have hded := hdel x habs -- apply continuity
        rw [abs_lt] at hded
        -- at this point hded.1 yields - f(c) + k < f(x) - f(c) ↔ k < f(x),
        -- so with linarith we contradict hx.2, by which x ∈ S so f(x) ≤ k by definition
        linarith [hded.1, hx.2]
      -- so c - δ/2 is an upper bound for S, but c - δ/2 < c = since δ > 0
      -- thus arriving at a contradiction because sup S = c and we have found a lower
      -- upper bound
      have hc : c ≤ c - δ/2 := csSup_le (s_non_empty f a b k hab hfa) h4
      linarith
    -- now prove f(c) ≥ k
    have hge : f c ≥ k := by
      -- again by contradiction, suppose f(c) < k
      by_contra hge
      push_neg at hge
      -- because c ≤ b, split into 2 cases: c = b or c < b
      have hcb : c = b ∨ c < b := eq_or_lt_of_le (sup_s_ab f a b k hfa hab).2
      rcases hcb with hcb1 | hcb2
      -- if c = b, direct contradiction of hfb from f(b) < k
      · rw [hcb1] at hge
        linarith
      -- if c < b
      · set ε := k - f c
        have he : ε > 0 := by grind
        obtain ⟨δ, hpos, hdel⟩ := hfc ε he
        -- because we add, we ensure c + δ'/2 stays within `[a,b]` by taking the min
        -- of δ or the midpoint between c and b
        set δ' := min δ (b - c)
        -- an element x less than a and b is less than its min, hence 0 < min δ (b - c)
        have hpos' : δ' > 0 := by
          apply lt_min hpos
          linarith
        -- set c + δ'/2 as x, and to use the continuity argument, begin by showing |x - c| < δ
        have habs : |c + (δ' / 2) - c| < δ := by
          rw [abs_lt]
          constructor
          · linarith
          · have hmin : δ' ≤ δ := min_le_left δ (b - c)
            linarith
        -- deduce that |f(c + (δ' / 2)) - f(c)| < ε = k - f(c)
        have hded := hdel (c + (δ' / 2)) habs
        rw [abs_lt] at hded
        -- now we show c + (δ' / 2) ∈ S
        have hfk : f (c + (δ' / 2)) < k := by linarith
        have hs : (c + (δ' / 2)) ∈ set_s f a b k := by
          have hs1 : (c + (δ' / 2)) ∈ Set.Icc a b := by
            constructor
            -- a ≤ c, hence a ≤ c + (δ' / 2) since δ' > 0
            · linarith [(sup_s_ab f a b k hfa hab).1]
            -- by min reasoning, δ' ≤ b - c, hence c + (δ' / 2) ≤ c + δ' ≤ b since δ' > 0
            · linarith [min_le_right δ (b - c)]
          exact ⟨hs1, le_of_lt hfk⟩
        have hc : c + (δ' / 2) > c := by linarith
        have hfin : c + (δ' / 2) ≤ c := le_csSup (set_s_upper_bound f a b k) hs
        -- contradiction : c + (δ' / 2) > c yet by supremum we must have c + (δ' / 2) ≤ c
        linarith
    exact le_antisymm hle hge

-- We now use the IVT to prove Bolzano's Theorem

/-- Proof of Bolzano's Theorem : If `f : ℝ → ℝ` is continuous on `[a, b]`, `a ≤ b`,
and `f(a)f(b) < 0` then there exists `c ∈ [a, b]` such that `f(c) = 0` -/
theorem bolzano
  (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
  (hcont : continuous_on_int f a b) (h : f a * f b < 0) :
  ∃ c : ℝ, a ≤ c ∧ c ≤ b ∧ f c = 0 := by

  -- from f(a)f(b) < 0, deduce two possible cases:
  have h1 : (0 < f b ∧ f a < 0) ∨ (0 < f a ∧ f b < 0) := by
    simpa [and_comm, or_comm] using (mul_neg_iff.mp h)

  rcases h1 with ⟨hfb, hfa⟩ | ⟨hfa, hfb⟩
  · -- case 1: f(a) < 0 < f(b) - apply IVT with k = 0
    exact intermediate_value_theorem f a b 0 hab (le_of_lt hfa) (le_of_lt hfb) hcont

  · -- case 2: f(b) < 0 < f(a) - apply IVT to -f with k = 0
    have hcont' : continuous_on_int (-f) a b := continuous_on_int_neg f a b hcont
    have h2 : (-f a) ≤ 0 := by linarith
    have h3 : 0 ≤ (-f b) := by linarith
    obtain ⟨c, hac, hcb, hc⟩ :=
      intermediate_value_theorem (fun x => - f x) a b 0 hab h2 h3 hcont'
    refine ⟨c, hac, hcb, ?_⟩
    -- from hc : -f(c) = 0, conclude f(c) = 0
    linarith

-- indent
-- docstring no "prove"
-- by_contra!
