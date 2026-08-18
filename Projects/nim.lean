import Mathlib

/-
We will be formalising the game of Nim, following the structure used in Imperial's
Game Theory Module. We set up the structure of positions, options and nim-sums of
the game, with the aim of proving Bouton's solution of Nim :

# Main Theorem : Bouton's Solution for Nim
A Nim position is losing if and only if the nim sum of all piles is 0
Equivalently, a nim position is winning if and only if the nim sum of all piles is not 0
-/


/-- A NimPosition represents different piles of different amounts of tokens,
here represented as a list of naturals, where each item is a pile and the
value of the elements corresponds to the quantity of tokens in that pile -/
abbrev NimPosition := List ℕ

-- ex: [1, 2] is two piles of 1 and 2 tokens

/-- In one move of the game, remove 1+ tokens from one pile. Here, given natural n
(quantity of tokens in one pile), produce a list of new possible pile sizes -/
def ReducePile (n : ℕ) : List ℕ := List.range n

-- example : given a heap of size 5, we can choose to reduce it to
-- any of the sizes given by reducePile 5 (take all tokens = 0, take 1 = 4)
example : ReducePile 5 = [0, 1, 2, 3, 4] := by rfl

/-- When we take all tokens from a pile, leaving a 0 pile,
"clean" the list of piles to remove the empty pile -/
def CleanPiles : NimPosition → NimPosition
| [] => []
| 0 :: t => CleanPiles t
| a :: t => a :: CleanPiles t

example : CleanPiles [0, 2, 3] = [2, 3] := by rfl
example : CleanPiles [0, 0] = [] := by rfl
example : CleanPiles [2, 0, 1] = [2, 1] := by rfl
example : CleanPiles [2, 5] = [2, 5] := by rfl

/-- We define options as a list of NimPositions, or positions that are reachable
in one move from our current NimPosition -/
def Options : NimPosition → List NimPosition
| [] => [] -- no heaps = no options
| p1 :: rest => -- extract first heap
    (ReducePile p1).map (fun el => CleanPiles (el :: rest))
    -- attach every element to the front of the other heaps
    ++ -- join this list with the options using the other heaps
    (Options rest).map (fun el => CleanPiles (p1 :: el))

example : Options [] = [] := by rfl
example : Options [3] = [[], [1], [2]] := by rfl
example : Options [2, 1] = [[1], [1, 1], [2]] := by rfl

/-- We keep track of the total number of tokens summed across all the piles -/
def TotalTokens : NimPosition → ℕ
| [] => 0
| a :: b => a + TotalTokens b

/-- We prove that "cleaning" the piles (removing the 0 piles) doesn't
change the total number of tokens in our game -/
lemma totalTokens_cleanPiles (p : NimPosition) :
    TotalTokens (CleanPiles p) = TotalTokens p := by
  induction p with
  | nil => rfl
  | cons a r ih =>
    cases a with
    | zero => simpa [CleanPiles, TotalTokens] using ih
    | succ n => simp [CleanPiles, TotalTokens, ih]

example : TotalTokens [2, 3, 1] = 6 := by rfl
example : TotalTokens [] = 0 := by rfl
example : TotalTokens [0] = 0 := by rfl

/-- We prove that any move in our options decreases the total number of tokens
in our game -/
lemma allMovesDecreaseTokens (p : NimPosition) :
    ∀ p', p' ∈ Options p → TotalTokens p' < TotalTokens p := by
  induction p with
  -- if p is [], Options p = [] so there is no p' in Options p,
  | nil =>
      intro p' h
      simp [Options] at h
  | cons a r ih =>
      intro p' h
      rw [Options] at h
      -- if p' ∈ l1 ++ l2, then p' ∈ l1 ∨ p' ∈ l2
      apply List.mem_append.mp at h
      -- two cases : either p' is obtained from changing the first heap, or the others
      rcases h with h_first | h_tail
      · -- unfold the map in h_first, rewrite p'
        rcases List.mem_map.mp h_first with ⟨k, hk, rfl⟩
        -- prove the move has decreased the size of the pile
        have hk' : k < a := by
          simpa [ReducePile] using (List.mem_range.mp hk)
        -- TotalTokens are the same for clean/unclean piles
        have hclean : TotalTokens (CleanPiles (k :: r)) = TotalTokens (k :: r) := by
          exact totalTokens_cleanPiles (k :: r)
        rw [hclean]
        -- show total tokens have been decreased by addition on both sides using hk'
        simpa [TotalTokens] using add_lt_add_right hk' (TotalTokens r)
      · -- if p' is obtained from changing the other heaps:
        rcases List.mem_map.mp h_tail with ⟨r', hr', rfl⟩
        -- by inductive hypothesis, obtain that the totaltokens have decreased
        have hr'' : TotalTokens r' < TotalTokens r := ih r' hr'
        have hclean : TotalTokens (CleanPiles (a :: r')) = TotalTokens (a :: r') := by
          exact totalTokens_cleanPiles (a :: r')
        rw [hclean]
        -- as in the other case, use symmetry of inequalities
        simpa [TotalTokens] using add_lt_add_left hr'' a

/-- Using allMovesDecreaseTokens, we specify that a specific move taking us to
option p' reduces the number of total tokens in our games -/
lemma moveDecreasesTokens {p p' : NimPosition} (h : p' ∈ Options p) :
    TotalTokens p' < TotalTokens p :=
  allMovesDecreaseTokens p p' h

/- We define a winning and losing position mutually, since both definitions depend on one
another. We use inductive definitions to describe these as logical properties -/
mutual
  /-- A WinningPos is one from which you can reach a LosingPos -/
  inductive WinningPos : NimPosition → Prop where
    | win : {p p' : NimPosition} → p' ∈ Options p → LosingPos p' → WinningPos p

  /-- A LosingPos is one from which all options are WinningPos -/
  inductive LosingPos : NimPosition → Prop where
    | lose : {p : NimPosition} → (∀ p' ∈ Options p, WinningPos p') → LosingPos p
end

example : LosingPos [] := by
  apply LosingPos.lose
  intro p' hp'
  simp [Options] at hp'

example : WinningPos [2] := by
  apply WinningPos.win (p' := [])
  · change [] ∈ [[], [1]] -- explicitly change goal
    simp
  · apply LosingPos.lose
    intro p' hp'
    simp [Options] at hp'

/-- Define nimSum using XOR across piles, where ^^^ acts on the bitwise/binary
representation of the elements of our given NimPosition -/
def NimSum : NimPosition → ℕ
| [] => 0
| a :: t => a ^^^ (NimSum t)

example : NimSum [1, 1] = 0 := by rfl
example : NimSum [4, 2, 3] = 5 := by rfl
example : NimSum [2, 1] = 3 := by rfl

/-- Prove that the nimSum of a position is equal to the same position with the piles "cleaned" -/
lemma nimSum_cleanPiles (p : NimPosition) :
    NimSum (CleanPiles p) = NimSum p := by
  induction p with
  | nil =>
      rfl -- CleanPiles [] = [] so rfl closes the goal
  | cons a t ih =>
      cases a with
      | zero =>
          -- if a = 0, obtain 0 xor NimSum t = NimSum t
          rw [CleanPiles, NimSum, ih]
          simp
      | succ n =>
          simp [CleanPiles, NimSum, ih]

/-- Prove right cancellation for k xor s = a xor s -/
lemma xor_right_cancel {k a s : ℕ} (h : k ^^^ s = a ^^^ s) : k = a := by
  have h1 : k ^^^ s ^^^ s = a ^^^ s ^^^ s := by rw [h]
  simp at h1
  exact h1

/-- Prove left cancellation for s xor k = s xor a -/
lemma xor_left_cancel {k a s : ℕ} (h : s ^^^ k = s ^^^ a) : k = a := by
  apply xor_right_cancel
  rw [Nat.xor_comm k s, Nat.xor_comm a s]
  exact h

/-- Prove that a move from one position to another changes the nimSum -/
lemma move_changes_nimSum {p p' : NimPosition}
    (hopt : p' ∈ Options p) : NimSum p' ≠ NimSum p := by
  -- prove by induction on p, generalizing p' to apply the ih to different p'
  induction p generalizing p' with
  | nil => simp [Options] at hopt
  -- let p = [a :: t]
  | cons a t ih =>
      rw [Options] at hopt
      apply List.mem_append.mp at hopt
      rcases hopt with h_first | h_tail
      -- case 1: first pile changes from a to k
      · rcases List.mem_map.mp h_first with ⟨k, hk, rfl⟩
        have hk' : k < a := by simpa [ReducePile] using List.mem_range.mp hk
        rw [nimSum_cleanPiles, NimSum]
        -- wts: k ^^^ nimSum t ≠ (nimSum a :: t)
        intro h -- prove by contradiction
        -- derive k = a from h
        have : k = a := by
          exact xor_right_cancel h
        linarith
      -- case 2: tail changes from t to r'
      · rcases List.mem_map.mp h_tail with ⟨r', hr', rfl⟩
        rw [nimSum_cleanPiles, NimSum]
        -- wts: a ^^^ nimSum r' ≠ (nimSum a :: t)
        -- by ih we have : nimSum r' ≠ nimSum t since r' ∈ Options t
        have ih' : NimSum r' ≠ NimSum t := ih hr'
        intro h
        -- again prove by contradiction
        apply ih'
        exact xor_left_cancel h -- left cancel a in h

/-- Deduce that from a zero nimsum position, we can move to a nonzero nimsum position -/
theorem zero_to_nonzero {p p' : NimPosition}
    (hz : NimSum p = 0) (hopt : p' ∈ Options p) : NimSum p' ≠ 0 := by
  have h := move_changes_nimSum hopt
  rw [hz] at h
  exact h

-- now we wish to prove the converse, nonzero to zero

/-- We prove that if i is the most significant bit of x, and a also has 1 at bit i,
    then a ^^^ x < a -/
lemma xor_msb
    {a x i : ℕ} (hxi : x.testBit i = true) -- bit i of x is 1
    (hmax : ∀ j, i < j → x.testBit j = false) -- no bits higher than i are 1 (leftmost)
    (hia : a.testBit i = true) : -- bit i of a is also 1
    a ^^^ x < a := by
  -- to prove a xor x < a, it suffices to find a bit position i where a xor x has a 0,
  -- a has a 1, and they agree on every bit above i
  apply Nat.lt_of_testBit
  -- Goal 1: (a ^^^ x).testBit i = false
  · rw [Nat.testBit_xor]  -- rw to xor on the bits of a and x
    rw [hxi, hia]
    rfl
  -- Goal 2: a.testBit i = true
  · exact hia
  -- Goal 3: ∀ j > i, (a ^^^ x).testBit j = a.testBit j
  · intro j hj
    rw [Nat.testBit_xor] -- rw to xor on the bits of a and x
    rw [hmax j hj]
    simp

/-- We prove that, given a nonzero nimSum nimPosition, there exists a heap a in our current position
    such that xoring it with the nimSum of our current position is less than a (required for it to
    be a "legal" move in our game) -/
lemma pivot_heap {p : NimPosition} (hnz : NimSum p ≠ 0 ) :
    ∃ a ∈ p, a ^^^ (NimSum p) < a := by
  let x := NimSum p
  -- there exists a most significant bit i of x for nonzero x
  obtain ⟨i, hi⟩ := Nat.exists_most_significant_bit hnz

  -- find a heap a in p that has bit i set to 1
  -- since x is the XOR of all heaps in p, and bit i of x is 1,
  -- an odd number of heaps must have bit i set, so at least one does
  have h_exists : ∃ a ∈ p, a.testBit i = true := by
    -- prove that there exists a heap a that has bit i = 1
    have h_ind : ∀ p : NimPosition, (NimSum p).testBit i = true →
        ∃ a ∈ p, a.testBit i = true := by
      intro p hp
      induction p with
      | nil => simp [NimSum] at hp
      | cons h t ih =>
        simp only [NimSum, Nat.testBit_xor] at hp
        -- cases : either first element has bit i = 1 or i = 0
        by_cases hh : h.testBit i = true
        · refine ⟨h, ?_, hh⟩ -- use h as witness
          simp
        · push_neg at hh
          simp at hh
          -- h is not the pivot, so true came from the tail
          simp [hh] at hp
          -- by ih, obtain witness a in the tail verifying conditions
          obtain ⟨a, ha_mem, ha_bit⟩ := ih hp
          exact ⟨a, List.mem_cons_of_mem h ha_mem, ha_bit⟩
    exact h_ind p hi.1

  obtain ⟨a, ha_mem, ha_bit⟩ := h_exists
  exact ⟨a, ha_mem, xor_msb hi.1 hi.2 ha_bit⟩


/-- Prove that there exists an option of p that yields a nimsum == nimSum p ^^^ y,
given the existence of pivot heap a -/
lemma build_option_from_pivot {p : NimPosition} {y : ℕ}
    (hpiv : ∃ a ∈ p, a ^^^ y < a) :
    ∃ p' ∈ Options p, NimSum p' = NimSum p ^^^ y := by
  induction p with
  -- trivially true if p = []
  | nil =>
      rcases hpiv with ⟨a, ha, _⟩
      simp at ha
  | cons h t ih =>
      rcases hpiv with ⟨a, ha_mem, ha_lt⟩
      -- pivot heap a is either in head or tail
      simp at ha_mem
      rcases ha_mem with hh | ht
      -- if pivot a is in the head of the list
      · subst hh
        -- replace pivot a with a ^^^ y
        refine ⟨CleanPiles ((a ^^^ y) :: t), ?_, ?_⟩
        -- prove it's an option
        · rw [Options]
          apply List.mem_append.mpr
          -- option is in the left of the append, since it's in the first heap
          left
          -- expand map
          apply List.mem_map.mpr
          refine ⟨a ^^^ y, ?_, rfl⟩
          -- use a ^^^ y < a to show it's in the options
          simpa [ReducePile] using List.mem_range.mpr ha_lt
        · -- prove the nimsum equality using commutativity of xor
          rw [nimSum_cleanPiles]
          simp [NimSum, Nat.xor_left_comm, Nat.xor_comm]
      -- if pivot heap is in the tail of the list
      · -- apply ih to the tail with the same pivot heap a
        -- yields p' option of t with nimSum p' = nimSum t ^^^ y
        rcases ih ⟨a, ht, ha_lt⟩ with ⟨p', hp', hnim⟩
        refine ⟨CleanPiles (h :: p'), ?_, ?_⟩
        -- prove it's an option, as before
        · rw [Options]
          apply List.mem_append.mpr
          right
          apply List.mem_map.mpr
          exact ⟨p', hp', rfl⟩
        -- prove the nimsum equality
        · rw [nimSum_cleanPiles]
          simp [NimSum, hnim, Nat.xor_left_comm, Nat.xor_comm]

/-- Prove that from a nonzero position, we can move to a zero position in one move -/
theorem nonzero_to_zero {p : NimPosition}
    (hnz : NimSum p ≠ 0) :
    ∃ p' ∈ Options p, NimSum p' = 0 := by
  -- get pivot heap a
  obtain ⟨a, ha_mem, ha_lt⟩ := pivot_heap hnz
  -- build option p' from the pivot heap
  have hopt := build_option_from_pivot ⟨a, ha_mem, ha_lt⟩
  -- get option p'
  obtain ⟨p', hp'mem, hp'xor⟩ := hopt
  refine ⟨p', hp'mem, ?_⟩
  -- show NimSum p' = 0
  rw [hp'xor]
  simp -- self cancel xor

/-- To finally prove Bouton's solution, we use top-down induction: assume both directions
hold for all positions with fewer tokens than p, then prove both directions for p -/
lemma nimSum_zero_losing_aux (n : ℕ) :
    ∀ p : NimPosition, TotalTokens p = n →
      ((NimSum p = 0 → LosingPos p) ∧ (NimSum p ≠ 0 → WinningPos p)) := by

  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro p hp
      constructor
      · intro psum
        -- prove p is a LosingPos
        apply LosingPos.lose
        intro p' hp'
        -- we will use ih so need to show totalTokens p' < n
        have hlt : TotalTokens p' < n := by
          rw [← hp] -- now wts totalTokens p' < totalTokens p
          exact moveDecreasesTokens hp' -- which we know by p' ∈ options p
        -- apply ih to p'
        have hreq := ih (TotalTokens p') hlt p' rfl
        exact hreq.2 (zero_to_nonzero psum hp')
      · intro psum
        -- obtain the zero nimsum position p'
        obtain ⟨p', hp'op, hp'zero⟩ := nonzero_to_zero psum
        -- again we will use ih so need to show totalTokens p' < n
        have hlt : TotalTokens p' < n := by
          rw [← hp]
          exact moveDecreasesTokens hp'op
        have hreq := ih (TotalTokens p') hlt p' rfl
        exact WinningPos.win hp'op (hreq.1 hp'zero)

/-- Prove that if the nimsum of nimposition p = 0, then it is a losing position -/
theorem nimSum_zero_losing {p : NimPosition}
    (hz : NimSum p = 0) : LosingPos p := by
  exact (nimSum_zero_losing_aux (TotalTokens p) p rfl).1 hz

/-- Prove that if the nimsum of nimposition p ≠ 0, then it is a winning position -/
theorem nimSum_nonzero_winning {p : NimPosition}
    (hnz : NimSum p ≠ 0) : WinningPos p := by
  exact (nimSum_zero_losing_aux (TotalTokens p) p rfl).2 hnz

/-- Auxiliary proving that WinningPos and LosingPos are mutually exclusive via strong induction -/
lemma not_both_aux (n : ℕ) :
    ∀ p : NimPosition, TotalTokens p = n → ¬ (WinningPos p ∧ LosingPos p) := by

  -- proof by strong induction on the number of total tokens
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro p hp ⟨hw, hl⟩ -- obtain by  ¬ a = a → False
      cases hw with
      | win hop hlose =>
          cases hl with
          | lose hallp =>
              rename_i p' -- rename implicit p'✝
              -- p' is WinningPos (by hallp) and LosingPos (by hlose)
              -- but it has strictly fewer tokens than p, contradicting ih
              have hlt : TotalTokens p' < n := by
                rw [← hp]
                exact moveDecreasesTokens hop
              -- apply ih to p' to get contradiction
              exact ih (TotalTokens p') hlt p' rfl ⟨hallp p' hop, hlose⟩

/-- Prove that WinningPos and LosingPos are mutually exclusive for a specific nimposition p -/
lemma not_both {p : NimPosition} : ¬ (WinningPos p ∧ LosingPos p) :=
  not_both_aux (TotalTokens p) p rfl

/-- Prove Bouton's Nim Solution : a nim position p is losing iff its nim sum is 0 -/
theorem losing_iff_nimSum_zero (p : NimPosition) :
    LosingPos p ↔ NimSum p = 0 := by
  constructor
  · intro hl
    by_contra hsum
    -- derive contradiction : p cannot be both winning (hsum) and losing position (hl)
    exact not_both ⟨nimSum_nonzero_winning hsum, hl⟩
  · intro hp
    exact nimSum_zero_losing hp

/-- Prove Bouton's Nim Solution : a nim position p is winning iff its nim sum is not 0 -/
theorem winning_iff_nimSum_nonzero (p : NimPosition) :
    WinningPos p ↔ NimSum p ≠ 0 := by
  constructor
  · intro hw
    by_contra hsum
    exact not_both ⟨hw, nimSum_zero_losing hsum⟩
  · exact nimSum_nonzero_winning
