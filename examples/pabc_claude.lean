/-
Proving lemmas and theorems from Morph Lab's recent autoformalization for De Brujin's theorem 
Using Claude Desktop, LeanTool and LeanExplore
-/
import Mathlib

lemma two_rpow_ge_add_one (x : ℝ) (hx : x ≥ 1) : 2 ^ x ≥ x + 1 := by
  -- Apply Bernoulli's inequality: 1 + p * s ≤ (1 + s) ^ p with s = 1, p = x
  have h : 1 + x * 1 ≤ (1 + 1) ^ x := 
    one_add_mul_self_le_rpow_one_add (by norm_num : (-1 : ℝ) ≤ 1) hx
  -- Simplify and rearrange
  simp only [mul_one] at h
  have : (1 + 1 : ℝ) ^ x = 2 ^ x := by norm_num
  rw [this] at h
  rwa [add_comm]



theorem two_rpow_ge_half_add_one (x : ℝ) (hx : x ≥ 0) : 2 ^ x ≥ x / 2 + 1 := by
  -- Use 2^x = exp(x * log 2) and exp(y) ≥ y + 1
  have h_two_pos : (0 : ℝ) < 2 := by norm_num
  rw [Real.rpow_def_of_pos h_two_pos]
  rw [mul_comm (Real.log 2) x]
  -- Now we have 2^x = exp(x * log 2)
  -- We need to show exp(x * log 2) ≥ x / 2 + 1
  have h_exp_bound : x * Real.log 2 + 1 ≤ Real.exp (x * Real.log 2) := Real.add_one_le_exp (x * Real.log 2)
  -- So it suffices to show x / 2 + 1 ≤ x * log 2 + 1
  suffices h : x / 2 + 1 ≤ x * Real.log 2 + 1 by linarith [h, h_exp_bound]
  -- This is equivalent to x / 2 ≤ x * log 2
  have h_key : x / 2 ≤ x * Real.log 2 := by
    -- We need to prove that log 2 ≥ 1/2 first
    have h_log_bound : (1 : ℝ) / 2 ≤ Real.log 2 := by
      -- Use the known bound log 2 > 0.6931471803
      have h_bound : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      -- And 1/2 = 0.5 < 0.6931471803
      have h_half : (1 : ℝ) / 2 = 0.5 := by norm_num
      rw [h_half]
      -- So 0.5 < 0.6931471803 < log 2
      have h_ineq : (0.5 : ℝ) < 0.6931471803 := by norm_num
      linarith [h_ineq, h_bound]
    -- Now case split on x
    cases' eq_or_lt_of_le hx with h_zero h_pos
    · -- Case x = 0
      rw [← h_zero]
      simp
    · -- Case x > 0
      -- Multiply both sides of 1/2 ≤ log 2 by x
      have h_mul : x * ((1 : ℝ) / 2) ≤ x * Real.log 2 := 
        mul_le_mul_of_nonneg_left h_log_bound (le_of_lt h_pos)
      -- Show that x * (1/2) = x / 2
      have h_eq : x * ((1 : ℝ) / 2) = x / 2 := by
        rw [mul_div_assoc', mul_one]
      rw [h_eq] at h_mul
      exact h_mul
  linarith [h_key]


theorem fundamental_theorem_of_arithmetic : UniqueFactorizationMonoid ℕ := by
  infer_instance

-- Definition [Divisor function]
def tau (n : ℕ) : ℕ := n.divisors.card

lemma tau_eq_prod_factorization_add_one (n : ℕ) (hn : n ≠ 0) : 
  tau n = n.primeFactors.prod (λ p => n.factorization p + 1) := by
  unfold tau
  rw [Nat.card_divisors hn]


lemma tau_n_div_n_rpow_eps_eq_prod (n : ℕ) (hn : n ≠ 0) (ε : ℝ) : 
  (tau n : ℝ) / ((n : ℝ) ^ ε) = n.primeFactors.prod (fun p => (((n.factorization p) + 1 : ℝ) / ((p : ℝ) ^ ((n.factorization p : ℝ) * ε)))) := by
  -- First, let's use the factorization of tau
  rw [tau_eq_prod_factorization_add_one n hn]
  
  -- Cast the product to reals
  simp_rw [Nat.cast_prod]
  
  -- Now we need to express n as a product of prime powers
  have h_n_eq : (n : ℝ) = n.primeFactors.prod (fun p => (p : ℝ) ^ (n.factorization p : ℕ)) := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rw [← Nat.prod_factorization_eq_prod_primeFactors]
    simp only [Finsupp.prod, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    rw [← Nat.cast_pow]
  
  -- Rewrite n^ε using the prime factorization
  rw [h_n_eq]
  
  -- Apply Real.finset_prod_rpow
  have h_pos : ∀ p ∈ n.primeFactors, (0 : ℝ) ≤ (p : ℝ) ^ (n.factorization p : ℕ) := by
    intro p hp
    apply pow_nonneg
    exact Nat.cast_nonneg _
  
  rw [← Real.finset_prod_rpow _ _ h_pos ε]
  
  -- Now simplify the products
  simp_rw [← Real.rpow_natCast_mul (Nat.cast_nonneg _)]
  
  -- Use prod_div_distrib to combine the division
  rw [← Finset.prod_div_distrib]
  
  -- Show the terms are equal
  apply Finset.prod_congr rfl
  intro p hp
  simp only [Nat.cast_add, Nat.cast_one]



lemma lemma7 (p a : ℕ) (ε : ℝ) (hp : p ≥ 2) (ha : a ≥ 1) (hε : ε > 0) (hε_small : ε < 1/100)  (h_cond : (p : ℝ) ^ ε ≥ 2) : (a + 1 : ℝ) / ((p : ℝ) ^ ((a : ℝ) * ε)) ≤ (a + 1 : ℝ) / ((2 : ℝ) ^ (a : ℝ)) ∧ (a + 1 : ℝ) / ((2 : ℝ) ^ (a : ℝ)) ≤ 1 := by
  constructor
  · -- First part: (a + 1) / (p^(a*ε)) ≤ (a + 1) / (2^a)
    -- Since the numerators are the same, we need to show that the first denominator is larger
    apply div_le_div_of_nonneg_left
    · -- Show (a + 1 : ℝ) ≥ 0
      exact add_nonneg (Nat.cast_nonneg a) zero_le_one
    · -- Show 2^a > 0
      exact Real.rpow_pos_of_pos (by norm_num) (a : ℝ)
    · -- Show 2^a ≤ p^(a*ε)
      -- Use Real.rpow_mul to rewrite p^(a*ε) = (p^ε)^a
      have h1 : (p : ℝ) ^ ((a : ℝ) * ε) = ((p : ℝ) ^ ε) ^ (a : ℝ) := by
        rw [mul_comm (a : ℝ) ε]
        rw [← Real.rpow_mul (Nat.cast_nonneg p)]
      rw [h1]
      -- Now use monotonicity of rpow with h_cond: p^ε ≥ 2
      apply Real.rpow_le_rpow
      · norm_num  -- 0 ≤ 2
      · exact h_cond  -- 2 ≤ p^ε
      · exact Nat.cast_nonneg a  -- 0 ≤ a
  · -- Second part: (a + 1) / (2^a) ≤ 1
    -- This follows from two_rpow_ge_add_one and div_le_one
    have h1 : (a : ℝ) ≥ 1 := Nat.one_le_cast.mpr ha
    have h2 : 2 ^ (a : ℝ) ≥ (a : ℝ) + 1 := two_rpow_ge_add_one (a : ℝ) h1
    have h3 : (a : ℝ) + 1 = (a + 1 : ℝ) := by simp only [Nat.cast_add, Nat.cast_one]
    rw [← h3] at h2
    have h4 : (0 : ℝ) < 2 ^ (a : ℝ) := Real.rpow_pos_of_pos (by norm_num) (a : ℝ)
    rwa [div_le_one h4]

lemma lemma8 (p a : ℕ) (ε : ℝ) (hp : p ≥ 2) (ha : a ≥ 1) (hε : ε > 0) (hε_small : ε < 1/100)  (hpε : (p : ℝ) ^ ε < 2) : (a + 1 : ℝ) / ((p : ℝ) ^ ((a : ℝ) * ε)) ≤ 2 / ε := by
  -- Since p ≥ 2, we have p^(a*ε) ≥ 2^(a*ε)
  have hp_ge_two : (2 : ℝ) ≤ p := by simp [hp]
  have haε_nonneg : 0 ≤ (a : ℝ) * ε := by
    apply mul_nonneg
    · simp [ha]
    · linarith [hε]
  have h_pow_mono : (2 : ℝ) ^ ((a : ℝ) * ε) ≤ (p : ℝ) ^ ((a : ℝ) * ε) := by
    apply Real.rpow_le_rpow
    · norm_num
    · exact hp_ge_two
    · exact haε_nonneg
  
  -- Therefore 1/p^(a*ε) ≤ 1/2^(a*ε)
  have h_2_pos : 0 < (2 : ℝ) ^ ((a : ℝ) * ε) := by
    apply Real.rpow_pos_of_pos
    norm_num
  have h_inv_mono : ((p : ℝ) ^ ((a : ℝ) * ε))⁻¹ ≤ ((2 : ℝ) ^ ((a : ℝ) * ε))⁻¹ := by
    apply inv_anti₀ h_2_pos h_pow_mono
  
  -- So it suffices to show (a + 1) / 2^(a*ε) ≤ 2 / ε
  calc (a + 1 : ℝ) / ((p : ℝ) ^ ((a : ℝ) * ε)) 
      = (a + 1 : ℝ) * ((p : ℝ) ^ ((a : ℝ) * ε))⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ (a + 1 : ℝ) * ((2 : ℝ) ^ ((a : ℝ) * ε))⁻¹ := by
        apply mul_le_mul_of_nonneg_left h_inv_mono
        linarith [ha]
    _ = (a + 1 : ℝ) / ((2 : ℝ) ^ ((a : ℝ) * ε)) := by rw [div_eq_mul_inv]
    _ ≤ 2 / ε := by
        -- Now we use the theorem two_rpow_ge_half_add_one with x = a * ε
        rw [div_le_div_iff₀ h_2_pos hε]
        -- We need to show (a + 1) * ε ≤ 2 * 2^(a*ε)
        -- Since 2^(a*ε) ≥ (a*ε)/2 + 1, we have 2 * 2^(a*ε) ≥ a*ε + 2
        have h_two_rpow : 2 ^ (a * ε) ≥ (a * ε) / 2 + 1 := two_rpow_ge_half_add_one (a * ε) haε_nonneg
        have h_mul_two : 2 * (2 ^ (a * ε)) ≥ 2 * ((a * ε) / 2 + 1) := by
          apply mul_le_mul_of_nonneg_left h_two_rpow
          norm_num
        have h_simplify : 2 * ((a * ε) / 2 + 1) = a * ε + 2 := by ring
        rw [h_simplify] at h_mul_two
        -- It suffices to show (a + 1) * ε ≤ a * ε + 2
        apply le_trans _ h_mul_two
        -- This simplifies to ε ≤ 2
        have h_expand : (a + 1 : ℝ) * ε = a * ε + ε := by ring
        rw [h_expand]
        have h_eps_bound : ε ≤ 2 := by linarith [hε_small]
        linarith

lemma lemma9 (s : Finset ℕ) (a : ℕ → ℕ) (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  (hs_prime : ∀ p ∈ s, p.Prime) (ha_ge_one : ∀ p ∈ s, a p ≥ 1) :
  (∏ p ∈ s, ((a p + 1 : ℝ) / ((p : ℝ) ^ ((a p : ℝ) * ε)))) =
  (∏ p ∈ s.filter (fun (p : ℕ) => (p : ℝ) ^ ε ≥ 2), ((a p + 1 : ℝ) / ((p : ℝ) ^ ((a p : ℝ) * ε)))) *
  (∏ p ∈ s.filter (fun (p : ℕ) => (p : ℝ) ^ ε < 2), ((a p + 1 : ℝ) / ((p : ℝ) ^ ((a p : ℝ) * ε)))) := by
  -- Use the theorem that splits a product based on a predicate
  rw [← Finset.prod_filter_mul_prod_filter_not s (fun p => (p : ℝ) ^ ε ≥ 2)]
  
  -- Show that filter with ¬(p^ε ≥ 2) is the same as filter with p^ε < 2
  congr 2
  ext p
  simp only [Finset.mem_filter, not_le]

lemma lemma10 (s : Finset ℕ) (a : ℕ → ℕ) (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  (hs_prime : ∀ p ∈ s, p.Prime) (ha_ge_one : ∀ p ∈ s, a p ≥ 1) : ∏ p ∈ s.filter (fun (p : ℕ) => (p : ℝ) ^ ε ≥ 2), ((a p + 1 : ℝ) / ((p : ℝ) ^ ((a p : ℝ) * ε))) ≤ 1 := by
  -- Apply Finset.prod_le_one
  apply Finset.prod_le_one
  · -- Show each term is non-negative
    intro p hp
    simp only [Finset.mem_filter] at hp
    have hp_in_s : p ∈ s := hp.1
    -- (a p + 1) is positive, p^(a p * ε) is positive, so the quotient is positive
    apply div_nonneg
    · -- (a p + 1 : ℝ) ≥ 0
      exact add_nonneg (Nat.cast_nonneg (a p)) zero_le_one
    · -- (p : ℝ) ^ ((a p : ℝ) * ε) ≥ 0
      apply Real.rpow_nonneg
      exact Nat.cast_nonneg p
  · -- Show each term is ≤ 1
    intro p hp
    simp only [Finset.mem_filter] at hp
    have hp_in_s : p ∈ s := hp.1
    have hp_cond : (p : ℝ) ^ ε ≥ 2 := hp.2
    -- Apply lemma7
    have h_prime : p.Prime := hs_prime p hp_in_s
    have hp_ge_2 : p ≥ 2 := Nat.Prime.two_le h_prime
    have ha_p : a p ≥ 1 := ha_ge_one p hp_in_s
    have h_bound := lemma7 p (a p) ε hp_ge_2 ha_p hε hε_small hp_cond
    -- Use transitivity: (a p + 1) / p^(a p * ε) ≤ (a p + 1) / 2^(a p) ≤ 1
    exact le_trans h_bound.1 h_bound.2


lemma lemma11 (s : Finset ℕ) (a : ℕ → ℕ) (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  (hs_prime : ∀ p ∈ s, p.Prime) (ha_ge_one : ∀ p ∈ s, a p ≥ 1) :
  (∏ p ∈ s.filter (fun (p : ℕ) => (p : ℝ) ^ ε < 2), ((a p + 1 : ℝ) / ((p : ℝ) ^ ((a p : ℝ) * ε)))) ≤
  (∏ p ∈ s.filter (fun (p : ℕ) => (p : ℝ) ^ ε < 2), (2 / ε : ℝ)) := by
  -- Apply Finset.prod_le_prod
  apply Finset.prod_le_prod
  · -- Show each term is non-negative
    intro p hp
    simp only [Finset.mem_filter] at hp
    have hp_in_s : p ∈ s := hp.1
    -- (a p + 1) is positive, p^(a p * ε) is positive, so the quotient is positive
    apply div_nonneg
    · -- (a p + 1 : ℝ) ≥ 0
      exact add_nonneg (Nat.cast_nonneg (a p)) zero_le_one
    · -- (p : ℝ) ^ ((a p : ℝ) * ε) ≥ 0
      apply Real.rpow_nonneg
      exact Nat.cast_nonneg p
  · -- Show each term is bounded by 2/ε
    intro p hp
    simp only [Finset.mem_filter] at hp
    have hp_in_s : p ∈ s := hp.1
    have hp_cond : (p : ℝ) ^ ε < 2 := hp.2
    -- Apply lemma8
    have h_prime : p.Prime := hs_prime p hp_in_s
    have hp_ge_2 : p ≥ 2 := Nat.Prime.two_le h_prime
    have ha_p : a p ≥ 1 := ha_ge_one p hp_in_s
    exact lemma8 p (a p) ε hp_ge_2 ha_p hε hε_small hp_cond

lemma card_Icc_eq_sub_add_one (m M : ℕ) (h_le : m ≤ M) :
    (Finset.Icc m M).card = M - m + 1 := by
  -- Use the existing theorem Nat.card_Icc
  rw [Nat.card_Icc]
  -- Now we need to show M + 1 - m = M - m + 1
  -- First use commutativity: M + 1 = 1 + M
  rw [Nat.add_comm M 1]
  -- Now we have 1 + M - m = M - m + 1
  -- Apply Nat.add_sub_assoc: 1 + M - m = 1 + (M - m)
  rw [Nat.add_sub_assoc h_le]
  -- Now we have 1 + (M - m) = M - m + 1
  -- Use commutativity of addition
  rw [Nat.add_comm]


lemma card_le_max_sub_min_add_one (S : Finset ℕ) (hS_nonempty : S.Nonempty) :
    S.card ≤ S.max' hS_nonempty - S.min' hS_nonempty + 1 := by
  -- Show that S ⊆ Icc (S.min' hS_nonempty) (S.max' hS_nonempty)
  have h_subset : S ⊆ Finset.Icc (S.min' hS_nonempty) (S.max' hS_nonempty) := by
    intro x hx
    rw [Finset.mem_Icc]
    constructor
    · exact Finset.min'_le S x hx
    · exact Finset.le_max' S x hx
  
  -- Use card_le_card to get S.card ≤ (Icc ...).card
  have h_card_le : S.card ≤ (Finset.Icc (S.min' hS_nonempty) (S.max' hS_nonempty)).card := 
    Finset.card_le_card h_subset
  
  -- Apply card_Icc_eq_sub_add_one
  rw [card_Icc_eq_sub_add_one] at h_card_le
  exact h_card_le
  
  -- Need to show S.min' hS_nonempty ≤ S.max' hS_nonempty
  exact Finset.min'_le S (S.max' hS_nonempty) (Finset.max'_mem S hS_nonempty)



lemma finset_card_le_of_all_lt (S : Finset ℕ) (X : ℝ) (x_pos : X > 0) (s_pos : ∀ s, s ∈ S → s > 0 ) (hn : ∀ n ∈ S, (n : ℝ) < X) : S.card ≤ X := by
  -- Since all elements of S are positive natural numbers < X, they are all ≤ ⌊X⌋₊
  -- So S.card ≤ ⌊X⌋₊ ≤ X
  
  -- First, show every element of S is ≤ ⌊X⌋₊
  have h_bound : ∀ n ∈ S, n ≤ ⌊X⌋₊ := by
    intro n hn_in_S
    have hn_lt_X : (n : ℝ) < X := hn n hn_in_S
    have hn_pos : n ≠ 0 := ne_of_gt (s_pos n hn_in_S)
    -- Use the contrapositive: if n > ⌊X⌋₊, then n > X
    by_contra h_not_le
    push_neg at h_not_le
    -- So n > ⌊X⌋₊, which means ⌊X⌋₊ < n
    have h_floor_lt_n : ⌊X⌋₊ < n := h_not_le
    -- By Nat.floor_lt', this means X < n
    rw [Nat.floor_lt' hn_pos] at h_floor_lt_n
    -- But we have n < X, contradiction
    linarith [h_floor_lt_n, hn_lt_X]
  
  -- Now we need to count how many positive natural numbers are ≤ ⌊X⌋₊
  -- They are {1, 2, ..., ⌊X⌋₊}, so there are ⌊X⌋₊ of them
  -- Since S consists of positive natural numbers ≤ ⌊X⌋₊, we have S.card ≤ ⌊X⌋₊
  
  -- More precisely, S ⊆ {1, 2, ..., ⌊X⌋₊} = (range (⌊X⌋₊ + 1)) \ {0}
  have h_subset : S ⊆ Finset.range (⌊X⌋₊ + 1) := by
    intro n hn_in_S
    rw [Finset.mem_range]
    exact Nat.lt_succ_iff.mpr (h_bound n hn_in_S)
  
  -- But we need to exclude 0 since all elements of S are positive
  have h_pos_subset : S ⊆ (Finset.range (⌊X⌋₊ + 1)) \ {0} := by
    intro n hn_in_S
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨h_subset hn_in_S, ne_of_gt (s_pos n hn_in_S)⟩
  
  -- The cardinality of {1, 2, ..., ⌊X⌋₊} is ⌊X⌋₊
  have h_card_bound : ((Finset.range (⌊X⌋₊ + 1)) \ {0}).card = ⌊X⌋₊ := by
    rw [Finset.card_sdiff, Finset.card_range, Finset.card_singleton]
    · rw [add_tsub_cancel_right]
    · rw [Finset.singleton_subset_iff, Finset.mem_range]
      exact Nat.zero_lt_succ ⌊X⌋₊
  
  -- Therefore S.card ≤ ⌊X⌋₊
  have h_card_le_floor : S.card ≤ ⌊X⌋₊ := by
    rw [← h_card_bound]
    exact Finset.card_le_card h_pos_subset
  
  -- Finally, ⌊X⌋₊ ≤ X
  have h_floor_le_X : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (le_of_lt x_pos)
  
  -- Combine: S.card ≤ ⌊X⌋₊ ≤ X
  exact le_trans (Nat.cast_le.mpr h_card_le_floor) h_floor_le_X


lemma lemma12 (s : Finset ℕ) (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100) (hs_prime : ∀ p ∈ s, p.Prime) :
  (2 / ε : ℝ) ^ ((s.filter (fun (p : ℕ) => (((↑p) : ℝ) ^ ε < (2 : ℝ)))).card : ℝ) ≤ (2 / ε : ℝ) ^ (2 : ℝ) ^ (1 / ε) := by
  -- It suffices to show that the cardinality is at most 2^(1/ε)
  have h_base_gt_one : 1 < 2 / ε := by
    rw [one_lt_div hε]
    linarith [hε_small]
  
  rw [Real.rpow_le_rpow_left_iff h_base_gt_one]
  
  -- Need to show: card(filter) ≤ 2^(1/ε)
  -- First, let's understand what the filter is selecting
  -- p^ε < 2 is equivalent to p < 2^(1/ε) (taking 1/ε power of both sides)
  have h_filter_bound : ∀ p ∈ s.filter (fun (p : ℕ) => (((↑p) : ℝ) ^ ε < (2 : ℝ))), (p : ℝ) < (2 : ℝ) ^ (1 / ε) := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    have hp_in_s : p ∈ s := hp.1
    have hp_cond : (p : ℝ) ^ ε < 2 := hp.2
    -- Since p is prime, p ≥ 2, so p > 0
    have h_prime : p.Prime := hs_prime p hp_in_s
    have hp_pos : 0 < (p : ℝ) := by simp [Nat.Prime.pos h_prime]
    have hp_nonneg : 0 ≤ (p : ℝ) := le_of_lt hp_pos
    -- We have p = p^1 = p^(ε * (1/ε)) = (p^ε)^(1/ε)
    have h_inv : ε * (1 / ε) = 1 := by field_simp [ne_of_gt hε]
    conv_lhs => rw [← Real.rpow_one (p : ℝ), ← h_inv, Real.rpow_mul hp_nonneg]
    -- Now apply rpow_lt_rpow to both sides
    have h_mono : (p : ℝ) ^ ε < 2 → ((p : ℝ) ^ ε) ^ (1 / ε) < 2 ^ (1 / ε) := by
      intro h
      apply Real.rpow_lt_rpow
      · apply Real.rpow_nonneg hp_nonneg
      · exact h
      · exact div_pos one_pos hε
    exact h_mono hp_cond
  
  -- Now use finset_card_le_of_all_lt
  have h_X_pos : 0 < (2 : ℝ) ^ (1 / ε) := Real.rpow_pos_of_pos two_pos _
  have h_all_pos : ∀ p ∈ s.filter (fun (p : ℕ) => (((↑p) : ℝ) ^ ε < (2 : ℝ))), p > 0 := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    have hp_in_s : p ∈ s := hp.1
    have h_prime : p.Prime := hs_prime p hp_in_s
    exact Nat.Prime.pos h_prime
  
  exact finset_card_le_of_all_lt _ _ h_X_pos h_all_pos h_filter_bound


lemma lemma13 (n : ℕ) (ε : ℝ) (hn : n ≥ 1) (hε : ε > 0) (hε_small : ε < 1/100) : 
  (tau n : ℝ) / ((n : ℝ) ^ ε) ≤ (2 / ε : ℝ) ^ ((2 : ℝ) ^ (1 / ε)) := by
  -- First handle the case n = 0 (which is excluded by hn ≥ 1)
  have hn_pos : n ≠ 0 := by linarith
  
  -- Express tau(n)/n^ε as a product using the factorization
  rw [tau_n_div_n_rpow_eps_eq_prod n hn_pos ε]
  
  -- Apply lemma9 to split the product
  have h_split := lemma9 n.primeFactors n.factorization ε hε hε_small 
    (fun p hp => Nat.prime_of_mem_primeFactors hp)
    (fun p hp => by
      have : n.factorization p ≠ 0 := by
        rw [← Nat.support_factorization] at hp
        exact Finsupp.mem_support_iff.mp hp
      exact Nat.one_le_iff_ne_zero.mpr this)
  
  rw [h_split]
  
  -- Now we have a product of two parts
  -- The first part (p^ε ≥ 2) is bounded by 1 using lemma10
  have h_first_bound := lemma10 n.primeFactors n.factorization ε hε hε_small
    (fun p hp => Nat.prime_of_mem_primeFactors hp)
    (fun p hp => by
      have : n.factorization p ≠ 0 := by
        rw [← Nat.support_factorization] at hp
        exact Finsupp.mem_support_iff.mp hp
      exact Nat.one_le_iff_ne_zero.mpr this)
  
  -- The second part (p^ε < 2) is bounded using lemma11
  have h_second_bound := lemma11 n.primeFactors n.factorization ε hε hε_small
    (fun p hp => Nat.prime_of_mem_primeFactors hp)
    (fun p hp => by
      have : n.factorization p ≠ 0 := by
        rw [← Nat.support_factorization] at hp
        exact Finsupp.mem_support_iff.mp hp
      exact Nat.one_le_iff_ne_zero.mpr this)
  
  -- Now apply lemma12
  have h_final := lemma12 n.primeFactors ε hε hε_small 
    (fun p hp => Nat.prime_of_mem_primeFactors hp)
  
  -- Transform the second bound to use prod_const
  have h_second_eq : (∏ p ∈ n.primeFactors.filter (fun (p : ℕ) => (p : ℝ) ^ ε < 2), (2 / ε : ℝ)) = 
                     (2 / ε : ℝ) ^ (n.primeFactors.filter (fun (p : ℕ) => (p : ℝ) ^ ε < 2)).card := by
    rw [Finset.prod_const]
  
  -- Since the first part ≤ 1 and the second part ≤ (2/ε)^card, their product is ≤ (2/ε)^card
  calc (∏ p ∈ n.primeFactors.filter (fun (p : ℕ) => (p : ℝ) ^ ε ≥ 2), ((n.factorization p + 1 : ℝ) / ((p : ℝ) ^ ((n.factorization p : ℝ) * ε)))) *
       (∏ p ∈ n.primeFactors.filter (fun (p : ℕ) => (p : ℝ) ^ ε < 2), ((n.factorization p + 1 : ℝ) / ((p : ℝ) ^ ((n.factorization p : ℝ) * ε)))) 
    ≤ 1 * (∏ p ∈ n.primeFactors.filter (fun (p : ℕ) => (p : ℝ) ^ ε < 2), (2 / ε : ℝ)) := by
        apply mul_le_mul h_first_bound h_second_bound
        · apply Finset.prod_nonneg
          intro p hp
          apply div_nonneg
          · simp only [add_nonneg, Nat.cast_nonneg, zero_le_one]
          · apply Real.rpow_nonneg
            exact Nat.cast_nonneg p
        · exact zero_le_one
    _ = (∏ p ∈ n.primeFactors.filter (fun (p : ℕ) => (p : ℝ) ^ ε < 2), (2 / ε : ℝ)) := by rw [one_mul]
    _ = (2 / ε : ℝ) ^ (n.primeFactors.filter (fun (p : ℕ) => (p : ℝ) ^ ε < 2)).card := by rw [h_second_eq]
    _ = (2 / ε : ℝ) ^ ((n.primeFactors.filter (fun (p : ℕ) => (p : ℝ) ^ ε < 2)).card : ℝ) := by norm_cast
    _ ≤ (2 / ε : ℝ) ^ (2 : ℝ) ^ (1 / ε) := h_final

lemma lemma14 (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  : ∃ (C : ℝ), C > 0 ∧ (2 / ε) ^ ((2 : ℝ) ^ (1 / ε)) ≤ C := by
  -- Choose C to be the value of the expression plus 1
  use (2 / ε) ^ ((2 : ℝ) ^ (1 / ε)) + 1
  constructor
  · -- Show C > 0
    have h1 : 0 < 2 / ε := by positivity
    have h2 : 0 < (2 : ℝ) ^ (1 / ε) := Real.rpow_pos_of_pos (by norm_num) _
    have h3 : 0 < (2 / ε) ^ ((2 : ℝ) ^ (1 / ε)) := Real.rpow_pos_of_pos h1 _
    linarith
  · -- Show the inequality
    linarith

lemma lemma15 (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  : 
  ∃ (C : ℝ), C > 0 ∧ ∀ (n : ℕ), 1 ≤ n → (tau n : ℝ) / ((n : ℝ) ^ ε) ≤ C := by
  -- Use lemma14 to get a bound for the expression (2/ε)^(2^(1/ε))
  obtain ⟨C, hC_pos, hC_bound⟩ := lemma14 ε hε hε_small
  -- Use this C as our witness
  use C
  constructor
  · exact hC_pos
  · intro n hn
    -- Apply lemma13 to bound tau(n)/n^ε
    have h13 := lemma13 n ε hn hε hε_small
    -- Combine with the bound from lemma14
    exact le_trans h13 hC_bound

lemma lemma16 (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  : 
  ∃ (C : ℝ), C > 0 ∧ ∀ (n : ℕ), 1 ≤ n → (tau n : ℝ) / ((n : ℝ) ^ ε) ≤ C := by
  -- Since lemma16 and lemma15 have identical statements, apply lemma15 directly
  exact lemma15 ε hε hε_small

lemma lemma17 (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  : 
  ∃ (C : ℝ), C > 0 ∧ ∀ (n : ℕ), 1 ≤ n → (tau n : ℝ) ≤ C * ((n : ℝ) ^ ε) := by
  -- Get the constant from lemma16
  obtain ⟨C, hC_pos, hC_bound⟩ := lemma16 ε hε hε_small
  -- Use the same constant C
  use C
  constructor
  · exact hC_pos
  · intro n hn
    -- We have (tau n : ℝ) / ((n : ℝ) ^ ε) ≤ C from lemma16
    have h_div_bound := hC_bound n hn
    -- We need to show (tau n : ℝ) ≤ C * ((n : ℝ) ^ ε)
    -- Since ((n : ℝ) ^ ε) > 0, we can multiply both sides by it
    have h_pow_pos : 0 < ((n : ℝ) ^ ε) := by
      apply Real.rpow_pos_of_pos
      rw [Nat.cast_pos]
      exact Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
    -- Multiply both sides of the inequality by ((n : ℝ) ^ ε)
    have h_mul_ineq : ((tau n : ℝ) / ((n : ℝ) ^ ε)) * ((n : ℝ) ^ ε) ≤ C * ((n : ℝ) ^ ε) := by
      apply mul_le_mul_of_nonneg_right h_div_bound
      exact le_of_lt h_pow_pos
    -- Simplify the left side using div_mul_cancel₀
    have h_simplify : ((tau n : ℝ) / ((n : ℝ) ^ ε)) * ((n : ℝ) ^ ε) = (tau n : ℝ) := by
      apply div_mul_cancel₀
      exact ne_of_gt h_pow_pos
    rw [h_simplify] at h_mul_ineq
    exact h_mul_ineq

theorem divisor_bound_tau_le_n_pow_o_one :
  ∀ ε : ℝ, ε > 0 → ε < 1/100 → 
  Filter.Tendsto (fun n : ℕ => (tau n : ℝ) / (n : ℝ) ^ ε) Filter.atTop (nhds 0) := by
  intro ε hε hε_small
  
  -- STEP 1: Apply lemma17 with ε/2 (the key insight!)
  have hε_half : ε / 2 > 0 := by linarith
  have hε_half_small : ε / 2 < 1/100 := by linarith
  obtain ⟨C, hC_pos, hC_bound⟩ := lemma17 (ε / 2) hε_half hε_half_small
  
  -- STEP 2: Show tau(n)/n^ε ≤ C/n^(ε/2) eventually
  have h_bound : ∀ᶠ n in Filter.atTop, (tau n : ℝ) / (n : ℝ) ^ ε ≤ C / (n : ℝ) ^ (ε / 2) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    -- For n > 0, we have n ≥ 1
    have hn_ge_1 : 1 ≤ n := hn
    have h1 := hC_bound n hn_ge_1  -- tau(n) ≤ C * n^(ε/2)
    have h_n_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    
    -- Apply the bound: tau(n) ≤ C * n^(ε/2), so tau(n)/n^ε ≤ C/n^(ε/2)
    have h_key : (tau n : ℝ) / (n : ℝ) ^ ε ≤ (C * (n : ℝ) ^ (ε / 2)) / (n : ℝ) ^ ε := by
      apply div_le_div_of_nonneg_right h1
      exact Real.rpow_nonneg (Nat.cast_nonneg n) ε
    
    -- Algebraic manipulation: C * n^(ε/2) / n^ε = C / n^(ε/2)
    rw [mul_div_assoc] at h_key
    have h_simp : (n : ℝ) ^ (ε / 2) / (n : ℝ) ^ ε = (n : ℝ) ^ (ε / 2 - ε) := by
      exact (Real.rpow_sub h_n_pos (ε / 2) ε).symm
    rw [h_simp] at h_key
    have h_neg : ε / 2 - ε = -(ε / 2) := by ring
    rw [h_neg, Real.rpow_neg (le_of_lt h_n_pos)] at h_key
    rwa [div_eq_mul_inv] at h_key
  
  -- STEP 3: Show C/n^(ε/2) → 0
  have h_lim : Filter.Tendsto (fun n : ℕ => C / (n : ℝ) ^ (ε / 2)) Filter.atTop (nhds 0) := by
    have h_inv_lim : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-(ε / 2))) Filter.atTop (nhds 0) := 
      (tendsto_rpow_neg_atTop hε_half).comp tendsto_natCast_atTop_atTop
    convert h_inv_lim.const_mul C using 1
    · ext n
      rw [Real.rpow_neg (Nat.cast_nonneg n)]
      simp [div_eq_inv_mul, mul_comm]
    · rw [mul_zero]
  
  -- STEP 4: Apply squeeze theorem: 0 ≤ tau(n)/n^ε ≤ C/n^(ε/2) → 0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds h_lim
    (Filter.Eventually.of_forall fun n => 
      div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    h_bound

-- Definition [Radical]
def rad (n : ℕ) : ℕ := if n = 0 then 0 else n.primeFactors.prod id

lemma rad_eq_prod_distinct_prime_factors (n : ℕ) (hn : n ≠ 0) : 
  rad n = n.factorization.support.prod id := by
  unfold rad
  simp only [hn, if_false]
  simp only [Nat.support_factorization]

lemma rad_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) : rad (a * b) = rad a * rad b := by
  -- Handle the case where the product is 0
  by_cases hab : a * b = 0
  · rw [Nat.mul_eq_zero] at hab
    cases hab with
    | inl ha => 
      -- If a = 0, then b = 1 since they're coprime
      have hb : b = 1 := by rwa [ha, Nat.coprime_zero_left] at h
      simp [rad, ha, hb]
    | inr hb => 
      -- If b = 0, then a = 1 since they're coprime
      have ha : a = 1 := by rwa [hb, Nat.coprime_zero_right] at h
      simp [rad, ha, hb]
  · -- Case where a * b ≠ 0
    have ha : a ≠ 0 := left_ne_zero_of_mul hab
    have hb : b ≠ 0 := right_ne_zero_of_mul hab
    simp only [rad, hab, ha, hb, if_false]
    -- Key insight: for coprime numbers, prime factors of product = union of prime factors
    rw [Nat.Coprime.primeFactors_mul h]
    -- Since prime factors are disjoint, product over union = product of products
    rw [Finset.prod_union (Nat.Coprime.disjoint_primeFactors h)]

lemma rad_abc_of_coprime (a b c : ℕ) (ha : a ≥ 1) (hb : b ≥ 1) (hc : c ≥ 1) 
    (h_abc_coprime : Nat.Coprime a (b * c)) (h_bc_coprime : Nat.Coprime b c) : 
    rad (a * b * c) = rad a * rad b * rad c := by
  -- Strategy: Apply the two-factor multiplicative property twice
  -- First rewrite a * b * c as a * (b * c)
  rw [mul_assoc a b c]
  -- Apply rad_mul_of_coprime with a and (b * c): rad(a * (b * c)) = rad(a) * rad(b * c)
  rw [rad_mul_of_coprime h_abc_coprime]
  -- Apply rad_mul_of_coprime with b and c: rad(b * c) = rad(b) * rad(c)
  rw [rad_mul_of_coprime h_bc_coprime]
  -- Rearrange multiplication: rad a * (rad b * rad c) = rad a * rad b * rad c
  rw [← mul_assoc]

lemma lemma23 (a b c : ℕ) (ha : a ≥ 1) (hb : b ≥ 1) (hc : c ≥ 1) 
    (h_abc_coprime : Nat.Coprime a (b * c)) (h_bc_coprime : Nat.Coprime b c) : 
    rad (a * b) * rad (a * c) * rad (b * c) = (rad (a * b * c)) ^ 2 := by
  -- First derive that a, b, c are pairwise coprime from the given conditions
  have h_ac_coprime : Nat.Coprime a c := Nat.Coprime.coprime_mul_left_right h_abc_coprime
  have h_ab_coprime : Nat.Coprime a b := by
    rw [mul_comm b c] at h_abc_coprime
    exact Nat.Coprime.coprime_mul_left_right h_abc_coprime
  
  -- Apply multiplicative properties to expand each term
  rw [rad_mul_of_coprime h_ab_coprime]   -- rad(a*b) = rad(a) * rad(b)
  rw [rad_mul_of_coprime h_ac_coprime]   -- rad(a*c) = rad(a) * rad(c)
  rw [rad_mul_of_coprime h_bc_coprime]   -- rad(b*c) = rad(b) * rad(c)
  
  -- Apply three-factor multiplicative property to the right side
  rw [rad_abc_of_coprime a b c ha hb hc h_abc_coprime h_bc_coprime]
  
  -- Now we have: (rad a * rad b) * (rad a * rad c) * (rad b * rad c) = (rad a * rad b * rad c)²
  -- This simplifies to: (rad a)² * (rad b)² * (rad c)² = (rad a * rad b * rad c)²
  ring
