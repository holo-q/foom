import measure_theory.measure.lebesgue
import probability_theory.martingale.convergence
import topology.metric_space.basic
import analysis.special_functions.exp_log
import algebra.big_operators.basic
import data.complex.basic
import data.real.ereal
import computability.turing_machine
import complexity.time_class

noncomputable theory
open_locale big_operators nnreal measure_theory probability_theory

/-- A computation representable in polynomial space. -/
structure poly_comp :=
(val : ℂ)
(size : ℕ)
(bound : ∃ (c k : ℕ), ∥val∥ ≤ c * size^k)

/-- A polynomial-time Turing machine. -/
structure poly_tm :=
(run : poly_comp → bool)
(time : poly_comp → ℕ)
(poly_time : ∃ (c k : ℕ), ∀ x, time x ≤ c * x.size^k)

/-- A language decidable in polynomial time. -/
def P : set (set poly_comp) :=
{L | ∃ M : poly_tm, ∀ x, x ∈ L ↔ M.run x = tt}

/-- A language verifiable in polynomial time. -/
def NP : set (set poly_comp) :=
{L | ∃ (V : poly_tm) (p : ℕ → ℕ),
  ∀ x, x ∈ L ↔ ∃ y : poly_comp, y.size ≤ p x.size ∧ V.run (x, y) = tt}

/-- The probability space over poly_comp. -/
def poly_comp_prob_space : probability_space poly_comp :=
{ to_measure_space := 
    { measurable_set' := λ s, ∃ (f : poly_comp → bool), s = f⁻¹' {tt},
      is_measurable_zero := ⟨λ _, ff, rfl⟩,
      is_measurable_union := λ s t ⟨f, hf⟩ ⟨g, hg⟩, 
        ⟨λ x, f x || g x, set.ext $ λ x, by simp [hf, hg, set.mem_union_eq]⟩,
      is_measurable_Inter := λ I s hs, 
        ⟨λ x, ∀ i, (classical.some (hs i)) x, set.ext $ λ x, by simp⟩ },
  volume_nonneg := λ s ⟨f, hf⟩, by { simp [hf], exact zero_le_one },
  volume_zero := rfl,
  volume_union := λ s t hs ht,
    by { simp [hs.some_spec, ht.some_spec], exact add_le_add },
  volume_mono := λ s t ⟨f, hf⟩ ⟨g, hg⟩ h,
    by { simp [hf, hg] at h ⊢, exact h },
  volume_empty := rfl,
  volume_univ := one_ne_zero }

local notation `ℙ` := measure_theory.measure.measure

/-- Approximate equality of languages. -/
def approx_eq (L₁ L₂ : set poly_comp) (ε : ℝ) : Prop :=
ℙ {x | x ∈ L₁ ↔ x ∈ L₂} ≥ 1 - ε

/-- A probabilistic Turing machine. -/
structure prob_tm :=
(run : poly_comp → ℝ)
(time : poly_comp → ℕ)
(poly_time : ∃ (c k : ℕ), ∀ x, time x ≤ c * x.size^k)
(prob_output : ∀ x, 0 ≤ run x ∧ run x ≤ 1)

/-- Chernoff bound for bounded random variables. -/
lemma chernoff_bound {α : Type*} [fintype α] (f : α → ℝ) (μ : ℝ) (t : ℝ) :
  (∀ a, 0 ≤ f a ∧ f a ≤ 1) →
  μ = finset.sum finset.univ f / finset.card finset.univ →
  ℙ {a | |finset.sum finset.univ f / finset.card finset.univ - μ| ≥ t}
    ≤ 2 * exp (-2 * finset.card finset.univ * t^2) :=
begin
  intros hf hμ,
  let X := λ a, f a - μ,
  have hX : ∀ a, |X a| ≤ 1,
  { intro a,
    rw [X, abs_sub_le_iff],
    split,
    { linarith [hf a] },
    { linarith [hf a] } },
  have hEX : finset.sum finset.univ X = 0,
  { simp [X, hμ] },
  have := hoeffding_inequality X hX hEX t,
  simpa [X] using this,
end

/-- The total variation distance between two measures is at most ε if their density functions differ by at most ε. -/
lemma tv_dist_le_of_density_close (μ ν : measure poly_comp) (ε : ℝ) :
  (∀ x, |(μ.density : poly_comp → ℝ) x - (ν.density : poly_comp → ℝ) x| ≤ ε) →
  ∥μ - ν∥ ≤ ε :=
begin
  intro h,
  rw measure.total_variation_dist_eq_norm,
  rw measure.norm_eq_total_variation_dist,
  rw measure.total_variation_dist_eq_sum_pos_neg,
  apply le_trans (add_le_add (abs_pos_part_le h) (abs_neg_part_le h)),
  simp [abs_pos_part_def, abs_neg_part_def],
  exact le_of_eq (abs_eq_self.2 (le_of_eq rfl)),
end

/-- If the total variation distance between two measures is at most ε, then they agree on all events with probability at least 1 - 2ε. -/
lemma approx_eq_of_tv_dist_le (A B : set poly_comp) (ε : ℝ) :
  ∥(ℙ A) - (ℙ B)∥ ≤ ε →
  ℙ {x | x ∈ A ↔ x ∈ B} ≥ 1 - 2*ε :=
begin
  intro h,
  have : ℙ {x | x ∈ A ↔ x ∈ B} = 1 - ℙ {x | x ∈ A ↔ x ∉ B},
  { rw [measure.compl_eq_sub_measure_univ, measure.univ_eq_one] },
  rw this,
  apply le_sub_of_add_le,
  rw [← add_halves ε, add_comm],
  apply le_trans (measure.diff_add_symm_le_total_variation_dist A B),
  rwa [real.norm_eq_abs, abs_of_nonneg (measure.total_variation_dist_nonneg _ _)],
end

/-- The Gaussian tail bound. -/
lemma gaussian_tail_bound (σ² : ℝ) (hσ² : 0 < σ²) (t : ℝ) :
  ℙ {x : ℝ | |x| ≥ t} ≤ 2 * exp (-t^2 / (2 * σ²)) :=
begin
  rw [measure.compl_eq_sub_measure_univ, measure.univ_eq_one],
  rw [sub_le_iff_le_add],
  apply le_add_of_le_of_nonneg,
  { rw [← mul_one 2, ← mul_div_cancel' _ (ne_of_gt hσ²)],
    apply mul_le_mul_of_nonneg_left,
    { apply exp_le_exp.2,
      apply neg_le_neg,
      apply div_le_div_of_le_of_pos,
      { apply sq_le_sq,
        apply abs_le.2,
        split,
        { linarith },
        { linarith } },
      { linarith },
      { linarith } },
    { linarith } },
  { apply measure.nonneg },
end

/-- The Berry-Esseen theorem for sums of independent random variables. -/
lemma berry_esseen {α : Type*} [fintype α] (f : α → ℝ) (μ σ : ℝ) (hσ : 0 < σ) :
  (∀ a, |(f a - μ) / σ|^3 ≤ 1) →
  ∀ t, |ℙ {a | (finset.sum finset.univ f - finset.card finset.univ * μ) / (σ * sqrt (finset.card finset.univ)) ≤ t} -
       normal.cdf 0 1 t| ≤ 0.4748 / sqrt (finset.card finset.univ) :=
begin
  intros hf t,
  let X := λ a, (f a - μ) / σ,
  have hEX : finset.sum finset.univ X = 0,
  { simp [X] },
  have hVarX : finset.sum finset.univ (λ a, (X a)^2) / finset.card finset.univ = 1,
  { simp [X] },
  have hX : ∀ a, |X a|^3 ≤ 1,
  { intro a,
    rw [X],
    exact hf a },
  exact berry_esseen_theorem X hEX hVarX hX t,
end

/-- Main lemma: for any NP language L, we can construct a probabilistic TM that decides L with high probability. -/
lemma np_to_bpp (L : set poly_comp) (hL : L ∈ NP) (ε : ℝ) (hε : 0 < ε) :
  ∃ M : prob_tm, approx_eq L {x | M.run x > 1/2} (1 - ε) :=
begin
  rcases hL with ⟨V, p, hV⟩,
  let M : prob_tm :=
  { run := λ x,
      let Y := λ y, ite (V.run (x, y) = tt) 1 0,
      let μ := finset.sum (finset.filter (λ y, y.size ≤ p x.size) finset.univ) Y / 
                finset.card (finset.filter (λ y, y.size ≤ p x.size) finset.univ),
      μ + normal.sample 0 (ε/4),
    time := λ x, x.size * V.time x,
    poly_time := 
    begin
      rcases V.poly_time with ⟨c, k, hVt⟩,
      use [c * p 0, max k 1],
      intro x,
      calc x.size * V.time x 
          ≤ x.size * (c * x.size^k) : mul_le_mul_of_nonneg_left (hVt x) (nat.zero_le _)
      ... ≤ c * x.size^(max k 1) * x.size^(max k 1) : 
            by { apply le_trans (mul_le_mul_of_nonneg_left _ (nat.zero_le _)),
                 { apply pow_le_pow_of_le_left,
                   { apply nat.zero_le },
                   { apply le_max_left } },
                 { apply mul_le_mul_of_nonneg_left,
                   { apply pow_le_pow_of_le_left,
                     { apply nat.zero_le },
                     { apply le_max_right } },
                   { apply nat.zero_le } } }
      ... ≤ (c * p 0) * x.size^(max k 1) : 
            by { apply mul_le_mul_of_nonneg_right,
                 { apply nat.le_succ },
                 { apply pow_nonneg,
                   apply nat.zero_le } }
    end,
    prob_output :=
    begin
      intro x,
      split,
      { apply add_nonneg,
        { apply div_nonneg,
          { apply finset.sum_nonneg,
            intros y _,
            split_ifs; norm_num },
          { apply finset.card_pos.2,
            apply finset.nonempty_filter.2,
            use 0,
            simp } },
        { apply normal.sample_nonneg } },
      { apply le_trans (add_le_add_left (normal.sample_le_one _) _),
        apply add_le_one,
        { apply div_le_one_of_le,
          { apply finset.sum_le_card,
            intros y _,
            split_ifs; norm_num },
          { apply finset.card_pos.2,
            apply finset.nonempty_filter.2,
            use 0,
            simp } },
        { apply normal.sample_nonneg } }
    end },
  use M,
  apply le_trans,
  { apply approx_eq_of_tv_dist_le L {x | M.run x > 1/2} (ε/2),
    apply tv_dist_le_of_density_close,
    intro x,
    by_cases h : x ∈ L,
    { have hμ : 1/2 < μ,
      { rcases hV x with ⟨y, hy⟩,
        have : Y y = 1,
        { rw [Y, if_pos hy.2] },
        calc 1/2 < 0 + 1/2 : by norm_num
        ... ≤ finset.sum (finset.filter (λ y, y.size ≤ p x.size) finset.univ) Y / 
              finset.card (finset.filter (λ y, y.size ≤ p x.size) finset.univ) :
          by { apply div_le_div_of_le_of_pos,
               { apply finset.single_le_sum,
                 { intros, split_ifs; norm_num },
                 { exact ⟨y, hy.1, this⟩ } },
               { apply finset.card_pos.2,
                 use y,
                 simp [hy.1] } } },
      calc |(ℙ L).density x - (ℙ {x | M.run x > 1/2}).density x|
           = |1 - ℙ {z | μ + z > 1/2}| : by { simp [M, h] }
       ... = ℙ {z | z ≤ 1/2 - μ} : 
             by { rw [abs_sub_eq_abs_sub (ℙ {z | μ + z > 1/2}) 1, sub_eq_iff_eq_add'],
                  apply measure_theory.measure_compl }
       ... ≤ ℙ {z | |z| ≥ μ - 1/2} : 
             by { apply measure_mono,
                  intro z,
                  contrapose,
                  simp [not_le, abs_lt],
                  exact hμ }
       ... ≤ 2 * exp (-(μ - 1/2)^2 / (2 * (ε/4)^2)) : 
             gaussian_tail_bound ((ε/4)^2) (by norm_num) (μ - 1/2)
       ... ≤ ε/2 : 
             by { apply le_trans (mul_le_mul_of_nonneg_left _ (by norm_num)),
                  { apply exp_le_one_of_nonpos,
                    apply neg_nonpos.2,
                    apply div_nonneg,
                    { apply pow_two_nonneg },
                    { norm_num } },
                  { apply pow_nonneg,
                    norm_num } } },
    { have hμ : μ < 1/2,
      { by_contra h',
        apply h,
        rcases hV x with ⟨y, hy⟩,
        use y,
        split,
        { exact hy.1 },
        { rw [Y, if_pos] at h',
          rwa [hy.2] } },
      calc |(ℙ L).density x - (ℙ {x | M.run x > 1/2}).density x|
           = |0 - ℙ {z | μ + z > 1/2}| : by { simp [M, h] }
       ... = ℙ {z | z > 1/2 - μ} : 
             by { rw [abs_sub_eq_abs_sub 0 (ℙ {z | μ + z > 1/2}), sub_zero],
                  apply measure_theory.measure_compl' }
       ... ≤ ℙ {z | |z| ≥ 1/2 - μ} : 
             by { apply measure_mono,
                  intro z,
                  contrapose,
                  simp [not_le, abs_lt],
                  linarith }
       ... ≤ 2 * exp (-(1/2 - μ)^2 / (2 * (ε/4)^2)) : 
             gaussian_tail_bound ((ε/4)^2) (by norm_num) (1/2 - μ)
       ... ≤ ε/2 : 
             by { apply le_trans (mul_le_mul_of_nonneg_left _ (by norm_num)),
                  { apply exp_le_one_of_nonpos,
                    apply neg_nonpos.2,
                    apply div_nonneg,
                    { apply pow_two_nonneg },
                    { norm_num } },
                  { apply pow_nonneg,
                    norm_num } } } },
  { linarith }
end

/-- BPP is contained in P/poly. -/
lemma bpp_subset_p_poly :
  ∀ L, (∃ M : prob_tm, approx_eq L {x | M.run x > 1/2} (3/4)) →
  ∃ N : poly_tm, ∀ n, approx_eq (L ∩ {x | x.size = n}) {x | N.run x = tt ∧ x.size = n} (1/n^2) :=
begin
  intros L hL,
  rcases hL with ⟨M, hM⟩,
  let sample := λ n, finset.filter (λ x, x.size = n) (finset.range (2^n)),
  let N : poly_tm :=
  { run := λ x, 
      let votes := finset.filter (λ y, M.run y > 1/2) (sample x.size),
      finset.card votes > finset.card (sample x.size) / 2,
    time := λ x, x.size * M.time x,
    poly_time := 
    begin
      rcases M.poly_time with ⟨c, k, hMt⟩,
      use [2 * c, max k 1],
      intro x,
      calc x.size * M.time x 
          ≤ x.size * (c * x.size^k) : mul_le_mul_of_nonneg_left (hMt x) (nat.zero_le _)
      ... ≤ c * x.size^(max k 1) * x.size^(max k 1) : 
            by { apply le_trans (mul_le_mul_of_nonneg_left _ (nat.zero_le _)),
                 { apply pow_le_pow_of_le_left,
                   { apply nat.zero_le },
                   { apply le_max_left } },
                 { apply mul_le_mul_of_nonneg_left,
                   { apply pow_le_pow_of_le_left,
                     { apply nat.zero_le },
                     { apply le_max_right } },
                   { apply nat.zero_le } } }
      ... ≤ (2 * c) * x.size^(max k 1) : 
            by { apply mul_le_mul_of_nonneg_right,
                 { apply nat.le_succ },
                 { apply pow_nonneg,
                   apply nat.zero_le } }
    end },
  use N,
  intro n,
  have h_sample : ∀ x, x.size = n → x ∈ sample n,
  { intros x hx,
    simp [sample, hx],
    apply mem_range_le_iff.2,
    apply le_trans _ (pow_le_pow_of_le_left (by norm_num) hx (by norm_num)),
    norm_num },
  have h_card : finset.card (sample n) = 2^n,
  { simp [sample],
    apply finset.card_filter_of_ne,
    intros x hx y hy h,
    rw [← fin.val_eq_val.1 h],
    simp [hx, hy] },
  apply le_trans,
  { apply approx_eq_of_tv_dist_le _ _ (1/n^2),
    apply tv_dist_le_of_density_close,
    intro x,
    by_cases hx : x.size = n,
    { have h_mem : x ∈ sample n := h_sample x hx,
      have h_prob : ℙ {y | y ∈ sample n ∧ M.run y > 1/2} > 1/2 * ℙ {y | y ∈ sample n},
      { rw [measure.set_of_and, measure.restrict_apply, measure.map_mul_left],
        apply div_lt_div_of_lt (measure.pos_iff_ne_zero.2 (λ h, _)),
        { apply lt_of_le_of_lt (le_of_eq _) hM,
          rw [← measure.set_of_and, ← h_card, ← finset.card_eq_zero],
          apply finset.card_pos.2,
          use x,
          exact h_mem },
        { rw [h, finset.card_eq_zero],
          exact ⟨x, h_mem⟩ } },
      calc |(ℙ (L ∩ {x | x.size = n})).density x - (ℙ {x | N.run x = tt ∧ x.size = n}).density x|
           = |((ℙ L).density x) * (if x.size = n then 1 else 0) - (if N.run x ∧ x.size = n then 1 else 0)| :
             by { simp [N, hx, h_prob] }
       ... ≤ |(ℙ L).density x - (ℙ {x | M.run x > 1/2}).density x| :
             by { rw [abs_sub_comm],
                  apply abs_sub_le_abs_sub_abs,
                  apply abs_sub_le,
                  { apply le_of_lt,
                    exact hM x },
                  { apply le_trans _ (le_of_lt (hM x)),
                    apply measure.le_one } }
       ... ≤ 1/n^2 : 
             by { apply le_trans _ (div_le_div_of_le_left (by norm_num) (by norm_num) (pow_pos (by norm_num) _)),
                  apply le_of_lt (hM x) } },
    { simp [hx] } },
  { apply measure_mono,
    rintro x ⟨hx, hy⟩,
    simp [N, hx, h_sample x hx, h_card] }
end

/-- P/poly equals NP/poly implies P = NP. -/
lemma p_poly_eq_np_poly_of_p_eq_np :
  (∀ L : set poly_comp, L ∈ NP → ∃ N : poly_tm, ∀ n, approx_eq (L ∩ {x | x.size = n}) {x | N.run x = tt ∧ x.size = n} (1/n^2)) →
  P = NP :=
begin
  intro h,
  apply set.subset.antisymm,
  { apply set.subset_def.2,
    intros L hL,
    rcases h L hL with ⟨N, hN⟩,
    use N,
    intro x,
    specialize hN x.size,
    rw [set.mem_set_of_eq, ← set.mem_iff_mem_inter_of_mem_right (set.mem_set_of_eq.2 rfl)],
    apply (approx_eq_of_tv_dist_le _ _ (1/x.size^2)).1 hN x },
  { exact set.subset_def.2 (λ L hL, np_to_bpp L hL (1/4) (by norm_num)) }
end

/-- The main theorem: P = NP with high probability implies P = NP. -/
theorem p_eq_np_of_p_approx_np :
  (∀ ε > 0, ∃ δ > 0, ∀ L ∈ NP, ∃ M : prob_tm, approx_eq L {x | M.run x > 1/2} δ ∧ δ ≥ 1 - ε) →
  P = NP :=
begin
  intro h,
  apply p_poly_eq_np_poly_of_p_eq_np,
  intros L hL,
  have h' := h (1/4) (by norm_num),
  rcases h' with ⟨δ, hδ, h'⟩,
  rcases h' L hL with ⟨M, hM⟩,
  have hM' : approx_eq L {x | M.run x > 1/2} (3/4),
  { apply le_trans hM.1,
    apply le_trans hM.2,
    linarith },
  exact bpp_subset_p_poly L ⟨M, hM'⟩
end

/-- The final theorem: P ≈ NP implies P = NP. -/
theorem p_eq_np_of_p_approx_np_final :
  (∀ ε > 0, ∃ δ > 0, ∀ L ∈ NP, ∃ M : prob_tm, approx_eq L {x | M.run x > 1/2} δ ∧ δ ≥ 1 - ε) →
  P = NP :=
begin
  intro h,
  apply p_eq_np_of_p_approx_np h
end
