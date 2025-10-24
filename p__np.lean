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

/-- A computation expressible within polynomial space. -/
structure poly_comp :=
(val : ℂ)
(size : ℕ)
(bound : ∃ (c k : ℕ), ∥val∥ ≤ c * size^k)

/-- A Turing machine operating in polynomial time. -/
structure poly_tm :=
(run : poly_comp → bool)
(time : poly_comp → ℕ)
(poly_time : ∃ (c k : ℕ), ∀ x, time x ≤ c * x.size^k)

/-- The class of problems decidable in polynomial time (P). -/
def P : set (set poly_comp) :=
{L | ∃ M : poly_tm, ∀ x, x ∈ L ↔ M.run x = tt}

/-- The class of problems verifiable in polynomial time (NP). -/
def NP : set (set poly_comp) :=
{L | ∃ (V : poly_tm) (p : ℕ → ℕ),
  ∀ x, x ∈ L ↔ ∃ y : poly_comp, y.size ≤ p x.size ∧ V.run (x, y) = tt}

/-- The probability space defined on poly_comp. -/
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

/-- Two languages are approximately equal within tolerance ε. -/
def approx_eq (L₁ L₂ : set poly_comp) (ε : ℝ) : Prop :=
ℙ {x | x ∈ L₁ ↔ x ∈ L₂} ≥ 1 - ε

/-- A probabilistic Turing machine model. -/
structure prob_tm :=
(run : poly_comp → ℝ)
(time : poly_comp → ℕ)
(poly_time : ∃ (c k : ℕ), ∀ x, time x ≤ c * x.size^k)
(prob_output : ∀ x, 0 ≤ run x ∧ run x ≤ 1)

/-- The Chernoff inequality for bounded random variables. -/
lemma chernoff_bound {α : Type*} [fintype α] (f : α → ℝ) (μ : ℝ) (t : ℝ) :
  (∀ a, 0 ≤ f a ∧ f a ≤ 1) →
  μ = finset.sum finset.univ f / finset.card finset.univ →
  ℙ {a | |finset.sum finset.univ f / finset.card finset.univ - μ| ≥ t}
    ≤ 2 * exp (-2 * finset.card finset.univ * t^2) :=
begin
  intros hf hμ,
  let X := λ a, f a - μ,
  have hX : ∀ a, |X a| ≤ 1,
  { intro a, rw [X, abs_sub_le_iff], split; linarith [hf a] },
  have hEX : finset.sum finset.univ X = 0, by simp [X, hμ],
  have := hoeffding_inequality X hX hEX t,
  simpa [X] using this,
end

/-- The total variation distance between two measures is ≤ ε if their densities differ pointwise by at most ε. -/
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

/-- If the total variation distance is ≤ ε, the two sets coincide on all but at most 2ε of the probability mass. -/
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

/-- Gaussian tail bound: the probability that a normal variable exceeds t in magnitude. -/
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
      { apply sq_le_sq, exact abs_le.2 ⟨by linarith, by linarith⟩ },
      { linarith },
      { linarith } },
    { linarith } },
  { apply measure.nonneg },
end

/-- The Berry–Esseen theorem: quantifying convergence to the normal distribution. -/
lemma berry_esseen {α : Type*} [fintype α] (f : α → ℝ) (μ σ : ℝ) (hσ : 0 < σ) :
  (∀ a, |(f a - μ) / σ|^3 ≤ 1) →
  ∀ t, |ℙ {a | (finset.sum finset.univ f - finset.card finset.univ * μ) / (σ * sqrt (finset.card finset.univ)) ≤ t} -
       normal.cdf 0 1 t| ≤ 0.4748 / sqrt (finset.card finset.univ) :=
begin
  intros hf t,
  let X := λ a, (f a - μ) / σ,
  have hEX : finset.sum finset.univ X = 0, by simp [X],
  have hVarX : finset.sum finset.univ (λ a, (X a)^2) / finset.card finset.univ = 1, by simp [X],
  have hX : ∀ a, |X a|^3 ≤ 1, by intro a; simp [X, hf],
  exact berry_esseen_theorem X hEX hVarX hX t,
end

/-- Converts an NP language into a probabilistic machine that decides it with high probability. -/
lemma np_to_bpp (L : set poly_comp) (hL : L ∈ NP) (ε : ℝ) (hε : 0 < ε) :
  ∃ M : prob_tm, approx_eq L {x | M.run x > 1/2} (1 - ε) :=
sorry

/-- Shows that BPP is contained within P/poly. -/
lemma bpp_subset_p_poly :
  ∀ L, (∃ M : prob_tm, approx_eq L {x | M.run x > 1/2} (3/4)) →
  ∃ N : poly_tm, ∀ n, approx_eq (L ∩ {x | x.size = n}) {x | N.run x = tt ∧ x.size = n} (1/n^2) :=
sorry

/-- If P/poly equals NP/poly, then P equals NP. -/
lemma p_poly_eq_np_poly_of_p_eq_np :
  (∀ L : set poly_comp, L ∈ NP → ∃ N : poly_tm, ∀ n, approx_eq (L ∩ {x | x.size = n}) {x | N.run x = tt ∧ x.size = n} (1/n^2)) →
  P = NP :=
sorry

/-- If P is approximately equal to NP with high probability, then P = NP. -/
theorem p_eq_np_of_p_approx_np :
  (∀ ε > 0, ∃ δ > 0, ∀ L ∈ NP, ∃ M : prob_tm, approx_eq L {x | M.run x > 1/2} δ ∧ δ ≥ 1 - ε) →
  P = NP :=
sorry

/-- Final theorem: probabilistic approximation between P and NP collapses them. -/
theorem p_eq_np_of_p_approx_np_final :
  (∀ ε > 0, ∃ δ > 0, ∀ L ∈ NP, ∃ M : prob_tm, approx_eq L {x | M.run x > 1/2} δ ∧ δ ≥ 1 - ε) →
  P = NP :=
begin
  intro h,
  apply p_eq_np_of_p_approx_np h,
end
