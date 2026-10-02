import Formalization.Eta

set_option linter.style.header false

namespace trm

theorem eta_diamond : ∀ m m₁ m₂,
    eta m m₁ → eta m m₂ →
    ∃ m₃, clos_refl eta m₁ m₃ ∧ clos_refl eta m₂ m₃ := by
  intro m m₁ m₂ h₁ h₂
  induction h₁ generalizing m₂
  -- Caso 1
  case eta_app1 t t₁ z lc_z r_t_t₁ ih =>
    cases h₂
    -- Caso 1.1
    case eta_app1 t₂ r_t_t₂ lc_z =>
      rcases ih t₂ r_t_t₂ with ⟨t₃, rl_t₁_t₃, rl_t₂_t₃⟩
      use app t₃ z
      constructor
      · exact refl_app1 lc_z rl_t₁_t₃
      · exact refl_app1 lc_z rl_t₂_t₃
    -- Caso 1.2
    case eta_app2 z₁ lc_t r_z_z₁ =>
      use app t₁ z₁
      constructor
      · apply refl_app2 (eta_lc_right r_t_t₁)
        exact clos_refl.step z z₁ r_z_z₁
      · apply refl_app1 (eta_lc_right r_z_z₁)
        exact clos_refl.step t t₁ r_t_t₁
  -- Caso 2
  case eta_app2 z t t₁ lc_z r_t_t₁ ih =>
    cases h₂
    -- Caso 2.1
    case eta_app1 z₁ r_z_z₁ lc_t =>
      use app z₁ t₁
      constructor
      · apply refl_app1 (eta_lc_right r_t_t₁)
        exact clos_refl.step z z₁ r_z_z₁
      · apply refl_app2 (eta_lc_right r_z_z₁)
        exact clos_refl.step t t₁ r_t_t₁
    -- Caso 2.2
    case eta_app2 t₂ lc_z r_t_t₂ =>
      rcases ih t₂ r_t_t₂ with ⟨t₃, rl_t₁_t₃, rl_t₂_t₃⟩
      use app z t₃
      constructor
      · exact refl_app2 lc_z rl_t₁_t₃
      · exact refl_app2 lc_z rl_t₂_t₃
  -- Caso 3
  case eta_red t lc_t =>
    cases h₂
    -- Caso 3.1
    case eta_red lc_t =>
      use t
      constructor
      · exact clos_refl.refl t
      · exact clos_refl.refl t
    -- Caso 3.2
    case eta_abs L u hbody =>
      rcases eta_redex_body lc_t hbody with ⟨t', r_t_t', hu⟩
      rewrite [hu]
      use t'
      constructor
      · exact clos_refl.step t t' r_t_t'
      · apply clos_refl.step
        exact eta.eta_red (eta_lc_right r_t_t')
  -- Caso 4
  case eta_abs L t t₁ hbody ih =>
    cases h₂
    -- Caso 4.1
    case eta_red lc_m₂ =>
      rcases eta_redex_body lc_m₂ hbody with ⟨t', r_m₂_t', ht₁⟩
      rewrite [ht₁]
      use t'
      constructor
      · apply clos_refl.step
        exact eta.eta_red (eta_lc_right r_m₂_t')
      · exact clos_refl.step m₂ t' r_m₂_t'
    -- Caso 4.2
    case eta_abs => sorry

theorem church_rosser : confluent eta := by
  unfold confluent
  rewrite [clos_refl_trans_eq]
  apply diamond_clos_trans
  intro m m₁ m₂ h₁ h₂
  cases h₁
  -- Caso 1
  case refl =>
    use m₂
    constructor
    · exact h₂
    · exact clos_refl.refl m₂
  -- Caso 2
  case step hstep₁ =>
    cases h₂
    -- Caso 2.1
    case refl =>
      use m₁
      constructor
      · exact clos_refl.refl m₁
      · exact clos_refl.step m m₁ hstep₁
    -- Caso 2.2
    case step hstep₂ =>
      exact eta_diamond m m₁ m₂ hstep₁ hstep₂

end trm
