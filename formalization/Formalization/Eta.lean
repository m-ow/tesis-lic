import Formalization.Lambda

set_option linter.style.header false

namespace trm

inductive eta : relation trm
  | eta_red {t : trm} :
      lc t →
      eta (abs (app t (bvar 0))) t
  | eta_app1 {t₁ t₁' t₂ : trm} :
      lc t₂ →
      eta t₁ t₁' →
      eta (app t₁ t₂) (app t₁' t₂)
  | eta_app2 {t₁ t₂ t₂' : trm} :
      lc t₁ →
      eta t₂ t₂' →
      eta (app t₁ t₂) (app t₁ t₂')
  | eta_abs (L : Finset String) {t t' : trm} :
      (∀ x, x ∉ L → eta (t ^ x) (t' ^ x)) →
      eta (abs t) (abs t')

lemma eta_lc_right {t t' : trm} :
    eta t t' → lc t' := by
  intro h
  induction h with
  | eta_red ht =>
      exact ht
  | eta_app1 ht₂ hstep ih =>
      exact lc.lc_app ih ht₂
  | eta_app2 ht₁ hstep ih =>
      exact lc.lc_app ht₁ ih
  | eta_abs L hsteps ih =>
      exact lc.lc_abs L _ ih

lemma refl_app1 {t₁ t₁' t₂ : trm} :
    lc t₂ →
    clos_refl eta t₁ t₁' →
    clos_refl eta (app t₁ t₂) (app t₁' t₂) := by
  intro lc_t₂ h_red
  cases h_red with
  | refl t₁ =>
      exact .refl (app t₁ t₂)
  | step t₁ t₁' h =>
      exact .step (app t₁ t₂) (app t₁' t₂) (.eta_app1 lc_t₂ h)

lemma refl_app2 {t₁ t₂ t₂' : trm} :
    lc t₁ →
    clos_refl eta t₂ t₂' →
    clos_refl eta (app t₁ t₂) (app t₁ t₂') := by
  intro lc_t₁ h_red
  cases h_red with
  | refl t₂ =>
      exact .refl (app t₁ t₂)
  | step t₂ t₂' h =>
      exact .step (app t₁ t₂) (app t₁ t₂') (.eta_app2 lc_t₁ h)

lemma eta_redex_body {L : Finset String} {t u : trm} :
    lc t →
    (∀ x ∉ L, eta ((app t (bvar 0)) ^ x) (u ^ x)) →
    ∃ t', eta t t' ∧ u = app t' (bvar 0) := sorry

end trm
