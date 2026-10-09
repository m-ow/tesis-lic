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
      (∀ x ∉ L, eta (t ^ x) (t' ^ x)) →
      eta (abs t) (abs t')

lemma lc_eta_redex {t : trm} :
    lc t → lc (abs (app t (bvar 0))) := by
  intro ht
  apply lc.lc_abs ∅
  intro x hx
  change lc (app (t ^ x) (fvar x))
  rewrite [open_var_lc ht]
  exact lc.lc_app ht (lc.lc_var x)

lemma eta_lc_left {t t' : trm} :
    eta t t' → lc t := by
  intro h
  induction h
  case eta_red t ht =>
    exact lc_eta_redex ht
  case eta_app1 t₁ t₁' t₂ ht₂ hstep ih =>
    exact lc.lc_app ih ht₂
  case eta_app2 t₁ t₂ t₂' ht₁ hstep ih =>
    exact lc.lc_app ht₁ ih
  case eta_abs L t t' hbody ih =>
    exact lc.lc_abs L t ih

lemma eta_lc_right {t t' : trm} :
    eta t t' → lc t' := by
  intro h
  induction h
  case eta_red t ht =>
    exact ht
  case eta_app1 t₁ t₁' t₂ ht₂ hstep ih =>
    exact lc.lc_app ih ht₂
  case eta_app2 t₁ t₂ t₂' ht₁ hstep ih =>
    exact lc.lc_app ht₁ ih
  case eta_abs L t t' hbody ih =>
    exact lc.lc_abs L t' ih

lemma eta_regular {r s : trm} :
    eta r s → lc r ∧ lc s := by
  intro h
  exact ⟨eta_lc_left h, eta_lc_right h⟩

lemma eta_fv_eq {r s : trm} :
    eta r s → fv r = fv s := by
  intro h
  induction h
  case eta_red t ht =>
    simp only [fv, Finset.union_empty]
  case eta_app1 t₁ t₁' t₂ ht₂ hstep ih =>
    change fv t₁ ∪ fv t₂ = fv t₁' ∪ fv t₂
    rw [ih]
  case eta_app2 t₁ t₂ t₂' ht₁ hstep ih =>
    change fv t₁ ∪ fv t₂ = fv t₁ ∪ fv t₂'
    rw [ih]
  case eta_abs L t u hbody ih =>
    change fv t = fv u
    apply Finset.ext
    intro x
    rcases exists_fresh (L ∪ {x}) with ⟨y, hy⟩
    have hxy : x ≠ y := by grind
    have hL : y ∉ L := by grind
    have hfv := ih y hL
    have hmem : x ∈ fv (t ^ y) ↔ x ∈ fv (u ^ y) := by
      rw [hfv]
    simpa only [open_var, mem_fv_open_rec hxy] using hmem

lemma refl_app1 {t₁ t₁' t₂ : trm} :
    lc t₂ →
    clos_refl eta t₁ t₁' →
    clos_refl eta (app t₁ t₂) (app t₁' t₂) := by
  intro ht₂ h
  cases h
  case refl =>
    exact clos_refl.refl (app t₁ t₂)
  case step hstep =>
    exact clos_refl.step (app t₁ t₂) (app t₁' t₂) (eta.eta_app1 ht₂ hstep)

lemma refl_app2 {t₁ t₂ t₂' : trm} :
    lc t₁ →
    clos_refl eta t₂ t₂' →
    clos_refl eta (app t₁ t₂) (app t₁ t₂') := by
  intro ht₁ h
  cases h
  case refl =>
    exact clos_refl.refl (app t₁ t₂)
  case step hstep =>
    exact clos_refl.step (app t₁ t₂) (app t₁ t₂') (eta.eta_app2 ht₁ hstep)

lemma eta_app_fvar_inv {t u : trm} {x : String} :
    eta (app t (fvar x)) u →
    ∃ t', eta t t' ∧ u = app t' (fvar x) := by
  intro h
  cases h
  case eta_app1 t' hstep lc_x =>
    exact ⟨t', hstep, rfl⟩
  case eta_app2 u' ht hstep =>
    cases hstep

lemma eta_redex_body {L : Finset String} {t u : trm} :
    lc t →
    (∀ x ∉ L, eta ((app t (bvar 0)) ^ x) (u ^ x)) →
    ∃ t', eta t t' ∧ u = app t' (bvar 0) := sorry

end trm
