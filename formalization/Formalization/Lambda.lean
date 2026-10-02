import Formalization.relations

set_option linter.style.header false

inductive trm : Type
  | bvar : ℕ → trm
  | fvar : String → trm
  | abs  : trm → trm
  | app  : trm → trm → trm

namespace trm

instance : Coe String trm where
  coe := fvar

instance (n : ℕ) : OfNat trm n where
  ofNat := bvar n

def fv (t : trm) : Finset String :=
  match t with
  | bvar _    => ∅
  | fvar x    => {x}
  | app t₁ t₂ => fv t₁ ∪ fv t₂
  | abs u     => fv u

def open_rec (k : ℕ) (x : String) (t : trm) : trm :=
  match t with
  | bvar i    => if i = k then fvar x else bvar i
  | fvar y    => fvar y
  | app t₁ t₂ => app (open_rec k x t₁) (open_rec k x t₂)
  | abs t     => abs (open_rec (k + 1) x t)

notation "{" k " ~> " x "} " t => open_rec k x t

def open_var (t : trm) (x : String) : trm :=
  {0 ~> x} t

infixl:80 " ^ " => open_var

example :
  (app (abs (app 0 1)) 0) ^ "x" = (app (abs (app 0 "x")) "x") := rfl

inductive lc : trm → Prop
  | lc_var (x : String) :
      lc (fvar x)
  | lc_app {t₁ t₂ : trm} :
      lc t₁ → lc t₂ → lc (app t₁ t₂)
  | lc_abs (L : Finset String) (t : trm) :
      (∀ x ∉ L, lc (t ^ x)) →
      lc (abs t)

def close_var_rec (k : ℕ) (x : String) (t : trm) : trm :=
  match t with
  | bvar i    => bvar i
  | fvar y    => if x = y then bvar k else fvar y
  | app t₁ t₂ => app (close_var_rec k x t₁) (close_var_rec k x t₂)
  | abs t     => abs (close_var_rec (k + 1) x t)

notation "{" k " <~ " x "} " t => close_var_rec k x t

def close_var (t : trm) (x : String) : trm :=
  {0 <~ x} t

infixl:80 " ^* " => close_var

example :
  (app (abs (app 0 "x")) "x") ^* "x" = (app (abs (app 0 1)) 0) := rfl

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
    eta t t' → lc t':= by
  intro h
  induction h with
  | eta_red ht => exact ht
  | eta_app1 ht₂ hstep ih => exact lc.lc_app ih ht₂
  | eta_app2 ht₁ hstep ih => exact lc.lc_app ht₁ ih
  | eta_abs L hsteps ih => exact lc.lc_abs L _ ih

lemma refl_app1 {t₁ t₁' t₂ : trm} :
    lc t₂ →
    clos_refl eta t₁ t₁' →
    clos_refl eta (app t₁ t₂) (app t₁' t₂) := by
  intro lc_t₂ h_red
  cases h_red with
  | refl t₁ => exact .refl (t₁.app t₂)
  | step t₁ t₁' h => exact .step (t₁.app t₂) (t₁'.app t₂) (.eta_app1 lc_t₂ h)

lemma refl_app2 {t₁ t₂ t₂' : trm} :
    lc t₁ →
    clos_refl eta t₂ t₂' →
    clos_refl eta (app t₁ t₂) (app t₁ t₂') := by
  intro lc_t₁ h_red
  cases h_red with
  | refl t₂ => exact .refl (t₁.app t₂)
  | step t₂ t₂' h => exact .step (t₁.app t₂) (t₁.app t₂') (.eta_app2 lc_t₁ h)

lemma eta_redex_body {L : Finset String} {t u : trm} :
    lc t →
    (∀ x ∉ L, eta ((app t (bvar 0)) ^ x) (u ^ x)) →
    ∃ t', eta t t' ∧ u = app t' (bvar 0) := sorry

end trm
