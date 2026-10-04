import Formalization.Relations

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

lemma exists_fresh : ∀ L : Finset String,
    ∃ x, x ∉ L := by
  intro L
  exact Infinite.exists_notMem_finset L

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

infixl:80 " ^\\ " => close_var

example :
  (app (abs (app 0 "x")) "x") ^\ "x" = (app (abs (app 0 1)) 0) := rfl

lemma close_open (x : String) (t : trm) (k : ℕ) :
    x ∉ fv t →
    close_var_rec k x (open_rec k x t) = t := by
  induction t generalizing k <;> grind [open_rec, close_var_rec, fv]

lemma close_open_var {x : String} {t : trm} :
    x ∉ fv t →
    (t ^ x) ^\ x = t := by
  intro hx
  exact close_open x t 0 hx

end trm
