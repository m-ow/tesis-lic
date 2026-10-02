import Mathlib.tactic

set_option linter.style.header false

def relation (X : Type) := X → X → Prop

variable {X : Type}

def reflexive (R : relation X) : Prop :=
  ∀ a : X, R a a

def transitive (R : relation X) : Prop :=
  ∀ a b c : X, R a b → R b c → R a c

inductive clos_refl (R : relation X) : relation X
  | refl : ∀ a : X,
      clos_refl R a a
  | step : ∀ a b : X,
      R a b → clos_refl R a b

inductive clos_trans (R : relation X) : relation X
  | step : ∀ a b : X,
      R a b → clos_trans R a b
  | trans : ∀ a b c : X,
      clos_trans R a b → clos_trans R b c →
      clos_trans R a c

inductive clos_refl_trans (R : relation X) : relation X
  | refl : ∀ a : X,
      clos_refl_trans R a a
  | step : ∀ a b : X,
      R a b → clos_refl_trans R a b
  | trans : ∀ a b c : X,
      clos_refl_trans R a b → clos_refl_trans R b c →
      clos_refl_trans R a c

lemma to_trans_refl {a b : X} {R : relation X} :
    clos_refl_trans R a b → clos_trans (clos_refl R) a b := by
  intro h
  induction h with
  | refl a =>
      apply clos_trans.step a a
      exact .refl a
  | step a b hab =>
      apply clos_trans.step a b
      exact clos_refl.step a b hab
  | trans a b c hab hbc ih₁ ih₂ =>
      exact .trans a b c ih₁ ih₂

lemma to_reflTrans {a b : X} {R : relation X} :
    clos_trans (clos_refl R) a b → clos_refl_trans R a b := by
  intro h
  induction h with
  | step a b hr =>
    cases hr with
    | refl a =>
        exact .refl a
    | step a b hab =>
        exact .step a b hab
  | trans a b c hab hbc ih₁ ih₂ =>
      exact .trans a b c ih₁ ih₂

lemma clos_refl_trans_eq : ∀ R : relation X,
    clos_refl_trans R = clos_trans (clos_refl R) := by
  intro R
  funext a b
  apply propext
  exact ⟨to_trans_refl, to_reflTrans⟩

def diamond (R : relation X) : Prop :=
  ∀ m m₁ m₂ : X, R m m₁ → R m m₂ → ∃ m₃ : X, R m₁ m₃ ∧ R m₂ m₃

def confluent (R : relation X) : Prop :=
  diamond (clos_refl_trans R)

lemma diamond_step_trans {R : relation X} (h : diamond R) :
    ∀ a b c : X, clos_trans R a b → R a c → ∃ d : X, R b d ∧ clos_trans R c d := by
  intro a b c hab hac
  induction hab generalizing c with
  | step a b hab =>
      have ⟨d, hbd, hcd⟩ := h a b c hab hac
      use d
      constructor
      · exact hbd
      · exact .step c d hcd
  | trans a b c' hab hbc' ih₁ ih₂ =>
      have ⟨d, hbd, hcd⟩ := ih₁ c hac
      have ⟨e, hc'e, hde⟩ := ih₂ d hbd
      use e
      constructor
      · exact hc'e
      · exact .trans c d e hcd hde

lemma diamond_clos_trans {R : relation X} :
    diamond R →
    diamond (clos_trans R) := by
  intro h a b c hab hac
  induction hac generalizing b with
  | step a c hac =>
      have ⟨d, hbd, hcd⟩ := diamond_step_trans h a b c hab hac
      use d
      constructor
      · exact .step b d hbd
      · exact hcd
  | trans a b' c hab' hb'c ih₁ ih₂ =>
      have ⟨d, hbd, hb'd⟩ := ih₁ b hab
      have ⟨e, hde, hce⟩ := ih₂ d hb'd
      use e
      constructor
      · exact .trans b d e hbd hde
      · exact hce
