import Dcc.Judge3

universe u
variable {τ_c : Type u} [DecidableEq τ_c]

namespace GenericExpr

def DefEq.symm {A B : GenericExpr τ_c} (h₁ : A ≡ B) : B ≡ A := by sorry

def DefEq.trans {A B C : GenericExpr τ_c} (h₁ : A ≡ B) (h₂ : B ≡ C) : A ≡ C := by sorry

def DefEq.push_head {A B : GenericExpr τ_c} (hr : RedAff A B) : A ≡ B := by sorry

def Reduces.to_defeq {A B : GenericExpr τ_c} (h : Reduces A B) : A ≡ B := by sorry

open Dsl in
inductive StepHead : GenericExpr τ_c → GenericExpr τ_c → Type u
/-
Core reductions:
-/
  | dup            : StepHead (DCC? ((Dup B x) (& env) (& y))) (DCC? (x env (,(`(B env) (B env)) y y)))
  | bimap          : StepHead (DCC? ((Map A B f g) (,_B x y))) (DCC? (,(`A B) (f x) (g y)))
  | assoc          : StepHead (DCC? ((Assoc A B C) (,_B₁ (,_B₂ x y) z))) (DCC? (,(`A (Σ (`B C))) x (,(`B C) y z)))
  | eql            : StepHead (DCC? ((Eql f_α) env (,B x y))) (DCC? (= (f_α env) x y))
  | map            : StepHead (DCC? ((!<> f) (& x))) (DCC? (!(f x)))
  | fmap           : StepHead (DCC? (($<> f) (& x))) (DCC? (& (f x)))
  | unbox          : StepHead (DCC? ((* A) (& x))) x
  | pair           : StepHead (DCC? ((⟨,⟩β M N) (& x))) (DCC? (,(β x) (M x) (N x (M x))))
  | evalc          : StepHead (DCC? ((Eval _α _β x) (,__β y z))) (DCC? (x y z))
  | quot           : StepHead (DCC? ((`β x) y)) x
  | id             : StepHead (DCC? ((Id α) x)) x
  | fstc           : StepHead (DCC? ((Fst _α) (,β a b))) a
  | sndc           : StepHead (DCC? ((Snd _α) (,β a b))) b
  | comp           : StepHead (DCC? ((∘ x y) z)) (DCC? (x (y z)))
  | curr           : StepHead (DCC? ((Λ α β x) y z)) (DCC? (x (,β y z)))
  | curr'          : StepHead (DCC? ((!Λα β x) (& y) (& z))) (DCC? (x (& (,β y z))))
  | sigma          : StepHead (DCC? ((Σ f_α f_β) env)) (DCC? ((Σ (f_β env))))
  | swap           : StepHead (DCC? ((Swap A B) (,B₂ x y))) (DCC? (,(`B A) y x))
  | ind_bool_true  : StepHead (DCC? ((Bool.Rec motive x y) env True)) (DCC? (x env True))
  | ind_bool_false : StepHead (DCC? ((Bool.Rec motive x y) env False)) (DCC? (y env False))
  | cong_1         : StepHead (DCC? ((≃.1 A B) ((≃.mk fX fY fidl fidr) env₂))) (DCC? (fX env₂))
  | cong_2         : StepHead (DCC? ((≃.2 A B) ((≃.mk fX fY fidl fidr) env₂))) (DCC? (fY env₂))
  | cong_3         : StepHead (DCC? ((≃.3 A B) (& ((≃.mk fX fY fidl fidr) env₂)))) (DCC? (fidl (& env₂)))
  | cong_4         : StepHead (DCC? ((≃.4 A B) (& ((≃.mk fX fY fidl fidr) env₂)))) (DCC? (fidr (& env₂)))

def Judge.preservation_id
  (ht : Judge (τ_c := τ_c) (DCC? ((Id A) x)) τ) : Σ' (τ_x : GenericExpr τ_c) (_ht_x : Judge x τ_x), τ_x ≡ τ := by
  cases ht with
  | app =>
    expose_names
    cases a_1 with
    | id =>
      expose_names
      have h₁ := ((a_3.push_head (.congrFun .quot)).push_head .quot).to_defeq
      exact ⟨_, a_2, a.symm.trans (.trans (.push_head .id) h₁)⟩

/-def Judge.preservation_step
  (ht : Judge (τ_c := τ_c) (DCC? (f x)) τ)
  (hr : StepHead (DCC? (f x)) e') : Judge e' τ := by
  cases ht with
  | app =>
    expose_names
    cases hr with
    | id =>
      
      sorry-/

end GenericExpr

/-
RedAffNorm is not necessary before unify in ≡.

Really want subject reduction lemma to work. Most important thing, I think.
Do it on StepHead.

As many Reduces should be removed from type conclusions.
-/
