import Dcc.Attrs
import Dcc.Ast
import Dcc.Relation
import Dcc.Aff.Size
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

namespace GenericExpr

open Dsl

universe u
variable {τ : Type u} [DecidableEq τ]

abbrev TUnif (u v : Level) (A B : GenericExpr τ) : GenericExpr τ := (DCC? (Σ ((Bool.Ind (`⊤ (`Bool (Sort (max u v)))) (`⊤ (`Bool (A ≃ B))) (`⊤ (`Bool ((A ≃ B) ≃ ⊥)))) ∗)))

/-
Easier rules before 
-/

--abbrev unif_fn (u v : Level) (B₁ C₁ x₁ B₂ C₂ x₂ : GenericExpr τ) : GenericExpr τ :=
  /-let t_out            := (TUnif u v (DCC? ((Π B₁ C₁) x₁)) (DCC? ((Π B₂ C₂) x₂)))
  let bool_ind_motive  := (DCC? (`⊤ (`Bool t_out)))
  let t_cod_eq         := (DCC? (C₁ x₁) ≃ (C₂ x₂))
  (DCC? (((Bool.Ind bool_ind_motive
                    (≃.mk (Λ t_cod_eq
                              (`t_cod_eq ((Π B₁ C₁) x₁))
                              (-- (h₁ : (C₁ x₁) ≃ (C₂ x₂), f : ((Π B₁ c₁) x₁)), prove ((Π B₂ C₂) x₂), so also x : (B₂ x₂)
                              (Λ (Σ (`t_cod_eq ((Π B₁ C₁) x₁)))
                                 (`(Σ (`t_cod_eq ((Π B₁ C₁) x₁))) (B₂ x₂))
                                 (-- ((h₁ : (C₁ x₁) ≃ (C₂ x₂), f : ((Π B₁ c₁) x₁)), x : (B₂ x₂)), so 
                                 ))
                              ))
                           ()
                           ()
                           ())  -- (C₁ x₁) ≃ (C₂ x₂), prove ((Π B₁ C₁) x₁) ≃ ((Π B₂ C₂) x₂)
                    ()
                    ())
           ∗
           (Unify (? 1) (? 2) (C₁ x₁) (C₂ x₂))))-/
/-abbrev unif_fn (u v : Level) (B₁ C₁ x₁ B₂ C₂ x₂ : GenericExpr τ) : GenericExpr τ :=
  let t_out            := (TUnif u v (DCC? ((Π B₁ C₁) x₁)) (DCC? ((Π B₂ C₂) x₂)))
  let t_out_false      := DCC? (((Π B₁ C₁) x₁) ≃ ((Π B₂ C₂) x₂)) ≃ ⊥
  let t_out_false_fst  := DCC? (((Π B₁ C₁) x₁) ≃ ((Π B₂ C₂) x₂))
  let bool_ind_motive  := (DCC? (`⊤ (`Bool t_out)))
  let t_eq_fst_true    := (DCC? ((B₁ x₁) ≃ (B₂ x₂)))
  let t_eq_fst_false   := (DCC? ((B₁ x₁) ≃ (B₂ x₂)) ≃ ⊥)
  let with_B₁x₁_eq_B₂x₂ (e : GenericExpr τ) : GenericExpr τ :=
    (DCC? (((Bool.Ind bool_ind_motive
                     (`⊤ e) -- (B₁ x₁) ≃ (B₂ x₂), ((Π B₁ C₁) x₁), (B₂ x₂)
                     (∘ ((Λ Bool (`Bool t_out_false) (Id (Σ (`Bool t_out_false)))) False)
                        (≃.mk (`t_eq_fst_false t_out_false_fst)
                               (`t_eq_fs_falset ⊥)
                               (Λ t_eq_fst_false
                                  (`t_eq_fst_false t_out_false_fst)
                                  (∘ () (Fst (`t_eq_fst_false t_out_false_fst)))) -- (DCC? ((B₁ x₁) ≃ (B₂ x₂)) ≃ ⊥), (((Π B₁ C₁) x₁) ≃ ((Π B₂ C₂) x₂)), prove ⊥
                               ())))) -- ((B₁ x₁) ≃ (B₂ x₂)) ≃ ⊥, prove (((Π B₁ C₁) x₁) ≃ ((Π B₂ C₂) x₂)) ≃ ⊥
                     -- ^ this is equivalent to showing (B₁ x₁) is inhabited
                     -- but since (((Π B₁ C₁) x₁) ≃ ((Π B₂ C₂) x₂)), then ((B₁ x₁) ≃ (B₂ x₂))
                     -- which should be solvable with reflexivity
           (Unify (Dom (C₁ x₁)) (Dom (C₂ x₂)) (B₁ x₁) (B₂ x₂))) ∗))
  with_B₁x₁_eq_B₂x₂ (by sorry)-/

/-
Preservation proof:
- can make these more type-directed

Id(A) ∘ Fst(Id(A))

Fst(B) ∘ Id(Coup(Id(A)))
-/

/-
Funext:

-/

@[aesop safe (rule_sets := [DccForceStep]) [constructors], aesop unsafe 50% (rule_sets := [DccForceStep]) [cases]]
inductive RedAff : GenericExpr τ → GenericExpr τ → Prop
/-
Core reductions:
-/
  | eql            : RedAff (DCC? ((Eql f_α) (& env) (& x))) (DCC? x = x)
  | map            : RedAff (DCC? ((!<> f) (& x))) (DCC? (!(f x)))
  | fmap           : RedAff (DCC? (($<> f) (& x))) (DCC? (& (f x)))
  | unbox          : RedAff (DCC? ((* A) (& x))) x
  | pair           : RedAff (DCC? ((⟨,⟩β M N) (& x))) (DCC? (,(β x) (M x) (N x (M x))))
  | evalc          : RedAff (DCC? ((Eval _α _β x) (,__β y z))) (DCC? (x y z))
  | quot           : RedAff (DCC? ((`β x) y)) x
  | id             : RedAff (DCC? ((Id α) x)) x
  | fstc           : RedAff (DCC? ((Fst _α) (,β a b))) a
  | sndc           : RedAff (DCC? ((Snd _α) (,β a b))) b
  | comp           : RedAff (DCC? ((∘ x y) z)) (DCC? (x (y z)))
  | curr           : RedAff (DCC? ((Λ α β x) y z)) (DCC? (x (,β y z)))
  | curr'          : RedAff (DCC? ((!Λα β x) (& y) (& z))) (DCC? (x (& (,β y z))))
  | sigma          : RedAff (DCC? ((Σ f_α f_β) env)) (DCC? ((Σ (f_β env))))
  | swap           : RedAff (DCC? ((Swap A B) (,B₂ x y))) (DCC? (,(`B A) y x))
  | ind_bool_true  : RedAff (DCC? ((Bool.Ind motive x y) env True)) (DCC? (x env True))
  | ind_bool_false : RedAff (DCC? ((Bool.Ind motive x y) env False)) (DCC? (y env False))
  | cong_1         : RedAff (DCC? (((≃.1 f_x B) env₁) ((≃.mk fX fY fidl fidr) env₂))) (DCC? ((fX env₂) (f_x env₁)))
  | cong_2         : RedAff (DCC? (((≃.2 B f_x) env₁) ((≃.mk fX fY fidl fidr) env₂))) (DCC? ((fY env₂) (f_x env₁)))
  | cong_3         : RedAff (DCC? (((≃.3 f_x B) env₁) ((≃.mk fX fY fidl fidr) env₂))) (DCC? ((fidl env₂) (f_x env₁)))
  | cong_4         : RedAff (DCC? (((≃.4 B f_x) env₁) ((≃.mk fX fY fidl fidr) env₂))) (DCC? ((fidr env₂) (f_x env₁)))
/-
Inner congruences:
-/
-- `(B, x)
  | point : (n : ℕ) → (h : n < point_arity e) → RedAff ((points e).get ⟨n, h⟩) p' → RedAff e (e.set_points ((points e).set n p'))
/-
App congruence:
-/
  | congrFun : RedAff f f' → RedAff (DCC? (f x)) (DCC? (f' x))
  | congrArg : RedAff x x' → RedAff (DCC? (f x)) (DCC? (f x'))
/-
Base combinator function domains
-/
  | eqlτ₀    : RedAff (DCC? (Dom (Eql B))) (DCC? (! (Dom B)))
  | reflτ₀   : RedAff (DCC? (Dom (refl B))) (DCC? (! (Dom B)))
  | mapτ₀    : RedAff (DCC? (Dom (!<> x))) (DCC? (! (Dom x)))
  | fmapτ₀   : RedAff (DCC? (Dom ($<> x))) (DCC? (! (Dom x)))
  | unboxτ₀  : RedAff (DCC? (Dom (* A))) (DCC? (! A))
  | pairτ₀   : RedAff (DCC? (Dom (⟨,⟩B x y))) (DCC? (! (Dom x)))
  | evalcτ₀  : RedAff (DCC? (Dom (Eval A B x))) (DCC? (Σ B))
  | quotτ₀   : RedAff (DCC? (Dom (`B x))) B
  | idτ₀     : RedAff (DCC? (Dom (Id A))) A
  | fstcτ₀   : RedAff (DCC? (Dom (Fst B))) (DCC? (Σ B))
  | sndcτ₀   : RedAff (DCC? (Dom (Snd B))) (DCC? (Σ B))
  | compτ₀   : RedAff (DCC? (Dom (∘ x y))) (DCC? (Dom y))
  -- x : (x : Coup(B)) -> ...., explicitly recurisng here is important since it
  -- is the only partial app possible
  | currτ₀   : RedAff (DCC? (Dom (Λ A B x))) (DCC? (Dom (Uncoup (Dom x))))
  | curr'τ₀  : RedAff (DCC? (Dom (!Λ A B x))) (DCC? (! (Dom (Uncoup (Unbang (Dom x))))))
  | sigmaτ₀  : RedAff (DCC? (Dom (Σ B C))) (DCC? (Dom C))
  | piτ₀     : RedAff (DCC? (Dom (Π B C))) (DCC? (Dom C))
  | eqlτ₁    : RedAff (DCC? (Dom ((Eql B) (& x)))) (DCC? (! (B x)))
  | reflτ₁   : RedAff (DCC? (Dom ((refl B) (& x)))) (DCC? (! (B x)))
  | currτ₁   : RedAff (DCC? (Dom ((Λ A B x) y))) (DCC? (((Uncoup (Dom x)) y)))
  | curr'τ₁  : RedAff (DCC? (Dom ((!Λ A B x) (& y)))) (DCC? ((! ((Uncoup (Unbang (Dom x))) y))))
  -- C : (x : A) → (y : B x) → Sort v
  -- where x is the second element such that Swap(C) ⟦...⟧(x, y) : Coup((C x)) and C x : y -> ...
  | swapτ₀   : RedAff (DCC? (Dom (Swap B C))) (DCC? (! (Σ B)))
/-
Dom congruence
-/
  | dom₀    : RedAff x x' → RedAff (DCC? (Dom x)) (DCC? (Dom x'))
/-
Matching Coup for Dom
-/
  | uncoup  : RedAff (DCC? (Uncoup (Σ x))) x
  | unbang  : RedAff (DCC? (Unbang (! x))) x
/-
Matchers congruence (matchers only used by the kernel in η-reduction
-/
  | uncoup₀ : RedAff x x' → RedAff (DCC? (Uncoup x)) (DCC? (Uncoup x'))
  | unbang₀ : RedAff x x' → RedAff (DCC? (Unbang x)) (DCC? (Unbang x'))
/-
Base combinator 2-argument function domains
-/
  | eqlτ₃   : RedAff (DCC? (Dom₂ (Eql B))) (DCC? (!<> B))
  | reflτ₃  : RedAff (DCC? (Dom₂ (refl B))) (DCC? (!<> B))
  | currτ₃  : RedAff (DCC? (Dom₂ (Λ A B x))) B
  | curr'τ₃ : RedAff (DCC? (Dom₂ (!Λ A B x))) (DCC? (!<> B))
-- Congruence for Dom₂
  | dom₂₀   : RedAff x x' → RedAff (DCC? (Dom₂ x)) (DCC? (Dom₂ x'))
/-
  Unifications:
-/
  -- A ≃ A = Id
  | unif_refl : RedAff (DCC? (Unify τ_A₁ τ_A₂ A A)) (DCC? (,(`Bool (A ≃ A)) True ((≃.mk (`⊤ (Id A)) (`⊤ (Id A)) (`⊤ ((refl (Id τ_A₁)) (&A))) (`⊤ ((refl (Id τ_A₂)) (&A)))) ∗)))
  /-
    (X ≃ ⊥) ≃ ⊥:
    - (Sort (m + 1) ≃ ⊥) ≃ ⊥
    - (Sort 0 ≃ ⊥) ≃ ⊥, by ⊤
    - 
  -/
  | unif_bot_sort : RedAff (DCC? (Unify τ_A τ_B (Sort (m + 1)) ⊥))
    (DCC? (,(`Bool (((Sort (m + 1)) ≃ ⊥) ≃ ⊥)) False ((≃.mk (`⊤ ((≃.1 (`⊤ (Sort m)) (`⊤ ⊥)) ∗)) (`⊤ ((⊥.Ind (`⊤ (`⊥ ((Sort (m + 1)) ≃ ⊥)))) ∗)) (`⊤ ((refl (Id τ_A)) (& (Sort (m + 1))))) (`⊤ ((refl (Id τ_B)) (& ⊥)))) ∗)))
  | unif_bot_prop : RedAff (DCC? (Unify τ_A τ_B (Sort 0) ⊥))
    (DCC? (,(`Bool (((Sort 0) ≃ ⊥) ≃ ⊥)) False ((≃.mk (`⊤ ((≃.1 (`⊤ ⊤) (`⊤ ⊥)) ∗)) (`⊤ ((⊥.Ind (`⊤ (`⊥ ((Sort 0) ≃ ⊥)))) ∗)) (`⊤ ((refl (Id τ_A)) (& (Sort 0)))) (`⊤ ((refl (Id τ_B)) (& ⊥)))) ∗)))
  /-
    Function unification:
    ((Π B₁ C₁) x₁) with ((Π B₂ C₂) x₂)
    can we do with just h₁
    (mk (fun f => f ∘ unify((B₁ x₁), (B₂ x₂)).2) (fun f => f ∘ unify((B₁ x₁), (B₂ x₂)).1) (? : ((unify((B₁ x₁), (B₂ x₂)).2) ·) ∘ ((unify((B₁ x₁), (B₂ x₂)).1 x) ·) = id)
    we arleady know the two A's are equal
    so we just want to send the codomain g' := (unify(C₁ x₁, C₂ x₂).1 ∘ f)
    (unify(C₁ x₁, C₂ x₂).2 ∘ (unify(C₁ x₁, C₂ x₂).1 ∘ f)) = f. that's perfect. just a notational game.

    comp_id is (to_fun ∘ inv_fun) f = (∘ unify(C₁ x₁, C₂ x₂).2) ∘ (∘ unify(C₁ x₁, C₂ x₂).1) f = (∘ unify(C₁ x₁, C₂ x₂).2) (unify(C₁ x₁, C₂ x₂).1 f) = f

    maybe we just need an identity for composed unification?

    we cannot unify (C₁ x₁) with (C₂ x₂) since we don't have a domain to plug them into.
    we can unify with hole. this is super ugly though.
  -/
  /-| unif_fn : RedAff (DCC? (Unify (Sort u) (Sort v) ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂)))
    (DCC? (((Bool.Ind (`⊤ (`Bool #(TUnif u v (DCC? ((Π B₁ C₁) x₁)) (DCC? ((Π B₂ C₂) x₂)))))
                     (`⊤ (`(B₁ ≃ x₁)
                           ((Bool.Ind (`⊤ (`Bool (#(TUnif u v (DCC? ((Π B₁ C₁) x₁)) (DCC? ((Π B₂ C₂) x₂))))))) ∗))) -- (B₁ x₁) ≃ (B₂ x₂), ((Π B₁ C₁) x₁), (B₂ x₂)
                     ()) -- ((B₁ x₁) ≃ (B₂ x₂)) ≃ ⊥)
           (Unify (Dom (C₁ x₁)) (Dom (C₂ x₂)) (B₁ x₁) (B₂ x₂))) ∗))-/

instance (A B : GenericExpr τ) : Repr (PLift (RedAff A B)) := ⟨fun _ _ => "⋯"⟩

@[dcc_force_reduce, dcc_force_aff, aesop unsafe norm (rule_sets := [DccForceReduce])]
def step? (e : GenericExpr τ) : Option ((e' : GenericExpr τ) × (PULift.{u + 1, 0} (RedAff (τ := τ) e e'))) :=
  match e with
  | (DCC? ((Bool.Ind motive x y) env True)) =>
    .some ⟨_, ⟨.ind_bool_true⟩⟩
  | (DCC? ((Bool.Ind motive x y) env False)) =>
    .some ⟨_, ⟨.ind_bool_false⟩⟩
  | (DCC? (Unify τ_A τ_B (Sort (m + 1)) ⊥)) =>
    .some ⟨_, ⟨.unif_bot_sort⟩⟩
  | (DCC? (Unify τ_A τ_B (Sort 0) ⊥)) =>
    .some ⟨_, ⟨.unif_bot_prop⟩⟩
  | (DCC? (((≃.1 f_x B) env₁) ((≃.mk fX fY fidl fidr) env₂))) =>
    .some ⟨_, ⟨.cong_1⟩⟩
  | (DCC? (((≃.2 B f_x) env₁) ((≃.mk fX fY fidl fidr) env₂))) =>
    .some ⟨_, ⟨.cong_2⟩⟩
  | (DCC? (((≃.3 f_x B) env₁) ((≃.mk fX fY fidl fidr) env₂))) =>
    .some ⟨_, ⟨.cong_3⟩⟩
  | (DCC? (((≃.4 B f_x) env₁) ((≃.mk fX fY fidl fidr) env₂))) =>
    .some ⟨_, ⟨.cong_4⟩⟩
  | (DCC? (Unify τ_A₁ τ_A₂ A B)) =>
    if heq : A = B then
      heq ▸ .some ⟨_, ⟨RedAff.unif_refl⟩⟩
    else
      match τ_A₁.step?, τ_A₂.step? with
      | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.point 0 (by grind) h₁⟩⟩
      | _, .some ⟨_, ⟨h₂⟩⟩ => .some ⟨_, ⟨.point 1 (by grind) h₂⟩⟩
      | _, _ =>
        match A.step?, B.step? with
        | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.point 2 (by grind) h₁⟩⟩
        | _, .some ⟨_, ⟨h₂⟩⟩ => .some ⟨_, ⟨.point 3 (by grind) h₂⟩⟩
        | _, _ => .none
  | DCC? (Bool.Ind motive x y) =>
    match motive.step?, x.step? with
    | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.point 0 (by grind) h₁⟩⟩
    | _, .some ⟨_, ⟨h₂⟩⟩ => .some ⟨_, ⟨.point 1 (by grind) h₂⟩⟩
    | _, _ =>
      match y.step? with
      | .some ⟨_, ⟨h₃⟩⟩ => .some ⟨_, ⟨.point 2 (by grind) h₃⟩⟩
      | .none => .none
  | DCC? (≃.Ind motive x) =>
    match motive.step?, x.step? with
    | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.point 0 (by grind) h₁⟩⟩
    | _, .some ⟨_, ⟨h₂⟩⟩ => .some ⟨_, ⟨.point 1 (by grind) h₂⟩⟩
    | _, _ => .none
  | DCC? (≃.mk to_fun inv_fun comp_id id_comp) =>
    match to_fun.step?, inv_fun.step? with
    | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.point 0 (by grind) h₁⟩⟩
    | _, .some ⟨_, ⟨h₂⟩⟩ => .some ⟨_, ⟨.point 1 (by grind) h₂⟩⟩
    | _, _ =>
      match comp_id.step?, id_comp.step? with
      | .some ⟨_, ⟨h₃⟩⟩, _ => .some ⟨_, ⟨.point 2 (by grind) h₃⟩⟩
      | _, .some ⟨_, ⟨h₄⟩⟩ => .some ⟨_, ⟨.point 3 (by grind) h₄⟩⟩
      | _, _ => .none
  | (DCC? (Π f_α f_β)) =>
    match f_α.step?, f_β.step? with
    | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.point 0 (by grind) h₁⟩⟩
    | _, .some ⟨_, ⟨h₁⟩⟩ => .some ⟨_, ⟨.point 1 (by grind) h₁⟩⟩
    | _, _ => .none
  | (DCC? (Σ f_α f_β)) =>
    match f_α.step?, f_β.step? with
    | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.point 0 (by grind) h₁⟩⟩
    | _, .some ⟨_, ⟨h₁⟩⟩ => .some ⟨_, ⟨.point 1 (by grind) h₁⟩⟩
    | _, _ => .none
  | (DCC? ((Eql _f_α) (& _env) (& _x))) => .some ⟨_, ⟨.eql⟩⟩
  | (DCC? (x = y)) =>
    match x.step?, y.step? with
    | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.point 0 (by grind) h₁⟩⟩
    | _, .some ⟨_, ⟨h₁⟩⟩ => .some ⟨_, ⟨.point 1 (by grind) h₁⟩⟩
    | _, _ => .none
  | DCC? (! x) =>
    match x.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 0 (by grind) h⟩⟩
    | _ => .none
  | DCC? (!<> x) =>
    match x.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 0 (by grind) h⟩⟩
    | _ => .none
  | DCC? ((!<> _f) (& _x))                                 => .some ⟨_, ⟨.map⟩⟩
  | DCC? (($<> _f) (& _x))                                 => .some ⟨_, ⟨.fmap⟩⟩
  | DCC? ((* _α) (& _x))                                 => .some ⟨_, ⟨.unbox⟩⟩
  | DCC? (* x) =>
    match x.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 0 (by grind) h⟩⟩
    | _ => .none
  | DCC? ($<> x) =>
    match x.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 0 (by grind) h⟩⟩
    | _ => .none
  | DCC? (& x) =>
    match x.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 0 (by grind) h⟩⟩
    | _ => .none
  | DCC? ((⟨,⟩_β M N) (& _x))                        => .some ⟨_, ⟨.pair⟩⟩
  | (DCC? ((Eval _α _β _x) (,__β _y _z)))            => .some ⟨_, ⟨.evalc⟩⟩
  | (DCC? ((`_β _x) _y))                             => .some ⟨_, ⟨.quot⟩⟩
  | (DCC? ((Id _α) _x))                                => .some ⟨_, ⟨.id⟩⟩
  | (DCC? ((Fst _α) (,_γ _a _b)))                     => .some ⟨_, ⟨.fstc⟩⟩
  | (DCC? ((Swap _B _C) (,_B₂ _a _b)))                 => .some ⟨_, ⟨.swap⟩⟩
  | DCC? (Fst B) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 0 (by grind) h⟩⟩
    | _ => .none
  | DCC? (Snd B) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 0 (by grind) h⟩⟩
    | _ => .none
  | DCC? (Swap B C) =>
    match B.step?, C.step? with
    | .some ⟨_, ⟨h⟩⟩, _ => .some ⟨_, ⟨.point 0 (by grind) h⟩⟩
    | _, .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 1 (by grind) h⟩⟩
    | _, _ => .none
  | DCC? (Eql B) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨ .point 0 (by grind) h⟩⟩
    | _ => .none
  | DCC? (Id A) =>
    match A.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨ .point 0 (by grind) h⟩⟩
    | _ => .none
  | DCC? (refl B) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨ .point 0 (by grind) h⟩⟩
    | _ => .none
  | (DCC? ((Snd _α) (,_γ _a _b)))                     => .some ⟨_, ⟨.sndc⟩⟩
  | (DCC? ((∘ _x _y) _z))                              => .some ⟨_, ⟨.comp⟩⟩
  | DCC? (∘ x  y) =>
    match x.step?, y.step? with
    | .some ⟨_, ⟨h⟩⟩, _ => .some ⟨_, ⟨.point 0 (by grind) h⟩⟩
    | _, .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 1 (by grind) h⟩⟩
    | _, _ => .none
  | (DCC? ((!Λ _α _β _x) (& _y) (& _z)))                => .some ⟨_, ⟨.curr'⟩⟩
  | DCC? (!Λ A B x) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 1 (by grind) h⟩⟩
    | .none => match A.step?, x.step? with
      | .some ⟨_, ⟨h⟩⟩, _ => .some ⟨_, ⟨.point 0 (by grind) h⟩⟩
      | _, .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 2 (by grind) h⟩⟩
      | _, _ => .none
  | (DCC? ((Λ _α _β _x) _y _z)) => .some ⟨_, ⟨.curr⟩⟩
  | DCC? (Λ A B x) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 1 (by grind) h⟩⟩
    | .none => match A.step?, x.step? with
      | .some ⟨_, ⟨h⟩⟩, _ => .some ⟨_, ⟨.point 0 (by grind) h⟩⟩
      | _, .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 2 (by grind) h⟩⟩
      | _, _ => .none
  | DCC? (Eval A B x) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 1 (by grind) h⟩⟩
    | .none => match A.step?, x.step? with
      | .some ⟨_, ⟨h⟩⟩, _ => .some ⟨_, ⟨.point 0 (by grind) h⟩⟩
      | _, .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 2 (by grind) h⟩⟩
      | _, _ => .none
  | (DCC? ((Σ _f_α _f_β) _env))                        => .some ⟨_, ⟨.sigma⟩⟩
  | DCC? (,β x y) =>
    match β.step? with
    | .some ⟨_, ⟨h₁⟩⟩ => .some ⟨_, ⟨.point 0 (by grind) h₁⟩⟩
    | _ =>
      match x.step?, y.step? with
      | .some ⟨x', ⟨h₁⟩⟩, _ => .some ⟨(DCC? (,β x' y)), ⟨.point 1 (by grind) h₁⟩⟩
      | _, .some ⟨y', ⟨h₁⟩⟩ => .some ⟨(DCC? (,β x y')), ⟨.point 2 (by grind) h₁⟩⟩
      | _, _ => .none
  | DCC? (⟨,⟩B x y) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 0 (by grind) h⟩⟩
    | _ =>
      match x.step?, y.step? with
      | .some ⟨_, ⟨h⟩⟩, _ => .some ⟨_, ⟨.point 1 (by grind) h⟩⟩
      | _, .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 2 (by grind) h⟩⟩
      | _, _ => .none
  | (DCC? (Σ β)) =>
    match β.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 0 (by grind) h⟩⟩
    | _ => .none
  | DCC? (`B x) =>
    match B.step?, x.step? with
    | .some ⟨_, ⟨h⟩⟩, _ => .some ⟨_, ⟨.point 0 (by grind) h⟩⟩
    | _, .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 1 (by grind) h⟩⟩
    | _, _ => .none
  | DCC? (f x) =>
    match f.step?, x.step? with
    | .some ⟨f', ⟨h₁⟩⟩, _ => .some ⟨(DCC? (f' x)), ⟨.congrFun h₁⟩⟩
    | _, .some ⟨x', ⟨h₁⟩⟩ => .some ⟨(DCC? (f x')), ⟨.congrArg h₁⟩⟩
    | _, _ => .none
  | DCC? (Dom (Eql _B)) => .some ⟨_, ⟨.eqlτ₀⟩⟩
  | DCC? (Dom (refl _B)) => .some ⟨_, ⟨.reflτ₀⟩⟩
  | DCC? (Dom (!<> _x)) => .some ⟨_, ⟨.mapτ₀⟩⟩
  | DCC? (Dom ($<> _x)) => .some ⟨_, ⟨.fmapτ₀⟩⟩
  | DCC? (Dom (* _x)) => .some ⟨_, ⟨.unboxτ₀⟩⟩
  | DCC? (Dom (⟨,⟩_B _x _y)) => .some ⟨_, ⟨.pairτ₀⟩⟩
  | DCC? (Dom (Eval _A _B _x)) => .some ⟨_, ⟨.evalcτ₀⟩⟩
  | DCC? (Dom (`_B _x)) => .some ⟨_, ⟨.quotτ₀⟩⟩
  | DCC? (Dom (Id _A)) => .some ⟨_, ⟨.idτ₀⟩⟩
  | DCC? (Dom (Fst _B)) => .some ⟨_, ⟨.fstcτ₀⟩⟩
  | DCC? (Dom (Snd _B)) => .some ⟨_, ⟨.sndcτ₀⟩⟩
  | DCC? (Dom (Swap _B _C)) => .some ⟨_, ⟨.swapτ₀⟩⟩
  | DCC? (Dom (∘ _x _y)) => .some ⟨_, ⟨.compτ₀⟩⟩
  | DCC? (Dom (Λ _A _B _x)) => .some ⟨_, ⟨.currτ₀⟩⟩
  | DCC? (Dom (!Λ _A _B _x)) => .some ⟨_, ⟨.curr'τ₀⟩⟩
  | DCC? (Dom (Σ B C)) => .some ⟨_, ⟨.sigmaτ₀⟩⟩
  | DCC? (Dom (Π B C)) => .some ⟨_, ⟨.piτ₀⟩⟩
  | DCC? (Dom ((Eql _B) (& _x))) => .some ⟨_, ⟨.eqlτ₁⟩⟩
  | DCC? (Dom ((refl _B) (& _x))) => .some ⟨_, ⟨.reflτ₁⟩⟩
  | DCC? (Dom ((Λ _A _B _x) _y)) => .some ⟨_, ⟨.currτ₁⟩⟩
  | DCC? (Dom ((!Λ _A _B _x) (& _y))) => .some ⟨_, ⟨.curr'τ₁⟩⟩
  | DCC? (Dom x) =>
    match x.step? with
    | .some ⟨_, ⟨hr⟩⟩ => .some ⟨_, ⟨.dom₀ hr⟩⟩
    | .none => .none
  | DCC? (Uncoup (Σ x)) => .some ⟨_, ⟨.uncoup⟩⟩
  | DCC? (Unbang (! x)) => .some ⟨_, ⟨.unbang⟩⟩
  | DCC? (Uncoup x) =>
    match x.step? with
    | .some ⟨_, ⟨hr⟩⟩ => .some ⟨_, ⟨.uncoup₀ hr⟩⟩
    | .none => .none
  | DCC? (Unbang x) =>
    match x.step? with
    | .some ⟨_, ⟨hr⟩⟩ => .some ⟨_, ⟨.unbang₀ hr⟩⟩
    | .none => .none
  | DCC? (Dom₂ (Eql B)) => .some ⟨_, ⟨.eqlτ₃⟩⟩
  | DCC? (Dom₂ (refl B)) => .some ⟨_, ⟨.reflτ₃⟩⟩
  | DCC? (Dom₂ (Λ A B x)) => .some ⟨_, ⟨.currτ₃⟩⟩
  | DCC? (Dom₂ (!Λ A B x)) => .some ⟨_, ⟨.curr'τ₃⟩⟩
  | DCC? (Dom₂ x) =>
    match x.step? with
    | .some ⟨_, ⟨hr⟩⟩ => .some ⟨_, ⟨.dom₂₀ hr⟩⟩
    | .none => .none
  | _ => .none

set_option maxHeartbeats 10000000 in
@[dcc_force_reduce, dcc_force_aff]
instance RedAff.instRedRel : RedRel (α := GenericExpr τ) (RedAff (τ := τ)) size where
  run := step?
  decreasing := by
    intro x y h
    induction h
    case point =>
      expose_names
      have h := point_size_lt' (n := n) (h := h)
      have h' : p'.size < e.size := by grind
      have h := set_point_size_lt (by assumption) rfl (by assumption)
      simp_all
    any_goals (
      focus
      try dsimp
      try grind
      try simp_all [dcc_rel, dcc_size, Rel.run]
      try grind
      try aesop (rule_sets := [DccRel, DccSize])
      try rfl)

theorem red_aff_sn : ∀ (e : GenericExpr τ), Acc (fun b a => RedAff (τ := τ) a b) e :=
  RedAff.instRedRel.sn

theorem red_aff_trans_sn : ∀ (e : GenericExpr τ), Acc (fun b a => Relation.TransGen RedAff a b) e :=
  RedAff.instRedRel.to_trans.sn

theorem RedAff.mkCongrFun (h : RedAff f f') : RedAff (DCC? (f x)) (DCC? (f' x)) := .congrFun h
theorem RedAff.mkCongArg (h : RedAff x x') : RedAff (DCC? (f x)) (DCC? (f x')) := .congrArg h

theorem congrFun' {f x f' : GenericExpr τ} (hr : Relation.ReflTransGen RedAff f f') : Relation.ReflTransGen RedAff (DCC? (f x)) (DCC? (f' x)) := by
  match hr.cases_head with
  | .inl h =>
    cases h
    exact .refl
  | .inr ⟨_, h₁, h₂⟩ =>
    have h_dec := RedAff.instRedRel.decreasing h₁
    exact .trans (.single (.congrFun h₁)) (congrFun' h₂)
termination_by size f

theorem swap₀' {x x' : GenericExpr τ} (hr : Relation.ReflTransGen RedAff x x') : Relation.ReflTransGen RedAff (DCC? (Swap x _y)) (DCC? (Swap x' _y)) := by
  match hr.cases_head with
  | .inl h =>
    cases h
    exact .refl
  | .inr ⟨_, h₁, h₂⟩ =>
    have h_dec := RedAff.instRedRel.decreasing h₁
    exact .trans (.single (.point 0 (by grind) h₁)) (swap₀' (by assumption))
termination_by x.size

theorem swap₁' {x x' : GenericExpr τ} (hr : Relation.ReflTransGen RedAff x x') : Relation.ReflTransGen RedAff (DCC? (Swap _x x)) (DCC? (Swap _x x')) := by
  match hr.cases_head with
  | .inl h =>
    cases h
    exact .refl
  | .inr ⟨_, h₁, h₂⟩ =>
    have h_dec := RedAff.instRedRel.decreasing h₁
    exact .trans (.single (.point 1 (by grind) h₁)) (swap₁' (by assumption))
termination_by x.size

theorem dom' {x x' : GenericExpr τ} (hr : Relation.ReflTransGen RedAff x x') : Relation.ReflTransGen RedAff (DCC? (Dom x)) (DCC? (Dom x')) := by
  match hr.cases_head with
  | .inl h =>
    cases h
    exact .refl
  | .inr ⟨_, h₁, h₂⟩ =>
    have h_dec := RedAff.instRedRel.decreasing h₁
    exact .trans (.single (.dom₀ h₁)) (dom' (by assumption))
termination_by x.size

theorem dom₂' {x x' : GenericExpr τ} (hr : Relation.ReflTransGen RedAff x x') : Relation.ReflTransGen RedAff (DCC? (Dom₂ x)) (DCC? (Dom₂ x')) := by
  match hr.cases_head with
  | .inl h =>
    cases h
    exact .refl
  | .inr ⟨_, h₁, h₂⟩ =>
    have h_dec := RedAff.instRedRel.decreasing h₁
    exact .trans (.single (.dom₂₀ h₁)) (dom₂' (by assumption))
termination_by x.size

theorem uncoup' {x x' : GenericExpr τ} (hr : Relation.ReflTransGen RedAff x x') : Relation.ReflTransGen RedAff (DCC? (Uncoup x)) (DCC? (Uncoup x')) := by
  match hr.cases_head with
  | .inl h =>
    cases h
    exact .refl
  | .inr ⟨_, h₁, h₂⟩ =>
    have h_dec := RedAff.instRedRel.decreasing h₁
    exact .trans (.single (.uncoup₀ h₁)) (uncoup' (by assumption))
termination_by x.size

theorem unbang' {x x' : GenericExpr τ} (hr : Relation.ReflTransGen RedAff x x') : Relation.ReflTransGen RedAff (DCC? (Unbang x)) (DCC? (Unbang x')) := by
  match hr.cases_head with
  | .inl h =>
    cases h
    exact .refl
  | .inr ⟨_, h₁, h₂⟩ =>
    have h_dec := RedAff.instRedRel.decreasing h₁
    exact .trans (.single (.unbang₀ h₁)) (unbang' (by assumption))
termination_by x.size

theorem congrArg' {x x' : GenericExpr τ} (hr : Relation.ReflTransGen RedAff x x') : Relation.ReflTransGen RedAff (DCC? (f x)) (DCC? (f x')) := by
  match hr.cases_head with
  | .inl h =>
    cases h
    exact .refl
  | .inr ⟨_, h₁, h₂⟩ =>
    have h_dec := RedAff.instRedRel.decreasing h₁
    exact .trans (.single (.congrArg h₁)) (congrArg' h₂)
termination_by size x

@[aesop safe forward (rule_sets := [DccForceReduce])]
theorem RedAff.elim_point₁ {A B : GenericExpr τ_c} (hr : RedAff A B) (h_arr : point_arity A = 1 := by rfl) : ∃ p', B = (A.set_points (A.points.set 0 p')) ∧ RedAff A.points[0] p' := by
  unfold point_arity at h_arr
  split at h_arr
  any_goals (simp at h_arr)
  any_goals (
    expose_names
    dcc_simp
    cases hr
    simp at h_arr_1
    expose_names
    simp [point_arity] at h
    cases h
    dcc_simp
    assumption)

theorem RedAff.mk_point {x y e : GenericExpr τ_c} (n : Fin (point_arity e) := by exact ⟨0, by grind⟩) (hr : RedAff x y := by assumption) (heq : (points e)[n] = x := by first | grind | (dcc_simp; rfl)) : RedAff e (e.set_points ((points e).set n y)) := .point n (by grind) (by
  cases heq
  exact hr)

theorem RedAff.instCongruent'_mp {e : GenericExpr τ_c} {p : Fin (point_arity e)} (h : RedAff (points e)[p] p') : RedAff e (set_points e ((points e).set p p')) :=
  .point (↑ p) (by grind) h

instance RedAff.instCongruent : Congruent (RedAff (τ := τ)) where
  coup_ := fun h => .point 0 (by grind) h
  pil_ := fun h => .point 0 (by grind) h
  pir_ := fun h => .point 1 (by grind) h
  sigl_ := fun h => .point 1 (by grind) h
  sigr_ := fun h => .point 2 (by grind) h

theorem point_trans (_hr : RedAff (τ := τ_c) ((points e).get ⟨n, h⟩) p') (hr' : RedAff p' w) : RedAff ((points ((e.set_points ((points e).set n p')))).get ⟨n, by
  have h := congr_point_arr (e := e) (p := ⟨n, h⟩) (p' := p')
  grind⟩) w := by
  have h := get_set_point (e := e) (p := ⟨n, h⟩) (p' := p')
  simp [h]
  assumption

theorem point_trans' (_hr : RedAff (τ := τ_c) ((points e).get ⟨n, h⟩) p') (hr' : Relation.ReflTransGen RedAff p' w) : Relation.ReflTransGen RedAff ((points ((e.set_points ((points e).set n p')))).get ⟨n, by
  have h := congr_point_arr (e := e) (p := ⟨n, h⟩) (p' := p')
  grind⟩) w := by
  have h := get_set_point (e := e) (p := ⟨n, h⟩) (p' := p')
  simp [h]
  assumption

theorem point' (hr : Relation.ReflTransGen (RedAff (τ := τ)) ((points e).get ⟨n, h⟩) p') : Relation.ReflTransGen RedAff e (e.set_points ((points e).set n p')) :=
  match hr.cases_head with
  | .inl h => by
    cases h
    have heq := get_set_point (p := ⟨n, h⟩) (e := e) (p' := e.points.get ⟨n, h⟩)
    have heq' := get_set_point' (p := ⟨n, h⟩) (e := e) rfl
    simp [heq']
    exact Relation.ReflTransGen.refl
  | .inr ⟨_, h₁, h₂⟩ => by
    expose_names
    have h_dec := RedAff.instRedRel.decreasing h₁
    have h_dec₂ := decreasing? _ h₂
    have heq := set_same_point_comp (e := e) (x := w) (p := ⟨n, h⟩) (y := p')
    have hr' := RedAff.point _ _ h₁
    have hr'' := point_trans' h₁ h₂
    have h_dec₃ := decreasing? _ hr''
    have h_dec₂ : (e.set_points (e.points.set n w h)).size < e.size := by
      have h_dec := RedAff.instRedRel.decreasing hr'
      grind
    have hrt' := point' hr''
    have heq' := set_same_point_comp (e := e) (x := w) (p := ⟨n, h⟩) (y := p')
    simp [heq'] at hrt'
    exact Relation.ReflTransGen.trans (.single (.point n h h₁)) hrt'
termination_by e.size

theorem aff_mk_point' {x y e : GenericExpr τ} (hr : Relation.ReflTransGen RedAff x y) (hn : n < point_arity e := by grind) (heq : (points e)[(Fin.mk n hn)] = x := by first | rfl | grind | (dcc_simp; rfl)) : Relation.ReflTransGen RedAff e (e.set_points ((points e).set n y)) := by
  match hr.cases_head with
  | .inl h =>
    cases h
    unfold point_arity at hn
    split at hn
    any_goals (grind)
    case h_1 | h_14 =>
      simp at hn
      match n with
      | 0 | 1 | 2 | 3 =>
        simp at heq
        cases heq
        simp [set_points_self_noop]
        exact Relation.ReflTransGen.refl
  | .inr ⟨_, h₁, h₂⟩ =>
    cases heq
    have h_dec := RedAff.instRedRel.decreasing h₁
    have hr' := point' hr
    exact hr'

theorem aff_mk_point'' {x y e : GenericExpr τ} (n : ℕ) (hr : RedAff x y := by assumption) (hn : n < point_arity e := by grind) (heq : (points e)[(Fin.mk n hn)] = x := by first | rfl | grind | (dcc_simp; rfl)) : Relation.ReflTransGen RedAff e (e.set_points ((points e).set n y)) := aff_mk_point' (.single hr)

/-@[grind ., grind →, grind! →]
theorem mk_inner_norm (h_points : 0 < point_arity e := by grind)
  (hrn : List.Forall (IsNorm RedAff) (points e).toList := by intro h; grind) : IsNorm RedAff e := by
  unfold point_arity at h_points
  split at h_points
  any_goals (grind)
  any_goals (
    focus
    try (
      intro ⟨_, h⟩
      simp [points, Vector.toList] at hrn
      cases h
      expose_names
      have ⟨h₁, h₂, h₃, h₄⟩ := hrn
      match n with
      | 0 | 1 | 2 | 3 =>
        simp [Vector.get, points] at h_1
        grind)
    done)
  any_goals (
    focus
    try (
      intro ⟨_, h⟩
      simp [points, Vector.toList] at hrn
      cases h
      expose_names
      have ⟨h₁, h₂, h₃⟩ := hrn
      match n with
      | 0 | 1 | 2 =>
        simp [Vector.get, points] at h_1
        grind)
    done)
  any_goals (
    focus
    try (
      intro ⟨_, h⟩
      simp [points, Vector.toList] at hrn
      cases h
      expose_names
      have ⟨h₁, h₂⟩ := hrn
      match n with
      | 0 | 1 =>
        simp [Vector.get, points] at h_1
        grind)
    done)
  any_goals (
    focus
    try (
      intro ⟨_, h⟩
      simp [points, Vector.toList] at hrn
      cases h
      expose_names
      match n with
      | 0 =>
        simp [Vector.get, points] at h_1
        grind)
    done)
  case h_9 =>
    intro ⟨_, h⟩
    simp [points, Vector.toList] at hrn
    cases h
    expose_names
    have ⟨h₁, h₂, h₃, h₄⟩ := hrn
    match n with
    | 0 | 1 | 2 | 3 =>
      simp [Vector.get, points] at h_1
      grind-/
  /-  <;> (
    first
    | (grind)
    | (
    intro ⟨_, h⟩
    simp [points, Vector.toList] at hrn
    cases h <;> grind))-/

/-@[grind ., grind →, grind! .]
theorem elim_inner_norm (hrn : IsNorm RedAff e) : List.Forall (IsNorm RedAff)
  (points e).toList := by
  unfold points
  split
  any_goals (simp)
  case h_18 =>
      constructor
      · intro ⟨_, h⟩
        exact hrn ⟨_, by constructor; assumption⟩
      · intro ⟨_, h⟩
        exact hrn ⟨_, .swap₁ (by assumption)⟩
  case h_8 =>
    constructor
    · intro ⟨_, h⟩
      exact hrn ⟨_, by constructor; assumption⟩
    · intro ⟨_, h⟩
      exact hrn ⟨_, .eq₁ (by assumption)⟩
  any_goals (
    intro ⟨_, h⟩
    exact hrn ⟨_, by constructor; assumption⟩)
  case h_12 =>
    constructor
    · intro ⟨_, h⟩
      exact hrn ⟨_, by constructor; assumption⟩
    · intro ⟨_, h⟩
      exact hrn ⟨_, .sigma₁ (by assumption)⟩
  case h_13 =>
    constructor
    · intro ⟨_, h⟩
      exact hrn ⟨_, by constructor; assumption⟩
    · intro ⟨_, h⟩
      exact hrn ⟨_, .quot₁ (by assumption)⟩
  case h_14 =>
    constructor
    · intro ⟨_, h⟩
      exact hrn ⟨_, by constructor; assumption⟩
    · constructor
      · intro ⟨_, h⟩
        exact hrn ⟨_, .sig₁ (by assumption)⟩
      · intro ⟨_, h⟩
        exact hrn ⟨_, .sig₂ (by assumption)⟩
  case h_20 =>
    constructor
    · intro ⟨_, h⟩
      exact hrn ⟨_, by constructor; assumption⟩
    · intro ⟨_, h⟩
      exact hrn ⟨_, .pi₁ (by assumption)⟩
  case h_21 =>
    constructor
    · intro ⟨_, h⟩
      exact hrn ⟨_, by constructor; assumption⟩
    · intro ⟨_, h⟩
      exact hrn ⟨_, .comp₁ (by assumption)⟩
  case h_22 =>
    constructor
    · intro ⟨_, h⟩
      exact hrn ⟨_, by constructor; assumption⟩
    · constructor
      · intro ⟨_, h⟩
        exact hrn ⟨_, .pair₁ (by assumption)⟩
      · intro ⟨_, h⟩
        exact hrn ⟨_, .pair₂ (by assumption)⟩
  case h_23 =>
    constructor
    · intro ⟨_, h⟩
      exact hrn ⟨_, by constructor; assumption⟩
    · constructor
      · intro ⟨_, h⟩
        exact hrn ⟨_, .curr₁ (by assumption)⟩
      · intro ⟨_, h⟩
        exact hrn ⟨_, .curr₂ (by assumption)⟩
  case h_24 =>
    constructor
    · intro ⟨_, h⟩
      exact hrn ⟨_, by constructor; assumption⟩
    · constructor
      · intro ⟨_, h⟩
        exact hrn ⟨_, .curr'₁ (by assumption)⟩
      · intro ⟨_, h⟩
        exact hrn ⟨_, .curr'₂ (by assumption)⟩
  case h_25 =>
    constructor
    · intro ⟨_, h⟩
      exact hrn ⟨_, by constructor; assumption⟩
    · constructor
      · intro ⟨_, h⟩
        exact hrn ⟨_, .eval₁ (by assumption)⟩
      · intro ⟨_, h⟩
        exact hrn ⟨_, .eval₂ (by assumption)⟩-/

@[aesop safe apply (rule_sets := [DccForceReduce])]
theorem refl_conf : ∃ B, Relation.ReflTransGen r A B ∧ Relation.ReflTransGen r A B := ⟨_, .refl, .refl⟩

@[aesop safe apply (rule_sets := [DccReduce])]
theorem congrFun_of_single (h : RedAff x x' := by assumption) : Relation.ReflTransGen RedAff (DCC? (x y)) (DCC? (x' y)) := .single (.congrFun h)

@[aesop safe apply (rule_sets := [DccReduce])]
theorem congrArg_of_single (h : RedAff y y' := by assumption) : Relation.ReflTransGen RedAff (DCC? (x y)) (DCC? (x y')) := .single (.congrArg h)

attribute [aesop safe (rule_sets := [DccForceReduce]) [constructors]] Relation.ReflTransGen

set_option maxHeartbeats 10000000000 in
open Congruent' in
open Congruent in @[dcc_reduce, aesop safe apply (rule_sets := [DccReduce])]
theorem RedAff.conf (h₁ : (RedAff (τ := τ)) A B) (h₂ : RedAff A C) : ∃ D, RedAff.instRedRel.ReflTrans B D ∧ RedAff.instRedRel.ReflTrans C D := by
  induction h₁ generalizing C
  case eqlτ₃ =>
    cases h₂ with
    | dom₂₀ h =>
      cases h
      case _ h => exact ⟨_, .single (by constructor; assumption), .single (by constructor)⟩
    | point =>
      dcc_simp_all
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case reflτ₃ =>
    cases h₂ with
    | dom₂₀ h =>
      cases h
      case _ h => exact ⟨_, .single (by constructor; assumption), .single (by constructor)⟩
    | point =>
      dcc_simp_all
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case currτ₃ =>
    cases h₂ with
    | dom₂₀ h =>
      cases h
      expose_names
      match n with
      | 0 => exact ⟨_, .refl, .single (by constructor)⟩
      | 1 => exact ⟨_, .single (by assumption), .single (by constructor)⟩
      | 2 => exact ⟨_, .refl, .single (by constructor)⟩
    | point =>
      dcc_simp_all
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case curr'τ₃ =>
    cases h₂ with
    | dom₂₀ h =>
      cases h
      expose_names
      match n with
      | 0 => exact ⟨_, .refl, .single (by constructor)⟩
      | 1 => exact ⟨_, .single (.point 0 (by grind) (by assumption)), .single (by constructor)⟩
      | 2 => exact ⟨_, .refl, .single (by constructor)⟩
    | point =>
      dcc_simp_all
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case dom₂₀ ih =>
    match h₂ with
    | .eqlτ₃ =>
      rename_i hr
      cases hr
      expose_names
      match n with
      | 0 => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) (by assumption))⟩
    | .reflτ₃ =>
      rename_i hr
      cases hr
      expose_names
      match n with
      | 0 => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) (by assumption))⟩
    | .dom₂₀ h =>
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, dom₂' h₁, dom₂' h₂⟩
    | .currτ₃ =>
      rename_i hr
      cases hr
      expose_names
      match n with
      | 0 => exact ⟨_, .single (by constructor), .refl⟩
      | 1 => exact ⟨_, .single .currτ₃, .single (by assumption)⟩
      | 2 => exact ⟨_, .single .currτ₃, .refl⟩
    | .curr'τ₃ =>
      rename_i hr
      cases hr
      expose_names
      match n with
      | 0 => exact ⟨_, .single (by constructor), .refl⟩
      | 1 => exact ⟨_, .single .curr'τ₃, .single (.point 0 (by grind) (by assumption))⟩
      | 2 => exact ⟨_, .single .curr'τ₃, .refl⟩
  /-case swap₁ ih =>
    match h₂ with
    | .swap₀ h =>
      exact ⟨_, .single (.swap₀ h), .single (.swap₁ (by assumption))⟩
    | .swap₁ h =>
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, swap₁' h₁, swap₁' h₂⟩
  case swap₀ ih =>
    match h₂ with
    | .swap₁ h =>
      exact ⟨_, .single (.swap₁ h), .single (.swap₀ (by assumption))⟩
    | .swap₀ h =>
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, swap₀' h₁, swap₀' h₂⟩-/
  case swap =>
    match h₂ with
    | .swap => exact ⟨_, .refl, .refl⟩
    | .congrFun (.point 1 hn h) => exact ⟨_, .single (.point 0 (by grind) (.point 0 (by simp [point_arity, points, Vector.get]) h)), .single .swap⟩
    | .congrFun (.point 0 hn h) => exact ⟨_, .single (.point 0 (by grind) (.point 1 (by simp [point_arity, points, Vector.get]) h)), .single .swap⟩
    | .congrArg h =>
      match h with
      | .point 0 hn h => exact ⟨_, .refl, .single .swap⟩
      | .point 1 hn h => exact ⟨_, .single (.point 2 (by grind) h), .single .swap⟩
      | .point 2 hn h => exact ⟨_, .single (.point 1 (by grind) h), .single .swap⟩
  case uncoup =>
    match h₂ with
    | .uncoup₀ (.point 0 hn h) => exact ⟨_, .single h, .single .uncoup⟩
    | .uncoup => exact ⟨_, .refl, .refl⟩
  case unbang =>
    match h₂ with
    | .unbang₀ (.point 0 hn h) => exact ⟨_, .single h, .single .unbang⟩
    | .unbang => exact ⟨_, .refl, .refl⟩
  case uncoup₀ =>
    match h₂ with
    | .uncoup₀ h =>
      rename_i h₀ ih
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, uncoup' h₁, uncoup' h₂⟩
    | .uncoup =>
      rename_i h ih
      match h with
      | .point 0 hn h => exact ⟨_, .single (by constructor), .single h⟩
  case unbang₀ =>
    match h₂ with
    | .unbang₀ h =>
      rename_i h₀ ih
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, unbang' h₁, unbang' h₂⟩
    | .unbang =>
      rename_i h ih
      match h with
      | .point 0 hn h => exact ⟨_, .single (by constructor), .single h⟩
  /-
    Domain reductions
  -/
  case unboxτ₀ =>
    match h₂ with
    | .dom₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single (.point 0 (by grind) hr), .single (by constructor)⟩
    | .unboxτ₀ => exact ⟨_, .refl, .refl⟩
  case swapτ₀ =>
    match h₂ with
    | .dom₀ (.point 0 hn hr) =>
      exact ⟨_, .single (.point 0 (by grind) (.point 0 (by simp [point_arity, points, Vector.get]) hr)), .single (by constructor)⟩
    | .dom₀ (.point 1 hn hr) =>
      exact ⟨_, .refl, .single (by constructor)⟩
    | .swapτ₀ => exact ⟨_, .refl, .refl⟩
  case eqlτ₀ | reflτ₀ | mapτ₀ | fmapτ₀ =>
    cases h₂ with
    | dom₀ hr =>
     match hr with
     | (.point 0 hn hr) => exact ⟨_, .single (.point 0 (by grind) (.dom₀ hr)), .single (by constructor)⟩
    | _ =>
      expose_names
      try (simp [point_arity] at h)
      try (exact ⟨_, .refl, .refl⟩)
  case pairτ₀ =>
    cases h₂ with
    | dom₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
      | .point 1 hn hr => exact ⟨_, .single (.point 0 (by grind) hr.dom₀), .single (by constructor)⟩
      | .point 2 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
    | pairτ₀ => exact ⟨_, .refl, .refl⟩
    | point =>
      expose_names
      simp [point_arity] at h
  case evalcτ₀ =>
    cases h₂ with
    | dom₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
      | .point 1 hn hr => exact ⟨_, .single (.point 0 (by grind) hr), .single (by constructor)⟩
      | .point 2 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
    | evalcτ₀ => exact ⟨_, .refl, .refl⟩
    | point =>
      expose_names
      simp [point_arity] at h
  case curr'τ₀ =>
    cases h₂ with
    | dom₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
      | .point 1 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
      | .point 2 hn h => exact ⟨_, .single (.point 0 (by grind) (h.dom₀.unbang₀.uncoup₀.dom₀)), .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case currτ₀ =>
    cases h₂ with
    | dom₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
      | .point 1 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
      | .point 2 hn h => exact ⟨_, .single h.dom₀.uncoup₀.dom₀, .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case sndcτ₀ | fstcτ₀ =>
    cases h₂ with
    | dom₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single (.point 0 (by grind) hr), .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case idτ₀ =>
    cases h₂ with
    | dom₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single hr, .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case quotτ₀ =>
    cases h₂ with
    | dom₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single (by assumption), .single (by constructor)⟩
      | .point 1 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case compτ₀ | sigmaτ₀ | piτ₀ =>
    cases h₂ with
    | dom₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
      | .point 1 hn hr => exact ⟨_, .single hr.dom₀, .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case eqlτ₁ | reflτ₁ =>
    cases h₂ with
    | dom₀ hr =>
      match hr with
      | .congrArg (.point 0 hn h) => exact ⟨_, .single (.point 0 (by grind) h.congrArg), .single (by constructor)⟩
      | .congrFun h =>
        match h with
        | .point 0 hn h => exact ⟨_, .single (.point 0 (by grind) h.congrFun), .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case currτ₁ =>
    cases h₂ with
    | dom₀ hr =>
      cases hr with
      | congrFun h =>
        match h with
        | .point 1 hn h | .point 0 hn h => exact ⟨_, .refl, .single (by constructor)⟩
        | .point 2 hn h => exact ⟨_, .single h.dom₀.uncoup₀.congrFun, .single (by constructor)⟩
      | congrArg h => exact ⟨_, .single h.congrArg, .single (by constructor)⟩
      | point =>
        expose_names
        simp [point_arity] at h
    | point =>
        expose_names
        simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case curr'τ₁ =>
    cases h₂ with
    | dom₀ hr =>
      match hr with
      | .congrFun h =>
        match h with
        | .point 2 hn h =>
          exact ⟨_, .single (.point 0 (by grind) (h.dom₀.unbang₀.uncoup₀.congrFun)), .single (by constructor)⟩
        | .point 1 hn h | .point 0 hn h => exact ⟨_, .refl, .single (by constructor)⟩
      | .congrArg (.point 0 hn h) => exact ⟨_, .single (.point 0 (by grind) h.congrArg), .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case dom₀ ih =>
    cases h₂
    case point hn hr => simp [point_arity] at hn
    case swapτ₀ hr =>
      match hr with
      | .point 1 hn h =>
        exact ⟨_, .single (by constructor), .refl⟩
      | .point 0 hn h =>
        exact ⟨_, .single .swapτ₀, .single (.point 0 (by grind) (.point 0 (by simp [point_arity, points, Vector.get]) h))⟩
    case unboxτ₀ hr =>
      match hr with
      | .point 0 hn hr =>
        exact ⟨_, .single (by constructor), .single (.point 0 (by grind) hr)⟩
    case eqlτ₀ | reflτ₀ | mapτ₀ | fmapτ₀ =>
      rename_i hr
      match hr with
      | .point 0 hn hr =>
        exact ⟨_, .single (by constructor), .single (.point 0 (by grind) (.dom₀ hr))⟩
    case pairτ₀ =>
      rename_i hr
      match hr with
      | .point 0 hn hr | .point 2 hn hr => exact ⟨_, .single (by constructor), .refl⟩
      | .point 1 hn hr => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) hr.dom₀)⟩
    case evalcτ₀ =>
      rename_i hr
      match hr with
      | .point 0 hn hr | .point 2 hn hr => exact ⟨_, .single (by constructor), .refl⟩
      | .point 1 hn hr => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) hr)⟩
    case idτ₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single (by constructor), .single hr⟩
    case quotτ₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single (by constructor), .single hr⟩
      | .point 1 hn hr => exact ⟨_, .single (by constructor), .refl⟩
    case fstcτ₀ hr | sndcτ₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) hr)⟩
    case compτ₀ hr | sigmaτ₀ hr | piτ₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single (by constructor), .refl⟩
      | .point 1 hn hr => exact ⟨_, .single (by constructor), .single hr.dom₀⟩
    case currτ₀ =>
      rename_i hr
      match hr with
      | .point 1 hn hr | .point 0 hn hr => exact ⟨_, .single (by constructor), .refl⟩
      | .point 2 hn h => exact ⟨_, .single (by constructor), .single h.dom₀.uncoup₀.dom₀⟩
    case curr'τ₀ =>
      rename_i hr
      match hr with
      | .point 1 hn hr | .point 0 hn hr => exact ⟨_, .single (by constructor), .refl⟩
      | .point 2 hn h => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) h.dom₀.unbang₀.uncoup₀.dom₀)⟩
    case eqlτ₁ hr | reflτ₁ hr =>
      cases hr with
      | congrFun h =>
        match h with
        | .point 0 hn hr => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) hr.congrFun)⟩
      | congrArg h =>
        match h with
        | .point 0 hn hr => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) hr.congrArg)⟩
      | point =>
        expose_names
        simp [point_arity] at h
    case currτ₁ hr =>
      cases hr with
      | congrFun hr =>
        match hr with
        | .point 0 hn hr | .point 1 hn hr =>
          exact ⟨_, .single (by constructor), .refl⟩
        | .point 2 hn hr =>
          exact ⟨_, .single (by constructor), .single hr.dom₀.uncoup₀.congrFun⟩
      | congrArg hr =>
        exact ⟨_, .single (by constructor), .single hr.congrArg⟩
      | point =>
        expose_names
        simp [point_arity] at h
    case curr'τ₁ hr =>
      cases hr with
      | congrFun hr =>
        match hr with
        | .point 1 hn hr | .point 0 hn hr =>
          exact ⟨_, .single (by constructor), .refl⟩
        | .point 2 hn hr => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) hr.dom₀.unbang₀.uncoup₀.congrFun)⟩
      | congrArg hr =>
        match hr with
        | .point 0 hn hr => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) hr.congrArg)⟩
      | point =>
        expose_names
        simp [point_arity] at h
    case dom₀ hr =>
      have ⟨_, h₁, h₂⟩ := ih hr
      exact ⟨_, dom' (by assumption), dom' (by assumption)⟩
  -- Main reductions:
  case eql =>
    cases h₂ with
    | congrFun hr =>
      cases hr with
      | point =>
        expose_names
        simp [point_arity] at h
      | congrFun hr =>
        have ⟨_, h⟩ := hr.elim_point₁
        dcc_simp at h
        cases h.left
        exact ⟨_, .refl, .single (by constructor)⟩
      | congrArg hr =>
        have ⟨_, h⟩ := hr.elim_point₁
        dcc_simp at h
        cases h.left
        exact ⟨_, .refl, .single (by constructor)⟩
    | congrArg hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      dcc_simp at h
      cases h.left
      exact ⟨_, .trans (.single (h.right.mk_point (n := ⟨0, by grind⟩)))
        (.single (h.right.mk_point (n := ⟨1, by grind⟩))), .single (by constructor)⟩
    | _ => dcc_aesop' [force_reduce, force_step]
  case fmap | map =>
    cases h₂ with
    | congrFun hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      dcc_simp at h
      cases h.left
      exact ⟨_, .single ((RedAff.congrFun h.right).mk_point (n := ⟨0, by grind⟩)), .single (by constructor)⟩
    | congrArg hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      dcc_simp at h
      cases h.left
      exact ⟨_, .single ((RedAff.congrArg h.right).mk_point (n := ⟨0, by grind⟩)), .single (by constructor)⟩
    | _ => dcc_aesop' [force_reduce, force_step]
  case unbox =>
    cases h₂ with
    | congrFun hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      dcc_simp at h
      cases h.left
      exact ⟨_, .refl, .single (by constructor)⟩
    | congrArg hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single hr, .single (by constructor)⟩
    | _ => dcc_aesop' [force_reduce, force_step]
  case pair =>
    cases h₂ with
    | congrFun hr =>
      match hr with
      | .point 0 hn hr =>
        exact ⟨_, .single (hr.congrFun.mk_point (n := ⟨0, by grind⟩)), .single (by constructor)⟩
      | .point 1 hn hr =>
        exact ⟨_, .trans (.single (hr.congrFun.mk_point (n := ⟨1, by grind⟩))) (.single (hr.congrFun.congrArg.mk_point (n := ⟨2, by grind⟩))), .single (by constructor)⟩
      | .point 2 hn hr =>
        exact ⟨_, .single (hr.congrFun.congrFun.mk_point (n := ⟨2, by grind⟩)), .single (by constructor)⟩
    | congrArg hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      dcc_simp at h
      cases h.left
      exact ⟨_, .trans (.trans (.trans (.single (h.right.congrArg.mk_point (n := ⟨0, by grind⟩)))
        (.single (h.right.congrArg.mk_point (n := ⟨1, by grind⟩))))
        (.single (h.right.congrArg.congrArg.mk_point (n := ⟨2, by grind⟩))))
        (.single (h.right.congrArg.congrFun.mk_point (n := ⟨2, by grind⟩))), .single (by constructor)⟩
    | _ => dcc_aesop' [force_reduce, force_step]
  case evalc =>
    cases h₂ with
    | congrFun hr =>
      match hr with
      | .point 2 hn hr =>
        exact ⟨_, .single hr.congrFun.congrFun, .single .evalc⟩
      | .point 0 hn hr | .point 1 hn hr => exact ⟨_, .refl, .single .evalc⟩
    | congrArg hr =>
      match hr with
      | .point 0 hn hr =>
        exact ⟨_, .refl, .single .evalc⟩
      | .point 1 hn hr =>
        exact ⟨_, .single hr.congrArg.congrFun, .single .evalc⟩
      | .point 2 hn hr => exact ⟨_, .single hr.congrArg, .single .evalc⟩
    | _ => dcc_aesop' [force_reduce, force_step]
  case quot =>
    cases h₂ with
    | congrFun h =>
      match h with
      | .point 0 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
      | .point 1 hn hr => exact ⟨_, .single hr, .single (by constructor)⟩
    | congrArg h => exact ⟨_, .refl, .single (by constructor)⟩
    | _ => dcc_aesop' [force_reduce, force_step]
  case id =>
    cases h₂ with
    | congrFun hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      cases h.left
      exact ⟨_, .refl, .single (by constructor)⟩
    | congrArg hr => exact ⟨_, .single hr, .single (by constructor)⟩
    | point =>
        expose_names
        simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case fstc | sndc =>
    cases h₂ with
    | congrFun hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      cases h.left
      exact ⟨_, .refl, .single (by constructor)⟩
    | congrArg hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
      | .point 2 hn hr | .point 1 hn hr => first | exact ⟨_, .single hr, .single (by constructor)⟩ | exact ⟨_, .refl, .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case comp =>
    cases h₂ with
    | congrFun hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single hr.congrFun, .single (by constructor)⟩
      | .point 1 hn hr => exact ⟨_, .single hr.congrFun.congrArg, .single (by constructor)⟩
    | congrArg hr =>
      exact ⟨_, .single hr.congrArg.congrArg, .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case curr =>
    cases h₂ with
    | congrFun hr =>
      cases hr with
      | congrFun hr =>
        match hr with
        | .point 0 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
        | .point 1 hn hr => exact ⟨_, .single (RedAff.point 0 (by grind) hr).congrArg, .single (by constructor)⟩
        | .point 2 hn hr => exact ⟨_, .single hr.congrFun, .single (by constructor)⟩
      | point =>
        expose_names
        simp [point_arity] at h
      | congrArg hr =>
        exact ⟨_, .single (.congrArg (RedAff.point 1 (by grind) hr)), .single (by constructor)⟩
    | congrArg hr =>
      exact ⟨_, .single (.congrArg (RedAff.point 2 (by grind) hr)), .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case curr' =>
    cases h₂ with
    | congrFun hr =>
      cases hr with
      | point =>
        expose_names
        simp [point_arity] at h
      | congrFun hr =>
        match hr with
        | .point 0 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
        | .point 1 hn hr => exact ⟨_, .single (.congrArg (.point 0 (by grind) (.point 0 (by simp [points, Vector.get, point_arity]) hr))), .single (by constructor)⟩
        | .point 2 hn hr => exact ⟨_, .single hr.congrFun, .single (by constructor)⟩
      | congrArg hr =>
        have ⟨_, h⟩ := hr.elim_point₁
        cases h.left
        exact ⟨_, .single (.congrArg (.point 0 (by grind) (.point 1 (by simp [points, Vector.get, point_arity]) h.right))), .single (by constructor)⟩
    | congrArg hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      cases h.left
      exact ⟨_, .single (.congrArg (.point 0 (by grind) (.point 2 (by simp [points, Vector.get, point_arity]) h.right))), .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case sigma =>
    cases h₂ with
    | congrFun hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
      | .point 1 hn hr => exact ⟨_, .single (.point 0 (by grind) hr.congrFun), .single (by constructor)⟩
    | congrArg hr =>
      case _ hr => exact ⟨_, .single (.point 0 (by grind) hr.congrArg), .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  -- Inner congruences:
  case quot₀ hr ih | quot₁ hr ih | sigma₀ hr ih | sigma₁ hr ih | pi₀ hr ih | pi₁ hr ih
    | eq₀ hr ih | eq₁ hr ih | eql₀ hr ih | refl₀ hr ih | fstc₀ hr ih | sndc₀ hr ih | id₀ hr ih | bang₀ hr ih
    | box₀ hr ih | map₀ hr ih | fmap₀ hr ih | unbox₀ hr ih | coup₀ hr ih | comp₀ hr ih | comp₁ hr ih =>
    cases h₂ <;> (
      first
      | (rename_i hr₂
         have ⟨_, h₁, h₂⟩ := ih hr₂
         exact ⟨_, aff_mk_point' h₁ (n := 0), aff_mk_point' h₂ (n := 0)⟩)
      | (rename_i hr₂
         exact ⟨_, .single (mk_point (n := ⟨1, by grind⟩)), .single (mk_point (n := ⟨0, by grind⟩))⟩)
      | (rename_i hr₂
         have ⟨_, h₁, h₂⟩ := ih hr₂
         exact ⟨_, aff_mk_point' h₁ (n := 1), aff_mk_point' h₂ (n := 1)⟩)
      | (rename_i hr₂
         exact ⟨_, .single (mk_point (n := ⟨0, by grind⟩)), .single (mk_point (n := ⟨1, by grind⟩))⟩))
  case curr₀ hr ih | curr₁ hr ih | eval₀ hr ih | curr'₀ hr ih | pair₀ hr ih | sig₀ hr ih
    | pair₁ hr ih | sig₁ hr ih | curr'₁ hr ih | eval₁ hr ih =>
    cases h₂ <;> (
      first
      | (rename_i hr₂
         have ⟨_, h₁, h₂⟩ := ih hr₂
         exact ⟨_, aff_mk_point' h₁ (n := 0), aff_mk_point' h₂ (n := 0)⟩)
      | (rename_i hr₂
         exact ⟨_, .single (mk_point (n := ⟨1, by grind⟩)), .single (mk_point (n := ⟨0, by grind⟩))⟩)
      | (rename_i hr₂
         have ⟨_, h₁, h₂⟩ := ih hr₂
         exact ⟨_, aff_mk_point' h₁ (n := 1), aff_mk_point' h₂ (n := 1)⟩)
      | (rename_i hr₂
         exact ⟨_, .single (mk_point (n := ⟨0, by grind⟩)), .single (mk_point (n := ⟨1, by grind⟩))⟩)
      | (rename_i hr₂
         exact ⟨_, .single (mk_point (n := ⟨2, by grind⟩)), .single (mk_point (n := ⟨0, by grind⟩))⟩)
      | (rename_i hr₂
         exact ⟨_, .single (mk_point (n := ⟨2, by grind⟩)), .single (mk_point (n := ⟨1, by grind⟩))⟩))
  case pair₂ hr ih | sig₂ hr ih | curr₂ hr ih | eval₂ hr ih | curr'₂ hr ih =>
    cases h₂
    · exact ⟨_, aff_mk_point' (.single (by assumption)) (n := 0), aff_mk_point' (.single (by assumption)) (n := 2)⟩
    · exact ⟨_, aff_mk_point' (.single (by assumption)) (n := 1), aff_mk_point' (.single (by assumption)) (n := 2)⟩
    · rename_i hr₂
      have ⟨_, h₁, h₂⟩ := ih hr₂
      exact ⟨_, aff_mk_point' h₁ (n := 2), aff_mk_point' h₂ (n := 2)⟩
  case congrArg hr ih =>
    rename_i x x' f
    cases h₂
    <;> (try (
      have ⟨p', heq, hrp⟩ := hr.elim_point₁
      dcc_simp at heq; dcc_simp at hrp
      cases heq))
    case swap =>
      match hrp with
      | .sig₀ h =>
        exact ⟨_, .single (by constructor), .refl⟩
      | .sig₁ h =>
        exact ⟨_, .single (by constructor), .trans (.single (.sig₂ h)) (.single (.sig₀ (.congrArg h)))⟩
      | .sig₂ h =>
        exact ⟨_, .single (by constructor), .single (.sig₁ h)⟩
    case eql =>
      exact ⟨_, .single (by constructor), .trans (aff_mk_point'' 0) (aff_mk_point'' 1)⟩
    case fmap | map =>
      exact ⟨_, .single (by constructor), aff_mk_point'' 0 hrp.congrArg⟩
    case unbox =>
      exact ⟨_, .single (by constructor), .single hrp⟩
    case pair =>
      exact ⟨_, .single (by constructor), .trans (.trans (aff_mk_point'' 0 hrp.congrArg) (aff_mk_point'' 1 hrp.congrArg))
        ((aff_mk_point'' 2 hrp.congrArg.congrArg).trans (aff_mk_point'' 2 hrp.congrArg.congrFun))⟩
    case evalc =>
      cases hr with
      | sig₀ hr => exact ⟨_, .single (by constructor), .refl⟩
      | sig₁ hr => exact ⟨_, .single (by constructor), .single hr.congrArg.congrFun⟩
      | sig₂ hr => exact ⟨_, .single (by constructor), .single hr.congrArg⟩
    case quot => exact ⟨_, .single (by constructor), .refl⟩
    case id => exact ⟨_, .single (by constructor), .single (by assumption)⟩
    case sndc | fstc =>
      cases hr
      <;> (first
           | exact ⟨_, .single (by constructor), .refl⟩
           | exact ⟨_, .single (by constructor), .single (by assumption)⟩)
    case comp =>
      exact ⟨_, .single (by constructor), .single hr.congrArg.congrArg⟩
    case curr => exact ⟨_, .single (by constructor), .single (.congrArg (.sig₂ (by assumption)))⟩
    case curr' hr => exact ⟨_, .single (by constructor), .single (.congrArg (.box₀ (.sig₂ (by assumption))))⟩
    case sigma => exact ⟨_, .single (by constructor), .single (.coup₀ hr.congrArg)⟩
    case congrFun hr => exact ⟨_, .single (.congrFun hr), .single (.congrArg (by assumption))⟩
    case congrArg hr =>
      have ⟨_, h₁, h₂⟩ := ih hr
      exact ⟨_, congrArg' h₁, congrArg' h₂⟩
  case congrFun hr ih =>
    rename_i f f' x
    cases h₂
    <;> (try (
      have ⟨p', heq, hrp⟩ := hr.elim_point₁
      dcc_simp at heq; dcc_simp at hrp
      cases heq))
    case swap =>
      match hr with
      | .swap₀ h =>
        exact ⟨_, .single .swap, .refl⟩
      | .swap₁ h =>
        exact ⟨_, .single .swap, .single (.sig₀ (.congrFun h))⟩
    case eql =>
      cases hr
      <;> (
        rename_i hr
        have ⟨p', heq, hrp⟩ := hr.elim_point₁
        dcc_simp at heq; dcc_simp at hrp
        cases heq
        exact ⟨_, .single (by constructor), .refl⟩)
    case map | fmap =>
      exact ⟨_, .single (by constructor), aff_mk_point'' 0 hrp.congrFun⟩
    case unbox => exact ⟨_, .single (by constructor), .refl⟩
    case pair =>
      cases hr
      · rename_i hr; exact ⟨_, .single (by constructor), aff_mk_point'' 0 hr.congrFun⟩
      · rename_i hr; exact ⟨_, .single (by constructor), .trans (aff_mk_point'' 1 hr.congrFun) (aff_mk_point'' 2 hr.congrFun.congrArg)⟩
      · rename_i hr; exact ⟨_, .single (by constructor), aff_mk_point'' 2 hr.congrFun.congrFun⟩
    case evalc =>
      cases hr
      case eval₂ hr =>
        exact ⟨_, .single (by constructor), .single hr.congrFun.congrFun⟩
      case _ | _ => exact ⟨_, .single (by constructor), .refl⟩
    case quot =>
      cases hr
      · exact ⟨_, .single (by constructor), .refl⟩
      · exact ⟨_, .single (by constructor), .single (by assumption)⟩
    case id | fstc | sndc =>
      cases hr
      · exact ⟨_, .single (by constructor), .refl⟩
    case comp =>
      cases hr
      · rename_i hr; exact ⟨_, .single (by constructor), .single hr.congrFun⟩
      · rename_i hr; exact ⟨_, .single (by constructor), .single hr.congrFun.congrArg⟩
    case curr =>
      cases hr with
      | congrFun hr =>
        cases hr
        · rename_i hr; exact ⟨_, .single (by constructor), .refl⟩
        · rename_i hr; exact ⟨_, .single (by constructor), (congrArg' (aff_mk_point'' 0))⟩
        · rename_i hr; exact ⟨_, .single (by constructor), .single (.congrFun (by assumption))⟩
      | congrArg hr => exact ⟨_, .single (by constructor), (congrArg' (aff_mk_point'' 1))⟩
    case curr' =>
      cases hr with
      | congrFun hr =>
        cases hr
        · rename_i hr; exact ⟨_, .single (by constructor), .refl⟩
        · rename_i hr; exact ⟨_, .single (by constructor), .single (.congrArg (.box₀ (.sig₀ (by assumption))))⟩
        · rename_i hr; exact ⟨_, .single (by constructor), .single (.congrFun (by assumption))⟩
      | congrArg hr =>
        have ⟨p', heq, hrp⟩ := hr.elim_point₁
        dcc_simp at heq; dcc_simp at hrp
        cases heq
        exact ⟨_, .single (by constructor), .single (.congrArg (.box₀ (.sig₁ (by assumption))))⟩
    case sigma =>
      cases hr with
      | sigma₀ hr => exact ⟨_, .single (by constructor), .refl⟩
      | sigma₁ hr => exact ⟨_, .single (by constructor), .single (.coup₀ hr.congrFun)⟩
    case congrFun hr₂ =>
      have ⟨_, ha, hb⟩ := ih hr₂
      exact ⟨_, congrFun' ha, congrFun' hb⟩
    case congrArg hr => exact ⟨_, .single (.congrArg (by assumption)), .single (.congrFun (by assumption))⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance RedAff.instConf.{u} {τ : Type u} : Confluent (RedAff (τ := τ)) := ⟨RedAff.conf⟩

theorem red_aff_globally_conf.{u} {τ : Type u} {A B C : GenericExpr τ} : Relation.ReflTransGen (RedAff (τ := τ)) A B → Relation.ReflTransGen RedAff A C → ∃ D,
  Relation.ReflTransGen RedAff B D ∧ Relation.ReflTransGen RedAff C D :=
  RedAff.instRedRel.globally_confluent.conf

#check Relation.ReflTransGen.head_induction_on

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance instConfRedAffTrans.{u} {τ : Type u} : Confluent (RedAff (τ := τ)) (m := Relation.ReflTransGen) := RedAff.instRedRel.globally_confluent

set_option maxHeartbeats 10000000000 in
def semi_complete.{u} {τ : Type u} {A B : GenericExpr τ} (hr : A.RedAff B) : ∃ B', ∃ (h : A.RedAff B'), (step? A) = .some ⟨B', ⟨h⟩⟩ := by
  change ∃ _, ∃ _, (step? _) = .some _
  unfold step?
  split
  any_goals (
    focus
    try (
      split
      case h_1 hr' heq => exact ⟨_, hr'.mk_point (n := ⟨0, by grind⟩), rfl⟩
      case h_2 hr' heq _ => exact ⟨_, hr'.mk_point (n := ⟨1, by grind⟩), rfl⟩
      case h_3 hn₁ hn₂ =>
        cases hr <;> (
          rename_i hr
          have ⟨_, hr'', heq⟩ := semi_complete hr
          grind))
    done)
  any_goals (exact ⟨_, by constructor, rfl⟩)
  any_goals (
    focus
    try (
      split
      case h_1 hr' heq =>
        exact ⟨_, hr'.mk_point (n := ⟨0, by grind⟩), rfl⟩
      case h_2 hn₁ hn₂ =>
        cases hr <;> (
          rename_i hr
          have ⟨_, hr'', heq⟩ := semi_complete hr
          grind))
    done)
  any_goals (
    focus
    try (
      split
      case h_1 hr' heq => exact ⟨_, hr'.mk_point (n := ⟨1, by grind⟩), rfl⟩
      · split
        case h_1 hr' heq => exact ⟨_, hr'.mk_point (n := ⟨0, by grind⟩), rfl⟩
        case h_2 hr' heq _ => exact ⟨_, hr'.mk_point (n := ⟨2, by grind⟩), rfl⟩
        case h_3 hn₁ hn₂ =>
          cases hr <;> (
            rename_i hr
            have ⟨_, hr'', heq⟩ := semi_complete hr
            grind))
    done)
  any_goals (
    focus
    try (
      split
      case h_1 hr' heq => exact ⟨_, hr'.mk_point (n := ⟨0, by grind⟩), rfl⟩
      · split
        case h_1 hr' heq => exact ⟨_, hr'.mk_point (n := ⟨1, by grind⟩), rfl⟩
        case h_2 hr' heq _ => exact ⟨_, hr'.mk_point (n := ⟨2, by grind⟩), rfl⟩
        case h_3 hn₁ hn₂ =>
          cases hr <;> (
            rename_i hr
            have ⟨_, hr'', heq⟩ := semi_complete hr
            grind))
    done)
  case h_38 =>
    cases hr
    <;> simp_all
    any_goals (grind)
    case congrFun hr =>
      have ⟨_, hr', heq⟩ := semi_complete hr
      simp [heq]
      exact hr'.congrFun
    case congrArg hr =>
      have ⟨_, hr', heq⟩ := semi_complete hr
      simp [heq]
      split
      · exact ⟨_, .congrFun (by assumption), rfl⟩
      · exact ⟨_, .congrArg (by assumption), rfl⟩
      · grind
  case h_60 =>
    simp_all
    cases hr
    any_goals (grind)
    case dom₀ hr =>
      have ⟨_, hr', heq⟩ := semi_complete hr
      exact ⟨_, hr'.dom₀, by simp [heq]⟩
  case h_63 =>
    simp_all
    cases hr
    any_goals (grind)
    case uncoup₀ hr =>
      have ⟨_, hr', heq⟩ := semi_complete hr
      exact ⟨_, hr'.uncoup₀, by simp [heq]⟩
  case h_64 =>
    simp_all
    cases hr
    any_goals (grind)
    case unbang₀ hr =>
      have ⟨_, hr', heq⟩ := semi_complete hr
      exact ⟨_, hr'.unbang₀, by simp [heq]⟩
  case h_69 =>
    simp_all
    cases hr
    any_goals (grind)
    case dom₂₀ hr =>
      have ⟨_, hr', heq⟩ := semi_complete hr
      exact ⟨_, hr'.dom₂₀, by simp [heq]⟩
  case h_70 =>
    simp_all
    cases hr
    any_goals (grind)

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance RedAff.instSemicomplete.{u} {τ : Type u} : SemiComplete (RedAff (τ := τ)) := ⟨semi_complete⟩

theorem aff_complete (h : Relation.ReflTransGen RedAff A B)
  (hn : IsNorm RedAff B) : reduce RedAff A = ⟨B, ⟨h⟩⟩ :=
  RedAff.instRedRel.instComplete.complete h hn

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance instComplete.{u} {τ : Type u} : Complete (Relation.ReflTransGen (RedAff (τ := τ))) (P := IsNorm RedAff) := RedAff.instRedRel.instComplete

-- RedRel.reduce Size RedAff.instRedRel : (e : Expr) → (e' : Expr) × PULift (Relation.ReflTransGen RedAff e e')
#check reduce RedAff

/-
Complete.complete
  Id : ∀ (h : Relation.ReflTransGen RedAff ?m.8 ?m.9), IsNorm RedAff ?m.9 → Rel.run Id ?m.8 = pure ⟨?m.9, { down := h }⟩
-/
#check instComplete.complete

@[grind ., grind →]
theorem RedAff.decreasing' (h : RedAff A B) : size B < size A := by
  induction h <;> grind

@[grind ., grind →]
theorem red_aff_decreasing?.{u} {τ : Type u} {A B : GenericExpr τ} [DecidableEq τ] (h : Relation.ReflTransGen (RedAff (τ := τ)) A B) : (size B) ≤ (size A) := by
  if hs : (size A) = (size B) then
    simp_all
  else
    rw [← Relation.reflGen_transGen] at h
    match h with
    | .refl => grind
    | .single h =>
      have hn' : B.size < A.size := RedAff.instRedRel.to_trans.decreasing h
      grind

@[grind ., grind →]
theorem red_aff_trans_decreasing.{u} {τ : Type u} {A B : GenericExpr τ} [DecidableEq τ] : Relation.TransGen (RedAff (τ := τ)) A B → (size B) < (size A) :=
  RedAff.instRedRel.to_trans.decreasing

@[dcc_force_reduce, dcc_force_aff]
abbrev RedAff.reduce.{u} {τ : Type u} := GenericExpr.reduce (RedAff (τ := τ))

attribute [dcc_force_reduce, dcc_force_aff] RedAff.reduce.eq_def

instance RedAff.instDecidableNorm.{u} {α : Type u} [DecidableEq α]
{A : GenericExpr α}  : Decidable (IsNorm (RedAff (τ := α)) A) :=
  match heq₀ : GenericExpr.reduce RedAff A with
  | ⟨A', ⟨h⟩⟩ =>
    if heq : A' = A then
      have h_norm := reduce_norm (h := heq ▸ h) (A := A) (B := A) (hR := RedAff.instRedRel) (heq ▸ heq₀)
      .isTrue (fun ⟨a, b⟩ => by
        exact h_norm ⟨_, b⟩)
    else
      .isFalse (fun h => by
        have h := RedAff.instRedRel.reduce_norm_fst h
        simp_all)

@[dcc_judge]
def RedAffReflTrans.{u} {τ : Type u} := Relation.ReflTransGen (RedAff (τ := τ))

theorem RedAffReflTrans.reflGen_transGen.{u} {τ : Type u} : Relation.ReflGen (Relation.TransGen RedAff) = RedAffReflTrans (τ := τ) :=
  Relation.reflGen_transGen

@[dcc_judge]
def RedAffTrans.{u} {τ : Type u} := Relation.TransGen (RedAff (τ := τ))

namespace RedAffTrans

def single (r : RedAff A B) : RedAffTrans A B := Relation.TransGen.single r

def trans (r₁ : RedAffTrans A B) (r₂ : RedAffTrans B C) : RedAffTrans A C := Relation.TransGen.trans r₁ r₂

def to_reflTrans {a b : Expr} (r : RedAffTrans a b) : RedAffReflTrans a b :=
  Relation.TransGen.to_reflTransGen (a := a) (b := b) r

end RedAffTrans

namespace RedAffReflTrans

def cases_head.{u} {τ : Type u} {a b : GenericExpr τ} (r : RedAffReflTrans a b) :=
  Relation.ReflTransGen.cases_head (a := a) (b := b) r

def single.{u} {τ : Type u} {A B : GenericExpr τ}
  (r : RedAff A B) : (RedAffReflTrans (τ := τ)) A B := Relation.ReflTransGen.single r

def trans.{u} {τ : Type u} {A B C : GenericExpr τ} (r₁ : RedAffReflTrans A B)
  (r₂ : RedAffReflTrans B C) : RedAffReflTrans A C := Relation.ReflTransGen.trans r₁ r₂

def conf.{u} {τ : Type u} {A B C : GenericExpr τ} (h₁ : RedAffReflTrans A B) (h₂ : RedAffReflTrans A C) : ∃ D, RedAffReflTrans B D ∧ RedAffReflTrans C D := RedAff.instRedRel.globally_confluent.conf h₁ h₂

def elim_head_norm.{u} {τ : Type u} {A B : GenericExpr τ} (h : RedAffReflTrans A B) (hn : IsNorm RedAff A) : A = B :=
  hn.unique_refl h

@[grind ., grind →]
theorem red_aff_decreasing?.{u} {τ : Type u} {A B : GenericExpr τ} [DecidableEq τ] (h : (RedAffReflTrans (τ := τ)) A B) : (size B) ≤ (size A) := by
  if hs : (size A) = (size B) then
    simp_all
  else
    rw [← reflGen_transGen] at h
    match h with
    | .refl => grind
    | .single h =>
      have hn' : B.size < A.size := RedAff.instRedRel.to_trans.decreasing h
      grind

def elim_norm (hr : RedAffReflTrans A B) (hn : IsNorm RedAff A) : A = B := by
  change Relation.ReflTransGen _ _ _ at hr
  exact hn.unique_refl hr

@[grind ., grind <=]
theorem elim_norm' (hr : RedAffReflTrans A B) (hn : IsNorm RedAff A) : A = B := by
  change Relation.ReflTransGen _ _ _ at hr
  exact hn.unique_refl hr

def push_head (hr₁ : RedAffReflTrans A C) (hn : IsNorm RedAff C) (hr₂ : RedAff A B) : RedAffReflTrans B C :=
  have ⟨_, h₁, h₂⟩ := RedAff.instRedRel.globally_confluent.conf hr₁ (.single hr₂)
  hn.unique_refl h₁ ▸ h₂

end RedAffReflTrans

namespace RedAffTrans

@[grind ., grind →]
theorem red_aff_trans_decreasing.{u} {τ : Type u} {A B : GenericExpr τ} [DecidableEq τ] : (RedAffTrans (τ := τ)) A B → (size B) < (size A) := by
  change Relation.TransGen _ _ _ → _
  exact (RedAff.instRedRel (τ := τ)).to_trans.decreasing

end RedAffTrans

namespace RedAff

abbrev decreasing.{u} {τ : Type u} (x y : GenericExpr τ) := (RedAff.instRedRel (τ := τ)).decreasing (x := x) (y := y)

end RedAff

namespace RedAffReflTrans

def push_head' (hr₁ : RedAffReflTrans A C) (hn : IsNorm RedAff C) (hr₂ : RedAffReflTrans A B) : RedAffReflTrans B C := by
  have ⟨_, h₁, h₂⟩ := hr₁.conf hr₂
  have heq := hn.unique_refl h₁
  exact heq ▸ h₂

@[grind ., grind →]
theorem decreasing?.{u} {τ : Type u} {A B : GenericExpr τ} [DecidableEq τ] (h : (RedAffReflTrans (τ := τ)) A B) : (size B) ≤ (size A) := red_aff_decreasing? h

end RedAffReflTrans

inductive RedAffNorm : GenericExpr τ → NormExpr (RedAff (τ := τ)) → Type u
  | mk : (hr : RedAffReflTrans A B) → (hn : IsNorm RedAff B) → RedAffNorm A ⟨B, hn⟩
deriving DecidableEq, Repr

@[dcc_step]
def RedAffNorm.decreasing? (h : RedAffNorm A B) : B.size ≤ A.size :=
  match h with
  | ⟨hr, _hn⟩ => GenericExpr.decreasing? _ hr

@[grind]
def RedAffNorm.raw (_r : RedAffNorm (τ := τ) A B) : NormExpr (RedAff (τ := τ)) := B

@[dcc_step]
def RedAffNorm.is_norm (r : RedAffNorm (τ := τ) A B) : IsNorm RedAff B.raw :=
  match r with
  | ⟨_ha, hb⟩ => hb

@[grind]
def aff_sound (heq : reduce RedAff A = ⟨B, ⟨h⟩⟩) : RedAffNorm A ⟨B, reduce_norm heq⟩ := ⟨reduce_sound heq, reduce_norm heq⟩

@[grind, dcc_force_reduce, aesop unsafe norm (rule_sets := [DccForceReduce])]
def aff_sound' (A : GenericExpr τ) : RedAffNorm A ⟨(reduce RedAff A).fst, reduce_norm rfl⟩ := ⟨reduce_sound rfl, reduce_norm rfl⟩

@[grind, inline, dcc_reduce]
def red_aff (A : GenericExpr τ) : NormExpr (RedAff (τ := τ)) := ⟨(reduce RedAff A).fst, reduce_norm (A := A) rfl⟩

@[aesop safe forward (rule_sets := [DccReduce]), dcc_rel]
def RedAffNorm.complete {A : GenericExpr τ} {B : NormExpr RedAff (τ := τ)} (h : RedAffNorm A B) : red_aff A = B :=
  match h with
  | ⟨hr, hn⟩ => by
    have ha := reduce_complete_fst hr hn
    simp [red_aff, ha]

@[aesop safe forward (rule_sets := [DccReduce]), dcc_rel]
def RedAffNorm.complete_fst {A : GenericExpr τ} (h : RedAffNorm A ⟨B, hn_B⟩) : (reduce RedAff A).fst = B :=
  match h with
  | ⟨hr, hn⟩ => by
    have ha := reduce_complete_fst hr hn
    simp [ha]

@[aesop safe forward (rule_sets := [DccReduce]), dcc_rel]
def RedAffNorm.complete_snd {A : GenericExpr τ} (h : RedAffNorm A ⟨B, hn_B⟩) : (reduce RedAff A).snd = ⟨reduce_sound rfl⟩ :=
  match h with
  | ⟨hr, hn⟩ => by simp

@[dcc_reduce]
def RedAffNorm.eq (hr : RedAffNorm e (red_aff e)) : hr = aff_sound rfl :=
  match hr with
  | ⟨hr, hn⟩ => by
    have heq := reduce_complete hr hn
    grind

abbrev RedAffNorm.red (h : RedAffNorm A ⟨B, hn⟩) : RedAffReflTrans A B :=
  match h with
  | ⟨hr, _⟩ => hr

def RedAffNorm.aff_complete (h : RedAffNorm A ⟨B, hn⟩) : reduce RedAff A = ⟨B, ⟨h.red⟩⟩ :=
  match h with
  | ⟨hr₁, hn₁⟩ => reduce_complete hr₁ hn₁

def RedAffNorm.out_eq (h : RedAffNorm A B) : B = (red_aff A) :=
  match h with
  | .mk hr hn => by
    have heq := reduce_complete hr hn
    rw [red_aff]
    aesop

@[ext]
def RedAffNorm.ext (h₁ h₂ : RedAffNorm A B) : h₁ = h₂ := by
  match h₁ with
  | ⟨hr₁, hn₁⟩ =>
    match h₂ with
    | ⟨hr₂, hn₂⟩ =>
      dcc_simp_all

@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])]
def RedAffNorm.unique (h₁ : RedAffNorm A B) (h₂ : RedAffNorm A C) : B = C :=
  match h₁, h₂ with
  | ⟨ha, hb⟩, ⟨hc, hd⟩ => NormExpr.ext (norm_unique ha hb hc hd)

@[macro_inline, dcc_size, aesop safe apply (rule_sets := [DccSize]) ]
def RedAffNorm.absurd {P : Sort v} (h₁ : RedAffNorm A B) (h₂ : RedAffNorm A C) (hneq : B ≠ C := by intro h; cases h) : P :=
  _root_.absurd (h₁.unique h₂) (by simp_all)

def RedAffNorm.elim_norm (hr : RedAffNorm A B) (hn : IsNorm RedAff A) : B = ⟨A, hn⟩ :=
  match hr with
  | ⟨hr, _hn⟩ => by
    have h := hn.unique_refl hr
    cases h
    grind

def RedAffNorm.push_head (hrt : RedAffNorm A C) (hr : RedAff A B) : RedAffNorm B C :=
  match hrt with
  | ⟨hrt, hn⟩ => ⟨hrt.push_head hn hr, hn⟩

open Congruent in
def RedAffNorm.congrFun (hrt : RedAffNorm (DCC? (f x)) C) (hrt_f : RedAffNorm f ⟨f', hn_f⟩) : RedAffNorm (DCC? (f' x)) C :=
  match hrt, hrt_f with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, _hn₂⟩ =>
    ⟨
      have ⟨_, h₁, h₂⟩ := hr₁.conf (Congruent.congrFun' (hR := RedAff.instCongruent.reflTrans) hr₂)
      hn₁.unique_refl h₁ ▸ h₂, hn₁⟩

open Congruent in
def RedAffNorm.congrArg (hrt : RedAffNorm (DCC? (f x)) C) (hrt_x : RedAffNorm x ⟨x', hn_f⟩) : RedAffNorm (DCC? (f x')) C :=
  match hrt, hrt_x with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, _hn₂⟩ =>
    ⟨
      have ⟨_, h₁, h₂⟩ := hr₁.conf (Congruent.congrArg' (hR := RedAff.instCongruent.reflTrans) hr₂)
      hn₁.unique_refl h₁ ▸ h₂, hn₁⟩

namespace IsNorm

def map (h : IsNorm RedAff (.map f)) : IsNorm RedAff f :=
  fun ⟨_, hr⟩ => h ⟨_, .map₀ hr⟩

def unbox (h : IsNorm RedAff (.unbox f)) : IsNorm RedAff f :=
  fun ⟨_, hr⟩ => h ⟨_, .unbox₀ hr⟩

def box₀ (h : IsNorm RedAff (DCC? (& x))) : IsNorm RedAff x :=
  fun ⟨_, hr⟩ => h ⟨_, .box₀ hr⟩

end IsNorm

def RedAff.elim_norm (hr : RedAff A B) (hn : IsNorm RedAff A) : False := by
  have h := hn.unique hr
  have h_dec := hr.decreasing
  grind

def RedAff.size_absurd (hr : RedAff A B) (h_size_eq : size A ≤ size B := by grind) : False := by
  have h_dec := hr.decreasing
  grind

end GenericExpr

abbrev Expr.RedAff := GenericExpr.RedAff (τ := Unit)
