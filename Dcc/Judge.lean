import Dcc.Ast
import Dcc.Eval
import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Relation

/-
(B (C I arg) I) head
I head
(C I arg) (I head)
I head arg

-/

def Γ.push (Γ x : Expr) : Expr :=
  SK (B (C I x) Γ)

def K.type (m n : Level) : Expr := SK ⟨⟨Sort m, arg 0 (C cons (K* Sort n)), ret 1, arg 1 (ret 1), ret 3⟩, I⟩

--#eval Std.format <| ((K.type 1 1).reduce_pi (SK Sort 0)).fst

def K'.type (m n : Level) : Expr :=
  SK ⟨⟨Sort m, (K* (Sort n)), (arg 0 (ret 1)), (arg 1 (ret 1)), (arg 0 (ret 3))⟩, I⟩

def S.type (m n o : Level) : Expr := SK
    ⟨⟨Sort m, -- α
    arg 0 (C cons (K* Sort n)), -- β
    (B (B (C cons) (C cons (K* Sort o))) (C I)),
    (C (B B (B B cons)) cons), -- x
    (B (B K* K*) cons), -- y
    (arg 0 (ret 4)), -- z
      (B (S.{[m, n, o.succ]}
        (__ ∶ Sort m)
        (__ ∶ Sort n)
        (__ ∶ Sort o)) (arg 2 (ret 1)))⟩, I⟩

def Expr.reduce!? (e : Expr) : Option ((e' : Expr) × (PLift (Expr.RedTyTrans e e' ∧ IsNorm e'))) :=
  let e' := e.reduce
  let proof : Relation.ReflTransGen Expr.RedTy e e' := reduce_sound rfl
  let norm : IsNorm e' := reduce_norm rfl
  if heq : e = e' then
    .none
  else
    .some ⟨e', ⟨by
    rw [← Relation.reflGen_transGen] at proof
    match heq₂ : proof with
    | .refl => contradiction
    | .single h =>
      rename_i heq
      exact ⟨h, heq ▸ norm⟩⟩⟩

inductive IsNotPi : Expr → Prop
  | hole   : IsNotPi (SK __ ∶ α)
  | t_comb : IsNotPi (.tycomb c)
  | comb   : IsNotPi (.comb c)
  | srt    : IsNotPi (.Srt m)
  | app    : IsNotPi (SK (f x))

def is_not_pi (e : Expr) : Option (PLift (IsNotPi e)) :=
  match e with
  | (SK __ ∶ _α) => .some ⟨.hole⟩
  | (.tycomb _c) => .some ⟨.t_comb⟩
  | (.comb _c) => .some ⟨.comb⟩
  | (SK Sort _m) => .some ⟨.srt⟩
  | (SK (_f _x)) => .some ⟨.app⟩
  | _ => .none

inductive FanPi (x : Expr) : Expr → Expr → Prop
  | pi  : FanPi x α α' → FanPi x β β'
    → FanPi x (SK Π α, β) (SK Π α', β')
  | app : IsNotPi e → FanPi x e (SK (e x))

inductive RunPi : Expr → Expr → Prop
  | pi  : RunPi α α' → RunPi β β'
    → RunPi (SK Π α, β) (SK Π α', β')
  | app : IsNotPi e → e.RedTyTrans e' → e'.IsNorm → RunPi e e'

theorem RunPi.IsNorm : RunPi t t' → t'.IsNorm := by
  intro h ⟨t'', h_e⟩
  induction h generalizing t'' with
  | pi => contradiction
  | app h_not_pi h_trans h_norm => exact h_norm ⟨_, by assumption⟩

inductive CountPi : Expr → ℕ → Prop
  | pi   : CountPi α m → CountPi β n → CountPi (SK (Π α, β)) (2 * (max m n))
  | leaf : IsNotPi e   → e.TySize m → CountPi e m

theorem RunPi.decreasing : RunPi t t' → CountPi t m → ∃ n, CountPi t' n ∧ n < m := by
  intro h_r ht
  induction h_r generalizing m with
  | pi rα rβ ih₁ ih₂ =>
    cases ht with
    | pi =>
      have ha := ih₁ (by assumption)
      have hb := ih₂ (by assumption)
      have ⟨n₁, hn₁, h_lt₁⟩ := ha
      have ⟨n₂, hn₂, h_lt₂⟩ := hb
      refine ⟨2 * (max n₁ n₂), .pi hn₁ hn₂, by grind⟩
    | leaf => contradiction

def Expr.count_pi (e : Expr) : ((n : ℕ) × (PLift (CountPi e n))) :=
  match e with
  | SK (Π α, β) =>
    let ⟨m, ⟨h₁⟩⟩ := α.count_pi
    let ⟨n, ⟨h₂⟩⟩ := β.count_pi

    ⟨2 * (max m n), ⟨.pi h₁ h₂⟩⟩
  | (SK __ ∶ _α) => ⟨0, ⟨.leaf .hole (TySize.sound rfl)⟩⟩
  | (SK Sort _m) => ⟨0, ⟨.leaf .srt (TySize.sound rfl)⟩⟩
  | (.comb _c) => ⟨0, ⟨.leaf .comb (TySize.sound rfl)⟩⟩
  | (.tycomb c) => ⟨(ty_size (.tycomb c)), ⟨.leaf .t_comb (TySize.sound rfl)⟩⟩
  | (SK (f x)) => ⟨(ty_size (SK (f x))), ⟨.leaf .app (TySize.sound rfl)⟩⟩

def fan_pi (x in_e : Expr) : Option ((e' : Expr) × (PLift (FanPi x in_e e'))) :=
  match in_e with
  | SK Π α, β =>
    match fan_pi x α, fan_pi x β with
    | .some ⟨α', ⟨hα⟩⟩, .some ⟨β', ⟨hβ⟩⟩ => .some ⟨(SK Π α', β'), ⟨.pi hα hβ⟩⟩
    | _, _ => .none
  | e => match is_not_pi e with
    | .some ⟨h_not_pi⟩ => .some ⟨SK (e x), ⟨.app (x := x) (e := e) h_not_pi⟩⟩
    | _ => .none

def run_pi (in_e : Expr) : Option ((e' : Expr) × (PLift (RunPi in_e e'))) :=
  match in_e with
  | SK Π α, β =>
    match run_pi α, run_pi β with
    | .some ⟨α', ⟨hα⟩⟩, .some ⟨β', ⟨hβ⟩⟩ => .some ⟨(SK Π α', β'), ⟨.pi hα hβ⟩⟩
    | _, _ => .none
  | e => match is_not_pi e with
    | .some ⟨h_not_pi⟩ =>
      match e.reduce!? with
      | .some ⟨e', ⟨h, h_norm⟩⟩ => .some ⟨e', ⟨.app h_not_pi h h_norm⟩⟩
      | _ => .none
    | _ => .none

/-
Judgments for Π combinators work inversely.

We use "typed holes." We find the innermost type combinator,
whose size is greater than 0 (Π binders have size zero), and accumulate "typed holes" as we recurse.
-/
inductive FoldElimPi : (fold : Expr → Expr) → Expr → Expr → Prop
  | single : e.TySize (m + 1)
    → FoldElimPi fold e (fold e)
  | tail   : FoldElimPi ((Expr.app · (SK (__ ∶ α))) ∘ fold) β γ
    → FoldElimPi fold (SK Π α, β) γ

def Expr.fold_elim_pi (fold : Expr → Expr) (in_e : Expr) : (Option ((e' : Expr) × (PLift (FoldElimPi fold in_e e')))) :=
  match hneq : in_e.ty_size, heeq : in_e with
  | .zero, (SK Π α, β) => match β.fold_elim_pi ((Expr.app · (SK (__ ∶ α))) ∘ fold) with
    | .some ⟨γ, ⟨h⟩⟩ => .some ⟨γ, ⟨.tail h⟩⟩
    | .none => .none
  | .succ _n, in_e => .some ⟨fold in_e, ⟨.single (Expr.TySize.sound (heeq ▸ hneq))⟩⟩
  | _, _ => .none

inductive Judge : Expr → Expr → Prop
  | app     : Judge (SK Π α, β) f
    → Judge α x
    → FanPi x β β'
    → Judge β' (SK (f x))
  | srt     : Judge (SK Sort m.succ) (SK Sort m)
  | k       : Judge (K.type m n) (SK K.{[m, n]})
  | k'      : Judge (K'.type m n) (SK K'.{[m, n]})
  | s       : Judge (S.type m n o) (SK S.{[m, n, o]})
  | pi      : FoldElimPi id (SK Π α, β) elim
    → RunPi elim (SK __ ∶ t_β)
    → Judge t_β (SK Π α, β)
  | hole    : Judge α (SK __ ∶ α)-- only visible to the kernel
  | conv  {α β : Expr} : Judge α x → RunPi α β → Expr.IsNorm β → Judge β x

def Judge.conv? (h_t : Judge α x) : Option ((t' : Expr) × (PLift (Judge t' x))) :=
  match run_pi α with
  | .some ⟨t', ⟨h_r⟩⟩ => .some ⟨t', ⟨Judge.conv h_t h_r h_r.IsNorm⟩⟩
  | _ => .none

def Judge.convD (h_t : Judge α x) : (t' : Expr) × (PLift (Judge t' x)) :=
  h_t.conv?.getD ⟨α, ⟨h_t⟩⟩

def infer (e : Expr) : Option ((t : Expr) × PLift (Judge t e)) :=
  match _h_eq : e with
  | SK Sort m => .some ⟨SK Sort m.succ, ⟨.srt⟩⟩
  | SK K.{[m, n]} => .some ⟨K.type m n, ⟨.k⟩⟩
  | SK K'.{[m, n]} => .some ⟨K'.type m n, ⟨.k'⟩⟩
  | SK S.{[m, n, o]} => .some ⟨S.type m n o, ⟨.s⟩⟩
  | SK (f x) => do
    let ⟨t_f, ⟨h_t_f⟩⟩ ← infer f
    let ⟨t_x, ⟨h_t_x⟩⟩ ← infer x

    let ⟨t_f, ⟨h_t_f⟩⟩ := h_t_f.convD
    let ⟨t_x, ⟨h_t_x'⟩⟩ := h_t_x.convD

    match t_f with
    | (SK Π α, β) =>
      if heq : α = t_x then
        let β' ← fan_pi x β
        let h_app := Judge.app (x := x) (f := f) h_t_f (by cases heq; exact h_t_x') β'.snd.down
        .some h_app.convD
      else
        .none
    | _ => .none
  | SK Π α, β =>
    match (SK Π α, β).fold_elim_pi id with
    | .some ⟨elim, ⟨h⟩⟩ =>
      match run_pi elim with
      | .some ⟨SK __ ∶ t_β, ⟨h_red⟩⟩ => .some ⟨t_β, ⟨.pi h h_red⟩⟩
      | _ => none
    | _ => none
  | _ => .none

theorem app_size_dec : Judge (SK (Π α, β)) f
  → (SK (f x)).RedTm e'
  → Judge t' e'
  → FanPi x β β'
  → CountPi β' m
  → CountPi t' n
  → n < m := by
  intro h_t_f h_red h_t_e' h_fan h_m h_n
  cases h_red with
  | k' =>
    
    sorry

#eval (infer (SK (K'.{[2, 2]} (Sort 1) (Sort 1) (Sort 0) (Sort 0)))).map (·.fst)
