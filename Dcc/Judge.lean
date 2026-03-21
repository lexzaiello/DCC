import Dcc.Ast
import Dcc.Eval
import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Relation

/-
our decreasing measure is implicit Π substitution.

counting becomes easier if we have a Π combinator, since we have to manually pass things around.

the challenge is, we still need a top-level construct to copy things, or some kind of context.

Contexts are cringe.

With minimal change, we can probably still count the decreasing measure.

our current approach might be fine. we need to stop treating Π copying like some kind of
algebraic rule. it's not. our old "RunPi" rule was pretty good.

We have a predicatre "IsBinder"
-/

def K.type (m n : Level) : Expr := (SK
  Π Sort m, Π (Π (arg 0 I), Sort n), Π (arg 0 (ret 1)), Π (arg 1 I), (arg 0 (ret 3)))

--#eval Std.format <| ((K.type 1 1).reduce_pi (SK Sort 0)).fst

def K'.type (m n : Level) : Expr :=
  (SK Π Sort m, Π (K* (Sort n)), Π (arg 0 (ret 1)), Π (arg 1 (ret 1)), (arg 0 (ret 3)))

def S.type (m n o : Level) : Expr := (SK
    Π Sort m, -- α
    Π (Π (arg 0 I), Sort n), -- β
    Π (Π (arg 0 (ret 1)), Π (arg 1 I), Sort o), -- γ
    Π (Π (arg 0 (ret 2)), Π (arg 1 (ret 1)), (arg 2 I)), -- x
    Π (Π (arg 0 (ret 3)), (arg 1 (ret 2))), -- y
    Π (arg 0 (ret 4)), -- z
      (B (S.{[m, n, o.succ]}
        (__ ∶ Sort m)
        (__ ∶ Sort n)
        (__ ∶ Sort o)) (arg 2 (ret 1)))) -- γ z (y z)
-- ^ note that this is safe, since prior apps were type-checked, and def-eq here is deferred to term-level

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

inductive RunPi (x : Expr) : Expr → Expr → Prop
  | pi  : RunPi x α α' → RunPi x β β'
    → RunPi x (SK Π α, β) (SK Π α', β')
  | app : IsNotPi e → (SK (e x)).RedTyTrans e' → RunPi x e e'

def run_pi (x in_e : Expr) : Option ((e' : Expr) × (PLift (RunPi x in_e e'))) :=
  match in_e with
  | SK Π α, β =>
    match run_pi x α, run_pi x β with
    | .some ⟨α', ⟨hα⟩⟩, .some ⟨β', ⟨hβ⟩⟩ => .some ⟨(SK Π α', β'), ⟨.pi hα hβ⟩⟩
    | _, _ => .none
  | e => match is_not_pi e with
    | .some ⟨h_not_pi⟩ =>
      match (SK (e x)).reduce!? with
      | .some ⟨e', ⟨h, _⟩⟩ => .some ⟨e', ⟨.app h_not_pi h⟩⟩
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
    → RunPi x β β'
    → Judge β' (SK (f x))
  | srt     : Judge (SK Sort m.succ) (SK Sort m)
  | k       : Judge (K.type m n) (SK K.{[m, n]})
  | k'      : Judge (K'.type m n) (SK K'.{[m, n]})
  | s       : Judge (S.type m n o) (SK S.{[m, n, o]})
  | pi      : FoldElimPi id (SK Π α, β) elim
    → Expr.RedTyTrans elim (SK __ ∶ t_β)
    → Judge t_β (SK Π α, β)
  | hole    : Judge α (SK __ ∶ α)-- only visible to the kernel
  | conv  {α β : Expr} : Judge α x → Expr.RedTyTrans α β → Expr.IsNorm β → Judge β x

def Judge.conv? (h_t : Judge α x) : Option ((t' : Expr) × (PLift (Judge t' x ∧ Expr.RedTyTrans α t'))) :=
  match α.reduce!? with
  | .some ⟨t', ⟨h_trans, h_norm⟩⟩ => .some ⟨t', ⟨Judge.conv h_t h_trans h_norm, h_trans⟩⟩
  | _ => .none

def Judge.convD (h_t : Judge α x) : (t' : Expr) × (PLift (Judge t' x)) :=
  match h_t.conv? with
  | .some ⟨t', ⟨h_t, _⟩⟩ => ⟨t', ⟨h_t⟩⟩
  | .none => ⟨α, ⟨h_t⟩⟩

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
        let β' ← run_pi x β
        .some ⟨β'.fst, ⟨Judge.app (x := x) (f := f) h_t_f (by cases heq; exact h_t_x') β'.snd.down⟩⟩
      else
        .none
    | _ => .none
  | SK Π α, β =>
    match (SK Π α, β).fold_elim_pi id with
    | .some ⟨elim, ⟨h⟩⟩ =>
      match elim.reduce!? with
      | .some ⟨SK __ ∶ t_β, ⟨h_red, _⟩⟩ => .some ⟨t_β, ⟨.pi h h_red⟩⟩
      | _ => none
    | _ => none
  | _ => .none

#eval (infer (SK (K'.{[2, 2]} (Sort 1) (Sort 1) (Sort 0) (Sort 0)))).map (·.fst)
