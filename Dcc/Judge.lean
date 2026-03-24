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

def Expr.push_ctx (Γ x : Expr) : Expr :=
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

inductive JudgePi : (args : Expr) → Expr → Expr → Prop
  | tail : (SK (args α)).RedTyTrans α'
    → JudgePi (args.push_ctx (SK (__ ∶ α'))) t_β xs
    → JudgePi args t_β (SK (cons α xs))
  | base : (SK (args cod)).RedTyTrans (SK __ ∶ Sort m)
    → JudgePi (SK Sort m) args (SK cod)

def infer_pi (head spine : Expr) : Option ((t : Expr) × PLift (JudgePi spine t head)) :=
  match _h_eq : head, spine with
  | SK (cons α xs), args =>
    match (SK (args α)).reduce!? with
    | .some ⟨α', ⟨hrt, _h_norm⟩⟩ =>
      let _h_size_dec := hrt.decreasing'
      match infer_pi xs (args.push_ctx (SK (__ ∶ α'))) with
      | .some ⟨t_β, ⟨h_pi⟩⟩ => .some ⟨t_β, ⟨.tail hrt h_pi⟩⟩
      | .none => .none
    | .none => .none
  | _, _ => .none

inductive Judge : Expr → Expr → Prop
  | app     : Judge (SK ⟨(cons α xs), args⟩) f
    → (SK (args α)).RedTyTrans α'
    → Judge α' x
    → Judge (SK ⟨xs, #(args.push_ctx x)⟩) (SK (f x))
  | srt     : Judge (SK Sort m.succ) (SK Sort m)
  | k       : Judge (K.type m n) (SK K.{[m, n]})
  | k'      : Judge (K'.type m n) (SK K'.{[m, n]})
  | s       : Judge (S.type m n o) (SK S.{[m, n, o]})
  | pi      : JudgePi args t_β tys
    → Judge t_β (SK ⟨tys, args⟩)
  | hole    : Judge α (SK __ ∶ α) -- only visible to the kernel
  | conv  {α β : Expr} : Judge α x → α.RedTyTrans β → Expr.IsNorm β → Judge β x

def Judge.conv? (h_t : Judge α x) : Option ((t' : Expr) × (PLift (Judge t' x))) :=
  match α.reduce!? with
  | .some ⟨t', ⟨h_r, h_norm⟩⟩ => .some ⟨t', ⟨Judge.conv h_t h_r h_norm⟩⟩
  | _ => .none

def Judge.convD (h_t : Judge α x) : (t' : Expr) × (PLift (Judge t' x)) :=
  h_t.conv?.getD ⟨α, ⟨h_t⟩⟩

def infer (e : Expr) : Option ((t : Expr) × PLift (Judge t e)) :=
  match _h_eq : e with
  | SK Sort m => .some ⟨SK Sort m.succ, ⟨.srt⟩⟩
  | SK K.{[m, n]} => .some ⟨K.type m n, ⟨.k⟩⟩
  | SK K'.{[m, n]} => .some ⟨K'.type m n, ⟨.k'⟩⟩
  | SK S.{[m, n, o]} => .some ⟨S.type m n o, ⟨.s⟩⟩
  | SK ⟨tys, args⟩ =>
    match infer_pi tys args with
    | .some ⟨t, ⟨j_t⟩⟩ => .some <| ⟨t, ⟨.pi j_t⟩⟩
    | .none => .none
  | SK (f x) => do
    let ⟨t_f, ⟨h_t_f⟩⟩ ← infer f
    let ⟨t_x, ⟨h_t_x⟩⟩ ← infer x

    let ⟨t_f, ⟨h_t_f⟩⟩ := h_t_f.convD
    let ⟨t_x, ⟨h_t_x⟩⟩ := h_t_x.convD

    match t_f with
    | (SK ⟨⟨α, xs⟩, args⟩) =>
      match (SK (args α)).reduce!? with
      | .some ⟨α', ⟨h_red_α, _h_norm⟩⟩ =>
        if heq : α' = t_x then
          let β' := (SK ⟨xs, #(args.push_ctx x)⟩)
          let h_app := Judge.app (x := x) (f := f) h_t_f h_red_α (by rw [heq]; exact h_t_x)
          .some h_app.convD
        else
          .none
      | _ => .none
    | _ => .none
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
