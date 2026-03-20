import Dcc.Ast
import Dcc.Eval
import Dcc.EvalPi
import Mathlib.Data.Nat.Notation

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

inductive Judge : Expr → Expr → Prop
  | app   : Judge (SK Π α, β) f
    → Judge α x
    → Expr.RedAppTy (SK ((Π α, β) x)) β'
    → Judge β' (SK (f x))
  | srt   : Judge    (SK Sort m.succ) (SK Sort m)
  | k     : Judge    (K.type m n) (SK K.{[m, n]})
  | k'    : Judge    (K'.type m n) (SK K'.{[m, n]})
  | s     : Judge    (S.type m n o) (SK S.{[m, n, o]})
  | conv  {α β : Expr} : Judge α x → Expr.RedTyReflTrans α β → Expr.IsNorm β → Judge β x

def infer (e : Expr) : Option ((t : Expr) × PLift (Judge t e)) :=
  match h_eq : e with
  | SK Sort m => .some ⟨SK Sort m.succ, ⟨.srt⟩⟩
  | SK K.{[m, n]} => .some ⟨K.type m n, ⟨.k⟩⟩
  | SK K'.{[m, n]} => .some ⟨K'.type m n, ⟨.k'⟩⟩
  | SK S.{[m, n, o]} => .some ⟨S.type m n o, ⟨.s⟩⟩
  | SK (f x) => do
    let ⟨t_f, ⟨h_t_f⟩⟩ ← infer f
    let ⟨t_x, ⟨h_t_x⟩⟩ ← infer x

    let α₂ := t_x.reduce
    let t_f' := t_f.reduce

    match heqf : t_f' with
    | (SK Π α, β) =>
      let h_t_f' := reduce_sound (e := t_f) (e' := (SK Π α, β)) heqf
      let h_t_x' := reduce_sound (e := t_x) (e' := α₂) rfl

      dbg_trace α
      dbg_trace α₂

      if heq : α = α₂ then
        match hsomeq : (SK ((Π α, β) x)).red_app_ty with
        | .some β' => .some ⟨β',
          ⟨.app (.conv h_t_f h_t_f' (reduce_norm heqf))
          (heq ▸ (.conv h_t_x h_t_x' (reduce_norm rfl)))
          (red_app_ty_sound hsomeq)⟩⟩
        | .none => .none
      else
        .none
    | _ => .none
  | _ => .none

/-
Challenge: inference for Π:

we can probably do this more reliably. we're not type-checking terms.

cases:
- atomic type (e.g., Srt) as codomain. we can infer that easily.

-/

#eval (infer (SK (K'.{[2, 2]} (Sort 1) (Sort 1) (Sort 0) (Sort 0)))).map (·.fst)
