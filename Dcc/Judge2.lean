import Dcc.Ast2
import Dcc.Eval2
import Mathlib.Data.Nat.Notation

def K.type (m n : Level) : Expr := (SK
  Π Sort m, Π (Π #(arg 0), Sort n), Π #((arg 0).ret 1), Π #(arg 1), #((arg 0).ret 3))

--#eval Std.format <| ((K.type 1 1).reduce_pi (SK Sort 0)).fst

def K'.type (m n : Level) : Expr :=
  (SK Π Sort m, Π Sort n, Π #((arg 0).ret 1), Π #((arg 1).ret 1), #((arg 0).ret 3))

def S.type (m n o : Level) : Expr := (SK
    Π Sort m, -- α
    Π (Π #(arg 0), Sort n), -- β
    Π (Π #((arg 0).ret 1), Π #(arg 1), Sort o), -- γ
    Π (Π #((arg 0).ret 2), Π #((arg 1).ret 1), #(arg 2)), -- x
    Π (Π #((arg 0).ret 3), #((arg 1).ret 2)), -- y
    Π #((arg 0).ret 4), -- z
      (B (S.{[m, n, o.succ]} (__ ∶ Sort m) (__ ∶ Sort n) (__ ∶ Sort o)) #((arg 2).ret 1))) -- γ z (y z)
-- ^ note that this is safe, since prior apps were type-checked, and def-eq here is deferred to term-level

inductive Judge : Expr → Expr → Prop
  | app   : Judge (SK Π α, β) f
    → Judge α x
    → RedPiArg x β β'
    → Judge β' (SK (f x))
  | srt   : Judge    (SK Sort m.succ) (SK Sort m)
  | k     : Judge    (K.type m n) (SK K.{[m, n]})
  | k'    : Judge    (K'.type m n) (SK K'.{[m, n]})
  | s     : Judge    (S.type m n o) (SK S.{[m, n, o]})
  | pi    : RedPiArg (SK __ ∶ α) β β' → Judge t_β β → Judge t_β (SK Π α, β)
  | conv  {α β : Expr} : Judge α x → Expr.TyRedReflTrans α β → Judge β x

def infer (e : Expr) : Option ((t : Expr) × PLift (Judge t e)) :=
  match h_eq : e with
  | SK Sort m => .some ⟨SK Sort m.succ, ⟨.srt⟩⟩
  | SK K.{[m, n]} => .some ⟨K.type m n, ⟨.k⟩⟩
  | SK K'.{[m, n]} => .some ⟨K'.type m n, ⟨.k'⟩⟩
  | SK S.{[m, n, o]} => .some ⟨S.type m n o, ⟨.s⟩⟩
  | SK (f x) => do
    let ⟨t_f, ⟨h_t_f⟩⟩ ← infer f
    let ⟨t_x, ⟨h_t_x⟩⟩ ← infer x
    let ⟨t_f', h_r_f⟩ := t_f.reduce_ty

    match heqf : t_f' with
    | (SK Π α, β) =>
      let ⟨α₂, hrx⟩ := t_x.reduce_ty

      if heq : α = α₂ then
        let ⟨β', h⟩ := β.reduce_pi_arg x
        .some <| ⟨β', ⟨.app (.conv h_t_f h_r_f) (by rw [heq]; exact (.conv h_t_x hrx)) h.down⟩⟩
      else
        .none
    | _ => .none
  -- | SK Π α, β => TODO TODO
  | _ => .none

#eval (infer (SK (K'.{[2, 2]} (Sort 1) (Sort 1) (Sort 0) (Sort 0)))).map (·.fst)
