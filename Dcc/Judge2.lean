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

def Expr.pi_size_of : Expr → ℕ
  | SK Π α, β => (α.pi_size_of + β.pi_size_of).succ
  | e => e.ty_size_of

theorem pi_size_of_decreasing : RedPiArg x (SK Π α, β) (SK Π α', β')
  → β'.pi_size_of < (SK Π α, β).pi_size_of := by
  intro h
  cases h
  · rename_i ih₁ ih₂
    sorry
  · rename_i h
    
    sorry

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

def mk_I (α : Expr) (m : Level) : Expr :=
  let α := α
  let y := SK (K'.{[2, m]} (Sort 1) α (Sort 0))
  let x := SK (K'.{[m, 2]} α (Sort 1))

  let β := SK (K'.{[3, m]} (Sort 2) α (Sort 1))
  let γ := SK (K'.{[m.succ, m]} ((Sort 1) → (Sort m)) α (K'.{[m.succ, 2]} (Sort m) (Sort 1) α))

  SK (S.{[m, 2, m]} α)

def test_S : Option Expr := do
  let s := SK S.{[3, 3, 3]}
  let α := SK (Sort 2)
  let z := SK (Sort 1)
  let y := SK (K'.{[3, 3]} (Sort 2) (Sort 2))
  let β ← match Sigma.fst <$> infer (SK (y (Sort 1))) with
  | .some β => do
    match ← Sigma.fst <$> infer α with
    | SK Sort out => .some (SK (K'.{[(out + 1), 3]} (Sort out) α β))
    | _ => .none
  | _ => none
  let t_yz ← (Sigma.fst <$> infer (SK (y z)))
  let t_t_yz ← Sigma.fst <$> infer t_yz
  let x ← match (Sigma.fst <$> infer t_yz) with
  | SK Sort m => .some (SK (K'.{[3, m]} α t_yz))
  | _ => .none
  let γ : Expr := ← (do
    let t_xzyz ← Sigma.fst <$> infer (SK (x z (y z)))
    let t_t_xzyz ← Sigma.fst <$> infer t_xzyz
    match t_xzyz, t_t_xzyz, t_t_yz with
    | t_out, (SK Sort out), (SK Sort yzm) =>
      let inner := (SK (K'.{[out.succ, yzm]} (Sort out) t_yz t_out))
      let t_inner ← Sigma.fst <$> (infer inner)
      match ← Sigma.fst <$> infer t_inner with
      | (SK Sort in_m) =>
        .some (SK (K'.{[in_m, 3]} t_inner α inner))
      | _ => .none
    | _, _, _ => .none
  )
  Sigma.fst <$> infer (SK (s α β γ x y z))

#eval test_S

