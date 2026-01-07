import Cm.Ast
import Cm.Error

/-
Minimal set of things we need:

- K, just read and next
- Dependent types, we need to be able to make new contexts. These are also represented by lists.
- Apply
- push_on

Ideal K type:
(:: Data (:: (:: read (:: push_on (:: Data nil))) (:: read (:: (:: apply (:: next read) (:: next (:: next read))) (:: read nil)))))

Making arrows:

Also don't really like nested exec.
Feels wrong.

Piping could be a lot cleaner.
-/

def exec_op (my_op : Expr) (ctx : Expr) : Option Expr :=
  match my_op, ctx with
  | ⟪₂ read ⟫, ⟪₂ :: :x :_xs ⟫ => x
  | ⟪₂ next ⟫, ⟪₂ :: :_x :xs ⟫ => xs
  | ⟪₂ :: next :f ⟫, ⟪₂ :: :_x :xs ⟫ => exec_op f xs
  | ⟪₂ :: read :f ⟫, ⟪₂ :: :x :_xs ⟫ => exec_op f x
  | ⟪₂ (:: push_on :l) ⟫, c => ⟪₂ :: :c :l ⟫
  | ⟪₂ :: both (:: :f :g) ⟫, c => do
    let f' ← exec_op f c
    let g' ← exec_op g c

    ⟪₂ :: :f' :g' ⟫
  | ⟪₂ :: apply (:: :f :g) ⟫, c => do
    match ← exec_op f c, ← exec_op g c with
    | ⟪₂ quoted :f ⟫, ⟪₂ quoted :x ⟫ =>
      ⟪₂ quoted (:f :x) ⟫
    | _, _ => .none
  | _, _ => .none

def step (e : Expr) : Option Expr :=
  match e with
  | ⟪₂ :: exec (:: :ops :Γ) ⟫ =>
    match ops with
    | ⟪₂ (:: :x nil) ⟫ =>
      exec_op x Γ
    | l => l.map_list (fun e => (exec_op e Γ).getD e)
  | ⟪₂ I :_α :x ⟫ => x
  | ⟪₂ K :_α :_β :x :_y ⟫
  | ⟪₂ K' :_α :_β :x :_y ⟫ => x
  | ⟪₂ S :_α :_β :_γ :x :y :z ⟫ => ⟪₂ (:x :z) (:y :z) ⟫
  | ⟪₂ :: :_a :_b ⟫ => .none
  | ⟪₂ :f :x ⟫ => do
    ⟪₂ (#← step f) :x ⟫
  | _ => .none

def try_step_n (n : ℕ) (e : Expr) : Option Expr := do
  if n = 0 then
    pure e
  else
    let e' ← step e
    pure <| (try_step_n (n - 1) e').getD e'

def unwrap_with {α : Type} (ε : Error) (o : Option α) : Except Error α :=
  (o.map Except.ok).getD (.error ε)

def do_step (e : Expr) : Except Error Expr :=
  unwrap_with (Error.stuck e) (try_step_n 30 e)

def try_step_n! (n : ℕ) (e : Expr) : Expr := (try_step_n n e).getD e

def my_k_type : Expr :=
  let t_α := ⟪₂ Data ⟫
  -- β : α → Type
  let α := ⟪₂ read ⟫
  let t_β := ⟪₂ :: :α (:: push_on (:: Data nil)) ⟫
  let β := ⟪₂ :: next read ⟫
  let x := ⟪₂ :: next (:: next read) ⟫

  let t_x := α
  -- y : β x
  let t_y := ⟪₂ :: apply (:: :β :x) ⟫

  let t_out := α

  ⟪₂ :: :t_α (:: :t_β (:: :t_x (:: :t_y (:: :t_out nil)))) ⟫

/-
Example k type:

K Data (I Data) Data Data

Also remember:
- our (I Data) term will be quoted.
-/

def test_
