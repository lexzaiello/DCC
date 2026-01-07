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
  | _, _ => .none

def step (e : Expr) : Option Expr :=
  match e with
  | ⟪₂ :: exec (:: :ops :Γ) ⟫ =>
    match ops with
    | ⟪₂ (:: :x nil) ⟫ =>
      exec_op x Γ
    | l => l.map_list (fun e => (exec_op e Γ).getD e)
  


