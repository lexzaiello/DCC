import Cm.Ast

/-
Upon user request, a list may be treated as a series of instructions
for processing some datum.

There is support for piping, quotation, and some list operations.

The format looks like:

exec (:: f (:: g nil)) data

assert returns the current value in the tape,
or a specified value.

assert discards the context, producing a value.
assert does not expect (, Δ Ξ), but

-/
def exec_op (my_op : Expr) (ctx : Expr) : Expr :=
  match my_op, ctx with
  | ⟪₂ (:: map :_f) ⟫, ⟪₂ nil ⟫ =>
    ⟪₂ nil ⟫
  | ⟪₂ (:: map :f) ⟫, ⟪₂ :: :x nil ⟫ =>
    let x' := exec_op f x

    ⟪₂ (:: :x' nil) ⟫
  | ⟪₂ (:: map :f) ⟫, ⟪₂ :: :x :xs ⟫  =>
    let x' := exec_op f x
    let xs' := exec_op f xs

    ⟪₂ (:: :x' :xs') ⟫
  | ⟪₂ read ⟫, ⟪₂ (:: :x :_xs) ⟫ => x
  | ⟪₂ next ⟫, ⟪₂ (:: :_x :xs) ⟫ => xs
  | ⟪₂ fst ⟫, ⟪₂ (, :a :_b) ⟫ => a
  | ⟪₂ snd ⟫, ⟪₂ (, :_a :b) ⟫ => b
  | ⟪₂ (:: push_on nil) ⟫, c => ⟪₂ :: :c nil ⟫
  | ⟪₂ (:: push_on :x nil) ⟫, c => ⟪₂ :: :c :x ⟫
  | ⟪₂ (:: push_on (:: :x :xs)) ⟫, c => ⟪₂ :: :c (:: :x :xs) ⟫
  | ⟪₂ (:: push_on (, :a :b)) ⟫, c => ⟪₂ (, :c (, :a :b)) ⟫
  | ⟪₂ (:: assert :x) ⟫, _ => ⟪₂ , (:: (:: assert :x) nil) (, nil nil) ⟫
  | ⟪₂ quote ⟫, a => ⟪₂ (:: assert :a) ⟫
  | ⟪₂ assert ⟫, a => ⟪₂ , (:: (:: assert :a) nil) (, nil nil) ⟫
  | ⟪₂ (:: apply (:: :f :g)) ⟫, Γ =>
    let f' := exec_op f Γ
    let g' := exec_op g Γ

    match f', g' with
    | ⟪₂ quoted :f' ⟫, ⟪₂ quoted :g' ⟫ =>
      let unquoted := ⟪₂ :f' :g' ⟫.unquote_pure
      ⟪₂ quoted :unquoted ⟫
    | f', g' =>
      ⟪₂ :f' :g' ⟫
  | ⟪₂ (:: both (:: :f :g)) ⟫, Γ =>
    let f' := exec_op f Γ
    let g' := exec_op g Γ

    ⟪₂ (:: :f' :g') ⟫
  -- pipelining operations
  | ⟪₂ :: :f :g ⟫, ctx =>
    let x := exec_op f ctx

    ⟪₂ exec :g :x ⟫
  | _, _ => ⟪₂ nil ⟫

def step : Expr → Option Expr
  | ⟪₂ exec :f :ctx ⟫ => exec_op f ctx
  | ⟪₂ push_on nil :a ⟫ => ⟪₂ :: :a nil ⟫
  | ⟪₂ push_on (:: :x :xs) :a ⟫ => ⟪₂ :: :a (:: :x :xs) ⟫
  | ⟪₂ push_on (, :a :b) :c ⟫ => ⟪₂ (, :c (, :a :b)) ⟫
  | ⟪₂ push_on :l :a ⟫ => ⟪₂ :: :a :l ⟫
  | ⟪₂ I :_α :x ⟫ => x
  | ⟪₂ K :_α :_β :x :_y ⟫
  | ⟪₂ K' :_α :_β :x :_y ⟫ => x
  | ⟪₂ both :f :g :Γ ⟫ =>
    let left := ⟪₂ :f :Γ ⟫
    let right := ⟪₂ :g :Γ ⟫

    ⟪₂ :: (# (step left).getD left) (# (step right).getD right) ⟫
  | e@⟪₂ next (:: :_x nil) ⟫ => e
  | ⟪₂ read nil ⟫ => .none
  | ⟪₂ next (:: :_x :xs) ⟫ => xs
  | ⟪₂ read (:: :x :_xs) ⟫ => x
  | ⟪₂ fst (, :a :_b) ⟫ => a
  | ⟪₂ snd (, :_a :b) ⟫ => b
  | ⟪₂ , :a :b ⟫ => do ⟪₂ , (#(step a).getD a) (#(step b).getD b) ⟫
  | ⟪₂ :f :x ⟫ =>
    let f' := (step f).getD f
    let x' := (step x).getD x
    ⟪₂ :f' :x' ⟫
  | _ => .none

#eval step ⟪₂ exec
  (:: (:: assert (:: Data nil)) (:: (:: fst (:: read nil)) (:: (:: fst (:: read nil))) nil))
  (:: Data (:: Data nil)) ⟫

def try_step_n (n : ℕ) (e : Expr) : Option Expr := do
  if n = 0 then
    pure e
  else
    let e' ← step e
    pure <| (try_step_n (n - 1) e').getD e'

def try_step_n! (n : ℕ) (e : Expr) : Expr := (try_step_n n e).getD e
