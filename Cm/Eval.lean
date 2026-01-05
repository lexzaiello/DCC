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
  | ⟪₂ (:: map :f) ⟫, ⟪₂ :: :x :xs ⟫  =>
    let x' := ⟪₂ (:: exec (:: :f :x)) ⟫
    let xs' := ⟪₂ (:: exec (:: (:: map :f) :xs)) ⟫

    ⟪₂ (:: :x' :xs') ⟫
  | ⟪₂ (:: map :f) ⟫, e =>⟪₂ (:: exec :f :e) ⟫
  | ⟪₂ read ⟫, ⟪₂ (:: :x :_xs) ⟫ => x
  | ⟪₂ next ⟫, ⟪₂ (:: :_x :xs) ⟫ => xs
  | ⟪₂ fst ⟫, ⟪₂ (, :a :_b) ⟫ => a
  | ⟪₂ snd ⟫, ⟪₂ (, :_a :b) ⟫ => b
  | ⟪₂ (:: push_on nil) ⟫, c => ⟪₂ :: :c nil ⟫
  | ⟪₂ (:: push_on :x nil) ⟫, c => ⟪₂ :: :c :x ⟫
  | ⟪₂ (:: push_on (:: :x :xs)) ⟫, c => ⟪₂ :: :c (:: :x :xs) ⟫
  | ⟪₂ (:: push_on (, :a :b)) ⟫, c => ⟪₂ (, :c (, :a :b)) ⟫
  | ⟪₂ (:: assert :x) ⟫, _ => x
  | ⟪₂ quote ⟫, a => ⟪₂ (:: assert :a) ⟫
  | ⟪₂ assert ⟫, a => a
  | ⟪₂ (:: apply (:: :f :g)) ⟫, Γ =>
    let f' := ⟪₂ (:: exec (:: :f :Γ)) ⟫
    let g' := ⟪₂ (:: exec (:: :g :Γ)) ⟫

    ⟪₂ (:: apply (:: :f' :g')) ⟫

    /-match f', g' with
    | ⟪₂ quoted :f' ⟫, ⟪₂ quoted :g' ⟫ =>
      let unquoted := ⟪₂ :f' :g' ⟫.unquote_pure
      ⟪₂ quoted :unquoted ⟫
    | f', g' =>
      ⟪₂ :f' :g' ⟫ TODO: move to step-/
  | ⟪₂ (:: both (:: :f :g)) ⟫, Γ =>
    let f' := ⟪₂ (:: exec (:: :f :Γ)) ⟫
    let g' := ⟪₂ (:: exec (:: :g :Γ)) ⟫

    ⟪₂ (:: :f' :g') ⟫
  -- pipelining operations
  | ⟪₂ :: :f :g ⟫, ctx =>
    let x := ⟪₂ (:: exec (:: :f :ctx)) ⟫

    ⟪₂ (:: exec (:: :g :x)) ⟫
  | _, _ => ⟪₂ nil ⟫

def step : Expr → Option Expr
  | ⟪₂ (:: (:: exec :m) :xs) ⟫ => do
    let e' ← step ⟪₂ :: exec :m ⟫
    let xs' ← (step xs).getD xs
    pure ⟪₂ :: :e' :xs' ⟫
  | ⟪₂ (:: apply (:: :f :g)) ⟫ => do
    let f' ← step f
    let g' ← step g

    match f', g' with
    | ⟪₂ (:: exec :_c₁) ⟫, ⟪₂ (:: exec :_c₂) ⟫ =>
      ⟪₂ (:: apply (:: :f' :g')) ⟫
    | ⟪₂ (:: (:: exec :_c₁₁) :_c₁₂) ⟫, _r
    | _r, ⟪₂ (:: (:: exec :_c₁₁) :_c₁₂) ⟫ =>
      ⟪₂ (:: apply (:: :f' :g')) ⟫
    | _, _ => ⟪₂ :f' :g' ⟫
  | ⟪₂ (:: exec (:: :f :ctx)) ⟫ => exec_op ((step f).getD f) ((step ctx).getD ctx)
  | ⟪₂ I :_α :x ⟫ => x
  | ⟪₂ K :_α :_β :x :_y ⟫
  | ⟪₂ K' :_α :_β :x :_y ⟫ => x
  | ⟪₂ , :_a :_b ⟫ => .none
  | ⟪₂ :: :_a :_b ⟫ => .none
  | ⟪₂ :f :x ⟫ =>
    let f' := (step f).getD f
    let x' := (step x).getD x
    ⟪₂ :f' :x' ⟫
  | _ => .none

def try_step_n (n : ℕ) (e : Expr) : Option Expr := do
  if n = 0 then
    pure e
  else
    let e' ← step e
    pure <| (try_step_n (n - 1) e').getD e'

def try_step_n! (n : ℕ) (e : Expr) : Expr := (try_step_n n e).getD e
