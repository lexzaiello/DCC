import Cm.Ast
import Cm.Error

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
  dbg_trace s!"op: {my_op}"
  dbg_trace s!"ctx: {ctx}"
  match my_op, ctx with
  | ⟪₂ (:: map :_f) ⟫, ⟪₂ nil ⟫ =>
    ⟪₂ nil ⟫
  | ⟪₂ (:: map :f) ⟫, ⟪₂ :: :x nil ⟫ =>
    let x' := ⟪₂ :: exec (:: :f :x) ⟫
    dbg_trace ⟪₂ (:: :x' nil) ⟫
    ⟪₂ (:: :x' nil) ⟫
  | ⟪₂ (:: map :f) ⟫, ⟪₂ :: :x :xs ⟫  =>
    let x' := ⟪₂ (:: exec (:: :f :x)) ⟫
    let xs' := ⟪₂ (:: exec (:: (:: map :f) :xs)) ⟫

    ⟪₂ (:: :x' :xs') ⟫
  | ⟪₂ (:: map :f) ⟫, e => ⟪₂ (:: exec :f :e) ⟫
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
  | ⟪₂ (:: both (:: :f :g)) ⟫, Γ =>
    let f' := ⟪₂ (:: exec (:: :f :Γ)) ⟫
    let g' := ⟪₂ (:: exec (:: :g :Γ)) ⟫

    ⟪₂ (:: :f' :g') ⟫
  -- pipelining operations
  | ⟪₂ :: :f :g ⟫, ctx =>
    let x := ⟪₂ (:: exec (:: :f :ctx)) ⟫

    ⟪₂ (:: exec (:: :g :x)) ⟫
  | _, _ => ⟪₂ nil ⟫

def step (e : Expr) : Option Expr :=
  dbg_trace e
  match e with
  | ⟪₂ (:: (:: exec :m) (:: exec :n)) ⟫ => do
    let m' ← step ⟪₂ :: exec :m ⟫
    let n' ← step ⟪₂ :: exec :n ⟫

    pure ⟪₂ (:: :m' :n') ⟫
  | ⟪₂ (:: exec (:: :f (:: exec :c))) ⟫ => do
    dbg_trace "b"
    let c' ← step ⟪₂ :: exec :c ⟫
    ⟪₂ :: exec :f :c' ⟫
  | ⟪₂ (:: (:: exec :m) :v) ⟫ => do
    let m' ← step ⟪₂ :: exec :m ⟫
    pure ⟪₂ (:: :m' :v) ⟫
  | ⟪₂ (:: :v (:: exec :m)) ⟫ => do
    let m' ← step ⟪₂ :: exec :m ⟫
    pure ⟪₂ (:: :v :m') ⟫
  | ⟪₂ (:: apply (:: :f :g)) ⟫ => do
    dbg_trace "app"
    let f' ← step f
    let g' ← step g

    match f', g' with
    | ⟪₂ (:: exec :_c₁) ⟫, ⟪₂ (:: exec :_c₂) ⟫ =>
      ⟪₂ (:: apply (:: :f' :g')) ⟫
    | ⟪₂ (:: (:: exec :_c₁₁) :_c₁₂) ⟫, _r
    | _r, ⟪₂ (:: (:: exec :_c₁₁) :_c₁₂) ⟫ =>
      ⟪₂ (:: apply (:: :f' :g')) ⟫
    | _, _ => ⟪₂ :f' :g' ⟫
  | ⟪₂ (:: exec (:: :f :ctx)) ⟫ =>
    dbg_trace "c"
    let e' := exec_op f ctx
    dbg_trace s!"hi: {e'}"
    e'
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

def unwrap_with {α : Type} (ε : Error) (o : Option α) : Except Error α :=
  (o.map Except.ok).getD (.error ε)

def do_step (e : Expr) : Except Error Expr :=
  unwrap_with (Error.stuck e) (try_step_n 10 e)

def try_step_n! (n : ℕ) (e : Expr) : Expr := (try_step_n n e).getD e

/-
Nested exec is bad.

Don't like it.
We shouldn't be nesting exec.

Why can't we sequence exec?

We can flattten the nesting.

Main operations we need to flatten:
- chain
- both

both we can chain by chaining the both operation like after?
or we can just stop both'ing once we hit an assert

No, this changes how both works. don't like it.

We just don't want to get confused.

We could give exec a special both interpretation.
-/

#eval do_step ⟪₂ (:: exec (:: (:: map assert) (:: Data nil))) ⟫

#eval do_step ⟪₂ (:: exec (:: ((:: ((:: both) ((:: ((:: fst) ((:: read) assert))) ((:: ((:: assert) quoted Data)) ((:: push_on) nil))))) ((:: ((:: map) quote)) ((:: push_on) ((, nil) nil))))
((, ((:: quoted Data) ((:: quoted (I Data)) nil))) ((:: ((, ((:: ((:: assert) quoted Data)) nil)) ((, nil) nil))) ((:: ((, ((:: ((:: fst) ((:: read) assert))) ((:: ((:: fst) ((:: read) assert))) nil))) ((, ((:: quoted Data) nil)) ((:: ((, ((:: ((:: assert) quoted Data)) nil)) ((, nil) nil))) nil)))) nil))))) ⟫
