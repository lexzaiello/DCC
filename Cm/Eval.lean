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
  match my_op, ctx with
  | ⟪₂ (:: map :_f) ⟫, ⟪₂ nil ⟫ =>
    ⟪₂ nil ⟫
  | ⟪₂ (:: map :f) ⟫, ⟪₂ :: :x nil ⟫ =>
    let x' := ⟪₂ :: exec (:: :f :x) ⟫
    ⟪₂ (:: exec (:: both (:: :x' nil))) ⟫
  | ⟪₂ (:: map :f) ⟫, ⟪₂ :: :x :xs ⟫  =>
    let x' := ⟪₂ (:: exec (:: :f :x)) ⟫
    let xs' := ⟪₂ (:: exec (:: (:: map :f) :xs)) ⟫

    ⟪₂ (:: exec (:: both (:: :x' :xs'))) ⟫
  | ⟪₂ (:: map :f) ⟫, e =>
    ⟪₂ (:: exec (:: :f :e)) ⟫
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

    ⟪₂ (:: exec (:: apply (:: :f' :g'))) ⟫
  | ⟪₂ (:: both (:: :f :g)) ⟫, Γ =>
    let f' := ⟪₂ (:: exec (:: :f :Γ)) ⟫
    let g' := ⟪₂ (:: exec (:: :g :Γ)) ⟫

    ⟪₂ (:: exec (:: both (:: :f' :g'))) ⟫
  -- pipelining operations
  | ⟪₂ :: :f :g ⟫, ctx =>
    let x := ⟪₂ (:: exec (:: :f :ctx)) ⟫

    ⟪₂ (:: exec (:: :g :x)) ⟫
  | _, _ => ⟪₂ nil ⟫

def step (e : Expr) : Option Expr :=
  match e with
  | ⟪₂ (:: exec (:: both (:: (:: exec :m) (:: exec :n)))) ⟫ => do
    let m' ← step ⟪₂ :: exec :m ⟫
    let n' ← step ⟪₂ :: exec :n ⟫

    pure ⟪₂ (:: exec (:: both (:: :m' :n'))) ⟫
  | ⟪₂ (:: exec (:: both (:: (:: exec :c) :g))) ⟫ => do
    let m' ← step ⟪₂ :: exec :c ⟫
    pure ⟪₂ (:: exec (:: both (:: :m' :g))) ⟫
  | ⟪₂ (:: exec (:: both (:: :f (:: exec :c)))) ⟫ => do
    let n' ← step ⟪₂ :: exec :c ⟫
    pure ⟪₂ (:: exec (:: both (:: :f :n'))) ⟫
  | ⟪₂ (:: exec (:: both (:: :f :g))) ⟫ =>
    ⟪₂ (:: :f :g) ⟫
  | ⟪₂ (:: exec (:: :f (:: exec :c))) ⟫ => do
    let c' ← step ⟪₂ :: exec :c ⟫
    ⟪₂ :: exec (:: :f :c') ⟫
  | ⟪₂ (:: exec (:: apply (:: (:: exec :f) (:: exec :g)))) ⟫ => do
    let f' ← step ⟪₂ :: exec :f ⟫
    let g' ← step ⟪₂ :: exec :g ⟫

    pure ⟪₂ :: exec (:: apply (:: :f' :g')) ⟫
  | ⟪₂ (:: exec (:: apply (:: (:: exec :f) :g))) ⟫ => do
    let f' ← step ⟪₂ :: exec :f ⟫

    pure ⟪₂ :: exec (:: apply (:: :f' :g)) ⟫
  | ⟪₂ (:: exec (:: apply (:: :f (:: exec :g)))) ⟫ => do
    let g' ← step ⟪₂ :: exec :g ⟫

    pure ⟪₂ :: exec (:: apply (:: :f :g')) ⟫
  | ⟪₂ (:: exec (:: apply (:: :f :g))) ⟫ => do
    let f' ← step ⟪₂ :f ⟫
    let g' ← step ⟪₂ :g ⟫

    ⟪₂ :f' :g' ⟫
  | ⟪₂ (:: exec (:: :f :ctx)) ⟫ =>
    let e' := exec_op f ctx
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
  unwrap_with (Error.stuck e) (try_step_n 20 e)

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

namespace test

def mk_singleton_ctx : Expr :=
  ⟪₂ (:: quote (:: (:: push_on nil) (:: push_on (, nil nil)))) ⟫

def ass_data : Expr :=
  ⟪₂ (:: assert (quoted Data)) ⟫

/-
Turns a list of constant values into
asserts in a context.

NOTES:
- chained operations are different from arguments. arguments should be in a different form from chaining
For example, assert cannot be chained due to this.

This is maybe fine but likely a problem for other ops.

Ops should always take the same number of arguments.
-/
def mk_const_ctx : Expr :=
  ⟪₂ (:: (:: map quote) (:: push_on (, nil nil))) ⟫

#eval do_step ⟪₂ (:: exec (:: (:: map :mk_singleton_ctx) Data)) ⟫
#eval do_step ⟪₂ (:: exec (:: :mk_const_ctx (:: Data (:: Data nil)))) ⟫

end test

