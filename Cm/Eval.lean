import Cm.Ast

/-
Upon user request, a list may be treated as a series of instructions
for processing some datum.

There is support for piping, quotation, and some list operations.

The format looks like:

exec (:: f (:: g nil)) data

-/
def exec_op (my_op : Expr) (ctx : Expr) : Option Expr := do
  match my_op, ctx with
  | ⟪₂ read ⟫, ⟪₂ (:: :x :_xs) ⟫ => x
  | ⟪₂ fst ⟫, ⟪₂ (, :a :_b) ⟫ => a
  | ⟪₂ snd ⟫, ⟪₂ (, :_a :b) ⟫ => b
  | ⟪₂ (:: both (:: :f :g)) ⟫, Γ =>
    let f' ← exec_op f Γ
    let g' ← exec_op g Γ

    ⟪₂ (:: :f' :g') ⟫
  -- pipelining operations
  | ⟪₂ :: :f :g ⟫, ctx =>
    let x ← exec_op f ctx

    pure ⟪₂ exec :g :x ⟫
  
  sorry

def step : Expr → Option Expr
  | ⟪₂ exec (:: apply (:: both (:: :f (:: :g nil)))) :ctx ⟫ => do
    let inner' ← step ⟪₂ exec (:: both (:: :f (:: :g nil))) :ctx ⟫

    dbg_trace "hi"
    dbg_trace inner'

    match inner' with
    | ⟪₂ ((:: :a) ((:: :b) nil)) ⟫ =>
      dbg_trace s!"hi again: {⟪₂ :a :b ⟫}"
      ⟪₂ :a :b ⟫
    | _ => .none
  | ⟪₂ exec (:: (:: quote (:: :c nil)) :rst) (:: :x :xs) ⟫ =>
    step ⟪₂ exec (:: :c (:: :rst nil)) :xs ⟫
  | ⟪₂ exec (:: read :rst) (:: :x :xs) ⟫ => step ⟪₂ exec :rst (:: :x nil) ⟫
  | ⟪₂ exec (:: fst :rst) (, :a :b) ⟫ => step ⟪₂ exec :rst :a ⟫
  | ⟪₂ exec (:: snd :rst) (, :a :b) ⟫ => step ⟪₂ exec :rst :b ⟫
  | ⟪₂ exec (:: next nil) (:: :x :xs) ⟫ => xs
  | ⟪₂ exec (:: next :rst) (:: :x :xs) ⟫ => step ⟪₂ exec :rst :xs ⟫
  | ⟪₂ exec (:: both (:: :f (:: :g nil))) :ctx ⟫ => do
    let fx ← step ⟪₂ exec :f :ctx ⟫
    let gx ← step ⟪₂ exec :g :ctx ⟫

    pure ⟪₂ (:: :fx (:: :gx nil)) ⟫
  | ⟪₂ exec (:: both (:: :f (:: :g :rst))) :ctx ⟫ => do
    let fx ← step ⟪₂ exec :f :ctx ⟫
    let gx ← step ⟪₂ exec :g :ctx ⟫

    pure ⟪₂ exec :rst (:: :fx (:: :gx nil)) ⟫
  | ⟪₂ exec (:: (:: push_on (, :a :b)) :rst) (:: :x :xs) ⟫ =>
    step ⟪₂ exec :rst (, (:: :x :xs) (, :a :b)) ⟫
  | ⟪₂ exec (:: (:: push_on (:: :l nil)) :rst) (:: :x :xs) ⟫ =>
    step ⟪₂ exec :rst (:: (:: :x :xs) :l) ⟫
  /-
    Drops context, giving a value.
  -/
  | ⟪₂ exec (:: (:: assert (:: :x nil)) :rst) :ctx ⟫ =>
    x
  | ⟪₂ exec (:: assert nil) (:: :x :_xs) ⟫ => x
  | ⟪₂ exec nil :x ⟫ => x
  | ⟪₂ push_on nil :a ⟫ => ⟪₂ :: :a nil ⟫
  | ⟪₂ push_on (:: :x :xs) :a ⟫ => ⟪₂ :: :a (:: :x :xs) ⟫
  | ⟪₂ push_on (, :a :b) :c ⟫ => ⟪₂ (, :c (, :a :b)) ⟫
  | ⟪₂ push_on :l :a ⟫ => ⟪₂ :: :a :l ⟫
  | ⟪₂ >> :f :g :Γ ⟫
  | ⟪₂ >>* :f :g :Γ ⟫ => step ⟪₂ :g (:f :Γ) ⟫
  | ⟪₂ I :_α :x ⟫ => x
  | ⟪₂ K :_α :_β :x :_y ⟫
  | ⟪₂ K' :_α :_β :x :_y ⟫ => x
  | ⟪₂ unquote (quote :x) ⟫ => x
  | ⟪₂ unquote :_x ⟫ => .none
  | ⟪₂ both :f :g :Γ ⟫
  | ⟪₂ both' :f :g :Γ ⟫ =>
    let left := ⟪₂ :f :Γ ⟫
    let right := ⟪₂ :g :Γ ⟫

    ⟪₂ (# (step left).getD left) (# (step right).getD right) ⟫
  | ⟪₂ bothM :f :g :Γ ⟫
  | ⟪₂ bothM' :f :g :Γ ⟫ =>
    let left := ⟪₂ :f :Γ ⟫
    let right := ⟪₂ :g :Γ ⟫

    ⟪₂ :: (# (step left).getD left) (# (step right).getD right) ⟫
  | e@⟪₂ next (:: :_x nil) ⟫ => e
  | ⟪₂ read nil ⟫ => .none
  | ⟪₂ next (:: :_x :xs) ⟫ => xs
  | ⟪₂ read (:: :x :_xs) ⟫ => x
  | ⟪₂ fst (, :a :_b) ⟫ => a
  | ⟪₂ snd (, :_a :b) ⟫ => b
  | ⟪₂ map_fst :f (, :a :b) ⟫ => do
    ⟪₂ (, (#← step ⟪₂ :f :a ⟫) :b) ⟫
  | ⟪₂ map_snd :f (, :a :b) ⟫ => do
    ⟪₂ (, :a (#← step ⟪₂ :f :b ⟫)) ⟫
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
