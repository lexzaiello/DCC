import Cm.Ast

def step : Expr → Option Expr
  | ⟪₂ exec (:: fst :rst) (, :a :b) ⟫ => step ⟪₂ exec :rst :a ⟫
  | ⟪₂ exec (:: snd :rst) (, :a :b) ⟫ => step ⟪₂ exec :rst :b ⟫
  | ⟪₂ exec (:: next :rst) (:: :x :xs) ⟫ => step ⟪₂ exec :rst :xs ⟫
  | ⟪₂ exec (:: (:: both (:: :f (:: :g nil))) :rst) (:: :x :xs) ⟫ => do
    let fx ← step ⟪₂ exec :f (:: :x :xs) ⟫
    let gx ← step ⟪₂ exec :g (:: :x :xs) ⟫

    pure ⟪₂ :rst (:: :fx (:: :gx nil)) ⟫
  | ⟪₂ exec (:: (:: push_on (:: :onto (:: :l nil))) :rst) (:: :x :xs) ⟫ =>
    ⟪₂ exec :rst (:: :x :l) ⟫
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
