import Cm.Ast
import Cm.Eval
import Cm.Infer

/-
I derived from S with any t_x
-/
def mk_i (t_x : Expr) : Option Expr := do
  /-
    γ gets x and y, should return t_x
    γ (x :t_x) Data = t_x
  -/
  let assert_t_x := ⟪₂ K' Data Data :t_x ⟫
  let t_assert_t_x ← infer assert_t_x

  let aa_t_x := ⟪₂ K' :t_assert_t_x :t_x :assert_t_x ⟫

  ⟪₂ S :t_x (K' Data :t_x Data) :aa_t_x (K' :t_x Data) (K' Data :t_x Data) ⟫

#eval mk_i ⟪₂ Data ⟫
  >>= infer

/-
((:: Data) ((:: ((, ((:: ((:: fst) ((:: next) ((:: read) assert)))) ((:: ((:: fst) ((:: read) assert))) nil))) ((, ((:: Data) ((:: Data) ((:: Data) nil)))) ((:: ((, ((:: ((:: assert) Data)) nil)) ((, nil) nil))) ((:: ((, ((:: ((:: assert) Data)) nil)) ((, nil) nil))) ((:: ((, ((:: ((:: assert) Data)) nil)) ((, nil) nil))) nil)))))) nil))
-/

/-
Aha. The fight isn't over.
Normalized contexts leak non-data values.
-/

/-
This type isn't type-checking:
Is it the K' Data Data Data? everything else looks like data.

This is from the Δ register.
We need to quote the entire thing somehow.

(some ((, ((:: ((:: fst) ((:: next) ((:: read) assert)))) ((:: ((:: fst) ((:: read) assert))) nil))) ((, ((:: ((, ((:: ((:: fst) ((:: next) ((:: read) assert)))) ((:: ((:: fst) ((:: read) assert))) nil))) ((, ((:: Data) ((:: Data) ((:: Data) nil)))) ((:: ((, ((:: ((:: assert) Data)) nil)) ((, nil) nil))) ((:: ((, ((:: ((:: assert) Data)) nil)) ((, nil) nil))) ((:: ((, ((:: ((:: assert) Data)) nil)) ((, nil) nil))) nil)))))) ((:: Data) ((:: (((K' Data) Data) Data)) nil)))) ((:: Data) ((:: ((, ((:: ((:: assert) Data)) nil)) ((, nil) nil))) ((:: ((, ((:: ((:: fst) ((:: next) ((:: read) assert)))) ((:: ((:: fst) ((:: read) assert))) nil))) ((, ((:: Data) ((:: Data) ((:: Data) nil)))) ((:: ((, ((:: ((:: assert) Data)) nil)) ((, nil) nil))) ((:: ((, ((:: ((:: assert) Data)) nil)) ((, nil) nil))) ((:: ((, ((:: ((:: assert) Data)) nil)) ((, nil) nil))) nil)))))) nil))))))
-/

/-
aa_t_x type-checks with Data Data inputs, but S doesn't like it.
maybe it's because we're leaving the context intact?

-/
/-#eval mk_i ⟪₂ Data ⟫
  >>= (fun e => infer ⟪₂ :e Data Data ⟫)

#eval mk_i ⟪₂ Data ⟫-/

/-
γ binds (x : α) and (y : β x)


(((K' ((, ((:: ((:: fst) ((:: next) ((:: read) assert)))) ((:: ((:: fst) ((:: read) assert))) nil))) ((, ((:: Data) ((:: Data) ((:: Data) nil)))) ((:: ((, ((:: ((:: assert) Data)) nil)) ((, nil) nil))) ((:: ((, ((:: ((:: assert) Data)) nil)) ((, nil) nil))) ((:: ((, ((:: ((:: assert) Data)) nil)) ((, nil) nil))) nil)))))) Data) (((K' Data) Data) Data))

this is what we're type-checking.
type should be data -> that gigantic thing.
-/

/-#eval mk_i ⟪₂ Data ⟫ >>=
  (fun e => infer ⟪₂ :e Data ⟫)
  >>= Expr.display_infer-/

/-def nested_example : Option Expr := do
  let inner_k := ⟪₂ K' Data Data ⟫
  let t_k ← infer inner_k

  ⟪₂ K' :t_k Data :inner_k ⟫

#eval nested_example >>= (fun e => infer ⟪₂ :e Data Data Data ⟫)

#eval Expr.display_infer <$> infer ⟪₂ (#mk_i ⟪₂ Data ⟫) Data ⟫

def mk_tre (t_a t_b : Expr) : Expr :=
  ⟪₂ K' :t_a :t_b ⟫

def mk_flse (t_a t_b : Expr) : Option Expr := do
  let my_i := ⟪₂ (#mk_i t_b) ⟫
  dbg_trace my_i
  let t_my_i ← infer my_i

  ⟪₂ K' :t_my_i :t_a :my_i ⟫

def mk_test : Option Expr := do
  let a := ⟪₂ K ⟫
  let b := ⟪₂ S ⟫

  let t_a ← infer a
  let t_b ← infer b

  let my_flse ← mk_flse t_a t_b

  ⟪₂ :my_flse :a :b ⟫

#eval mk_test

def mk_church (t_f t_x : Expr) : Option Expr :=
  -/
