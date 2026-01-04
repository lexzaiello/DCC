import Cm.Ast
import Cm.Eval

def steal_context (from_e for_e : Expr) : Expr :=
  match from_e, for_e with
  | ⟪₂ :_Γ (, :Δ :Ξ) ⟫, ⟪₂ :Γ₂ (, nil nil) ⟫ => ⟪₂ :Γ₂ (, :Δ :Ξ) ⟫
  | _, _ => for_e

def do_or_unquote (to_do : Expr) (in_e : Expr) : Option Expr :=
  try_step_n 10 ⟪₂ exec :in_e :to_do ⟫

-- Applies the Δ claims context to all handlers in the app context
-- returns all of the applied assertions, in order
def sub_context : Expr → Expr
  | ⟪₂ , :Γ (, :Δ :Ξ) ⟫ =>
    Expr.from_list <| (do (← Γ.as_list).mapM (fun f =>
    (do_or_unquote ⟪₂ , :Δ :Ξ ⟫ f).getD f)).getD []
  | e@⟪₂ (:: :_e :_rst) ⟫ => e
  | e => ⟪₂ (:: :e nil) ⟫

def norm_context : Expr → Expr := (try_step_n! 10 ∘ sub_context)

def read_data : Expr :=
  ⟪₂ , (:: (quote Data) (:: (quote Data) nil)) ⟫

def read_α : Expr :=
  ⟪₂ , (:: (>> fst read) (:: (quote Data) nil)) ⟫

def ass_data : Expr :=
  ⟪₂ (:: assert Data) ⟫

/-
S type:

S : ∀ (α : Type) (β : α → Type) (γ : ∀ (x : α), β x → Type)
  (x : ∀ (z : α) (y : β z), γ z y)
  (y : ∀ (z : α), β z)
  (z : α), γ z (y z)
-/

namespace s

def α : Expr := ⟪₂ :ass_data ⟫

-- β : α → Type
def β : Expr :=
  let α := ⟪₂ :: fst (:: read assert) ⟫
  ⟪₂ (:: both (:: :α (:: :ass_data (:: push_on nil)))) ⟫

#eval try_step_n 10 ⟪₂ exec :β (, (:: Data nil) nil) ⟫

/- γ : ∀ (x : α), β x → Type
-/
def γ : Expr :=
  let Δ := ⟪₂ fst ⟫

  -- α is the first argument in Δ. we don't do anything to it
  let α := ⟪₂ (:: read assert) ⟫
  let β := ⟪₂ (:: next (:: read assert)) ⟫

  -- x is a quoted operation that shouldn't run until the later context
  -- flow starts by getting our dependents, then building the new context via quotation
  -- x is the first argument in the later context
  -- it selects the Δ register, then reads
  let x := ⟪₂ (:: fst (:: read assert)) ⟫

  /-
    Need to quote the apply so it doesn't get run until later.
    Can pipe into it.
    Can use both to quote.
  -/
  let mk_βx := ⟪₂ (:: both (::
    (:: assert apply)
    (:: both (::
      (:: :β quote) (:: assert :x))))) ⟫
  /-let mk_βx := ⟪₂ (:: both (::
    (:: assert apply)
    (:: both (::
      (:: :β quote)
      (:: assert :x))))) ⟫-/

  -- α properly quoted
  let asserts := ⟪₂ (:: both (::
    (:: :α quote)
    (:: :mk_βx (:: push_on (:: :ass_data nil))))) ⟫

  let append_tuple_ctx : Expr := ⟪₂ (:: push_on (, nil nil)) ⟫

  ⟪₂ :: :Δ (:: :asserts :append_tuple_ctx) ⟫

/-
βx:

(:: ((:: apply) ((:: ((:: (I Data)) ((:: ((:: fst) ((:: read) assert))) nil))) nil)))

successfully captured β
and quoted the rest.
there's just an extra both.
-/

def test_γ_ctx : Expr := ⟪₂ , (:: Data (:: (I Data) nil)) nil ⟫
def γ_e_1 : Option Expr := try_step_n 10 ⟪₂ exec :γ :test_γ_ctx ⟫

#eval γ_e_1

#eval Expr.as_list <$> (γ_e_1 >>= (fun e => try_step_n 10 ⟪₂ exec fst :e ⟫))

/-
x : ∀ (z : α) (y : β z), γ z y
-/
def arg_x : Expr :=
  -- arguments in the first register
  let Δ := ⟪₂ fst ⟫

  let α := ⟪₂ (:: read assert) ⟫
  let β := ⟪₂ (:: next (:: read assert)) ⟫
  let γ := ⟪₂ (:: next (:: next (:: read assert))) ⟫

  let x := ⟪₂ (:: fst (:: read assert)) ⟫
  let mk_βx := ⟪₂ (:: both (::
    (:: assert apply)
    (:: both (::
      (:: :β quote) (:: assert :x))))) ⟫

  -- sequence after β

  let y := ⟪₂ (:: fst (:: next (:: read assert))) ⟫

  let mk_γz := ⟪₂ (:: both (::
    (:: assert apply)
    (:: both (::
      (:: :γ quote) (:: assert :x))))) ⟫
  let mk_γzy := ⟪₂ (:: both (::
    (:: assert apply)
    (:: both (::
      :mk_γz (:: assert :y))))) ⟫

  let asserts := ⟪₂ (:: both (::
    (:: :α quote)
    (:: both (::
      :mk_βx (:: :mk_γzy (:: push_on nil)))))) ⟫

  let append_tuple_ctx : Expr := ⟪₂ (:: push_on (, nil nil)) ⟫

  ⟪₂ :: :Δ (:: :asserts :append_tuple_ctx) ⟫

/-
For testing the x type, S's context:
- α = Data
- β = I Data
- γ = I
-/
def test_context_arg_x : Expr := ⟪₂ (, (:: Data (:: (I Data) (:: I nil))) nil) ⟫

/-
this should be:
γ = I
x : ∀ (z : Data) (y : I Data z), I z y

((:: (((K Data) (I Data)) Data)) ((:: ((both (((K Data) (I Data)) (I Data))) ((>> fst) read))) ((:: ((both ((both (((K Data) (I Data)) I)) ((>> fst) read))) ((>> fst) ((>> next) read)))) nil)))

See tests below
-/
#eval try_step_n 10 ⟪₂ ((both (((K Data) (I Data)) (I Data))) ((>> fst) read)) (, (:: I nil) nil) ⟫
#eval try_step_n 10 ⟪₂ :arg_x :test_context_arg_x ⟫
#eval try_step_n 10 ⟪₂ ((both ((both (((K Data) (I Data)) I)) ((>> fst) read))) ((>> fst) ((>> next) read))) (, (:: Data (:: Data nil)) nil) ⟫

/-
(y : ∀ (z : α), β z)
-/
def arg_y : Expr :=
  let Δ := ⟪₂ fst ⟫

  let α := ⟪₂ (:: read assert) ⟫
  let β := ⟪₂ (:: next (:: read assert)) ⟫

  let x := ⟪₂ (:: fst (:: read assert)) ⟫
  let mk_βx := ⟪₂ (:: both (::
    (:: assert apply)
    (:: both (::
      (:: :β quote) (:: assert :x))))) ⟫

  let asserts := ⟪₂ (:: both (::
    (:: :α quote) (:: :mk_βx (:: push_on nil)))) ⟫

  let append_tuple_ctx : Expr := ⟪₂ (:: push_on (, nil nil)) ⟫

  ⟪₂ :: :Δ (:: :asserts :append_tuple_ctx) ⟫

/-
y test, pretty similar. use the same test context.
should be ∀ (x : α), β x
first arg in asserts is the data quoted, nice
second is the both thing. let's test
((, ((:: (((K Data) (I Data)) Data)) ((:: ((both (((K Data) (I Data)) (I Data))) ((>> fst) read))) nil))) ((, nil) nil))
-/
#eval try_step_n 10 ⟪₂ :arg_y :test_context_arg_x ⟫

#eval try_step_n 10 ⟪₂ ((both (((K Data) (I Data)) (I Data))) ((>> fst) read)) (, (:: I nil) nil) ⟫

/-
z is pretty easy, since it's not even under a binder. Assume we're given (, Δ Ξ)
-/

def arg_z : Expr :=
  let Δ := ⟪₂ fst ⟫
  ⟪₂ :: :Δ (:: read assert) ⟫

/-
Final output:
γ z (y z)
-/
def t_out : Expr :=
  let Δ := ⟪₂ fst ⟫

  -- x is in register 4
  -- y is in register 5
  -- z is in register 6

  let γ := ⟪₂ :: next (:: next read) ⟫
  let y := ⟪₂ :: next (:: next (:: next (:: next read))) ⟫
  let z := ⟪₂ :: next (:: next (:: next (:: next (:: next read)))) ⟫

  ⟪₂ :: :Δ (:: apply (:: (:: apply (:: :γ :z)) (:: apply (:: :y :z)))) ⟫

def full_test_context : Expr :=
  let α := ⟪₂ Data ⟫
  let β := ⟪₂ I Data ⟫
  let γ := ⟪₂ I ⟫

  let x := ⟪₂ I ⟫
  let y := ⟪₂ I Data ⟫
  let z := ⟪₂ Data ⟫

  ⟪₂ (, (:: :α (:: :β (:: :γ (:: :x (:: :y (:: :z nil)))))) nil) ⟫

#eval try_step_n 10 ⟪₂ :t_out :full_test_context ⟫

def s_rule : Expr :=
  ⟪₂ , (:: :α (:: :β (:: :γ (:: :arg_x (:: :arg_y (:: :arg_z (:: :t_out nil))))))) (, nil nil) ⟫

end s

def ass_data_here : Expr :=
  ⟪₂ (:: assert (:: Data nil)) ⟫

def reduce_unquote : Expr → Option Expr := (try_step_n 10) ∘ Expr.unquote_pure

def Expr.display_infer : Expr → Option Expr
  | ⟪₂ , :Γ :X ⟫ => do
    let out ← (← Γ.as_list).getLast?
    (reduce_unquote <=< try_step_n 10) ⟪₂ exec :out :X ⟫
  | e => reduce_unquote e

def infer (e : Expr) (with_dbg_logs : Bool := false) : Option Expr :=
  match e with
  | ⟪₂ assert ⟫
  | ⟪₂ next ⟫
  | ⟪₂ fst ⟫
  | ⟪₂ snd ⟫
  | ⟪₂ both ⟫
  | ⟪₂ read ⟫
  | ⟪₂ apply ⟫
  | ⟪₂ quote ⟫
  | ⟪₂ push_on ⟫ => ⟪₂ , (:: :ass_data nil) (, nil nil) ⟫
  | ⟪₂ S ⟫ => s.s_rule
  | ⟪₂ I ⟫ =>
    let α := ⟪₂ (:: fst (:: read assert)) ⟫
    ⟪₂ , (:: :ass_data (:: :α (:: :α nil))) (, nil nil) ⟫
  | ⟪₂ K ⟫ =>
    let t_α := ⟪₂ :ass_data ⟫
    let t_β := ⟪₂ (:: both (:: (:: fst (:: read assert)) (:: :ass_data (:: push_on nil)))) ⟫
    let t_x := ⟪₂ (:: fst (:: read assert)) ⟫
    let t_y := ⟪₂ (:: apply (:: (:: fst (:: next (:: read assert))) (:: fst (:: next (::next (:: read assert)))))) ⟫

    ⟪₂ , (:: :t_α (:: :t_β (:: :t_x (:: :t_y (:: :t_x nil))))) (, nil nil) ⟫
  | ⟪₂ K' ⟫ =>
    ⟪₂ , (::
      :ass_data
      (::
        :ass_data
        (::
          (:: fst (:: read assert))
          (::
            (:: fst (:: next (:: read assert)))
            (::
              (:: fst (:: read assert))
              nil)))))
      (, nil nil) ⟫
  | ⟪₂ quoted :_e ⟫ => ⟪₂ ,
    (:: :ass_data nil)
    (, nil nil) ⟫
  | ⟪₂ :: ⟫
  | ⟪₂ , ⟫ => ⟪₂ ,
    (::
      :ass_data
      (::
        :ass_data
        (::
          :ass_data nil)))
      (, nil nil) ⟫
  | ⟪₂ nil ⟫ => ⟪₂ , (:: :ass_data nil) (, nil nil) ⟫
  | ⟪₂ Data ⟫ => ⟪₂ , (:: :ass_data nil) (, nil nil) ⟫
  | ⟪₂ exec ⟫ => ⟪₂ ,
    (:: :ass_data (:: :ass_data (:: :ass_data nil)))
    (, nil nil) ⟫
  | ⟪₂ :f :arg ⟫ => match infer f, infer arg with
    | .some t_f, .some raw_t_arg => do
      let t_arg := norm_context raw_t_arg

      match t_f with
      | ⟪₂ , :Γ (, :Δ :Ξ) ⟫ =>
        let Δ' := Expr.push_in ⟪₂ quoted :arg ⟫ Δ
        let Ξ' := Expr.push_in raw_t_arg Ξ

        let check_with ← Γ.list_head

        let expected' ← do_or_unquote ⟪₂ , :Δ' :Ξ' ⟫ check_with
        let stolen := try_step_n! 10 <| norm_context <| steal_context raw_t_arg expected'

        let unquoted_expected := reduce_unquote stolen
        let unquoted_actual   := reduce_unquote t_arg

        if with_dbg_logs then
          dbg_trace raw_t_arg
          dbg_trace expected'

          dbg_trace stolen
          dbg_trace t_arg
          dbg_trace unquoted_expected
          dbg_trace unquoted_actual

        if Expr.unquote_once expected' == raw_t_arg || unquoted_expected == unquoted_actual then
          let Γ' ← Γ.list_pop

          match Γ'.as_singleton with
          | .some t_out =>
            do_or_unquote ⟪₂ (, :Δ' :Ξ') ⟫ t_out
          | _ =>
            pure ⟪₂ , :Γ' (, :Δ' :Ξ') ⟫
        else
          .none
      | _ => .none
    | _, _ => .none
  | _ => .none

def infer_list (e : Expr) : List (List (Option Expr)) :=
  (e.any_data_as_list.getD []).map (·.any_data_as_list.getD [] |> List.map infer)

#eval infer ⟪₂ I Data Data ⟫
#eval infer ⟪₂ K' Data Data Data Data ⟫
#eval infer ⟪₂ K Data (I Data) Data Data ⟫

#eval Expr.display_infer <$> infer ⟪₂ S Data (I Data) (K' Data Data) (K' Data Data) (I Data) Data ⟫

#eval (infer <=< infer) ⟪₂ S ⟫

#eval infer ⟪₂ S ⟫

def example_return_S : Option Expr := do
  let t_s ← infer ⟪₂ S ⟫

  infer ⟪₂ I :t_s S ⟫

#eval example_return_S

def mk_tre (t_a t_b : Expr) : Expr :=
  ⟪₂ K' :t_a :t_b ⟫

