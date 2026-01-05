import Cm.Ast
import Cm.Eval
import Cm.Error

/-
Takes an assert value and builds it as the sole type
of a context.

e.g.,
(, (:: (:: assert x) nil) (, nil nil))
-/
def mk_singleton_ctx : Expr :=
  ⟪₂ (:: quote (:: (:: push_on nil) (:: push_on (, nil nil)))) ⟫

def ass_data : Expr :=
  ⟪₂ (:: assert (quoted Data)) ⟫

/-
Turns a list of constant values into
asserts in a context.
-/
def mk_const_ctx : Expr :=
  ⟪₂ (:: (:: map quote) (:: push_on (, nil nil))) ⟫

def assert_eq (expected actual in_app : Expr) : Except Error Unit :=
  -- Throw a nicer error with a location if we the data are lists
  match Expr.as_list expected, Expr.as_list actual with
  /-| .some l₁, .some l₂ =>
    let append (acc : Option Error) (err : Error) : Option Error :=
      acc.map (Error.combine err) <|> (pure err)

    let e : Option Error := (l₁.zipWithAll Prod.mk l₂).zipIdx.foldl (fun (acc : Option Error) ((e₁, e₂), idx)  =>
      if e₁ == e₂ then
        acc
      else
        append acc <| Error.mismatch_arg (e₁.getD ⟪₂ nil ⟫) (e₂.getD ⟪₂ nil ⟫) in_app idx) .none

    let root_err : Error :=
      Error.mismatch_arg expected actual in_app .none

    (e.map (Except.error ∘ (Error.combine root_err))).getD (pure ())-/
  | _, _ =>
    if expected == actual then
      pure ()
    else
      .error <| .mismatch_arg expected actual in_app .none

def steal_context (from_e for_e : Expr) : Expr :=
  match from_e, for_e with
  | ⟪₂ :_Γ (, :Δ :Ξ) ⟫, ⟪₂ :Γ₂ (, nil nil) ⟫ => ⟪₂ :Γ₂ (, :Δ :Ξ) ⟫
  | _, _ => for_e

def do_or_unquote (to_do : Expr) (in_e : Expr) : Option Expr :=
  try_step_n 10 ⟪₂ (:: exec (:: :in_e :to_do)) ⟫

-- Applies the Δ claims context to all handlers in the app context
-- returns all of the applied assertions, in order
-- this will also
def sub_context : Expr → Expr
  | ⟪₂ , :Γ (, :Δ :Ξ) ⟫ =>
    Expr.from_list <| (do (← Γ.as_list).mapM (fun f =>
    (do_or_unquote ⟪₂ , :Δ :Ξ ⟫ (Expr.unquote_once f)).getD f)).getD []
  | e@⟪₂ (:: :_e :_rst) ⟫ => e
  | e => ⟪₂ (:: :e nil) ⟫

def norm_context : Expr → Expr := (try_step_n! 10 ∘ sub_context)

def norm_all_contexts : Expr → Expr
  | ⟪₂ :: (quoted (, :Γ :C)) :xs ⟫ =>
    let x' := norm_context ⟪₂ , :Γ :C ⟫

    match xs with
    | ⟪₂ nil ⟫ => x'
    | _ =>  ⟪₂ :: (quoted :x') (#norm_all_contexts xs) ⟫
  | ⟪₂ :: (, :Γ :C) :xs ⟫ =>
    match norm_context ⟪₂ (, :Γ :C) ⟫ with
    | ⟪₂ :: :t nil ⟫ =>
      ⟪₂ :: :t (#norm_all_contexts xs) ⟫
    | t =>
      ⟪₂ :: :t (#norm_all_contexts xs) ⟫
  | ⟪₂ :: (:: :t nil) :xs ⟫ => ⟪₂ :: :t (#norm_all_contexts xs) ⟫
  | ⟪₂ :: :x :xs ⟫ => ⟪₂ :: :x (#norm_all_contexts xs) ⟫
  | x => x

/-
  Converts a rendered context, a list of types,
  into a normal context, where all the assertions don't depend on actual arguments.
-/
def assert_all_with_context (e : Expr) : Expr :=
  let rec add_asserts : Expr → Expr
  | ⟪₂ nil ⟫ => ⟪₂ nil ⟫
  | ⟪₂ :: :x :xs ⟫ => ⟪₂ :: (:: assert :x) (#add_asserts xs) ⟫
  | x => x

  match e with
  | ⟪₂ :: :_x :_xs ⟫ => ⟪₂ , (#add_asserts e) (, nil nil) ⟫
  | x => x

def read_data : Expr :=
  ⟪₂ , (:: (quote (quoted Data)) (:: (quote (quoted Data)) nil)) ⟫

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

#eval try_step_n 10 ⟪₂ (:: exec (:: :β (, (:: Data nil) nil))) ⟫

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

#eval Expr.as_list <$> (γ_e_1 >>= (fun e => try_step_n 10 ⟪₂ (:: exec (:: fst :e)) ⟫))

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

def reduce_unquote : Expr → Option Expr := (try_step_n 10) ∘ Expr.unquote_pure

def Expr.display_infer : Expr → Option Expr
  | ⟪₂ , :Γ :X ⟫ => do
    let out ← (← Γ.as_list).getLast?
    let out ← try_step_n 10 ⟪₂ (:: exec (:: :out :X)) ⟫
    try_step_n 10 out.unquote_pure <|> (pure out)
  | e => reduce_unquote e

--#eval do_step ⟪₂ (:: exec (:: ( ((:: fst) ((:: read) assert))) ((, ((:: quoted ((, ((:: ((:: assert) quoted Data)) ((:: ((:: ((:: both) ((:: ((:: fst) ((:: read) assert))) ((:: ((:: assert) quoted Data)) ((:: push_on) nil))))) ((:: ((:: map) quote)) ((:: push_on) ((, nil) nil))))) ((:: ((:: fst) ((:: read) assert))) ((:: ((:: apply) ((:: ((:: fst) ((:: next) ((:: read) assert)))) ((:: fst) ((:: next) ((:: next) ((:: read) assert))))))) ((:: ((:: fst) ((:: read) assert))) nil)))))) ((, nil) nil))) ((:: quoted K) nil))) ((:: ((, ((:: ((:: assert) quoted Data)) nil)) ((, nil) nil))) ((:: ((, ((:: ((:: assert) quoted Data)) ((:: ((:: ((:: both) ((:: ((:: fst) ((:: read) assert))) ((:: ((:: assert) quoted Data)) ((:: push_on) nil))))) ((:: ((:: map) quote)) ((:: push_on) ((, nil) nil))))) ((:: ((:: fst) ((:: read) assert))) ((:: ((:: apply) ((:: ((:: fst) ((:: next) ((:: read) assert)))) ((:: fst) ((:: next) ((:: next) ((:: read) assert))))))) ((:: ((:: fst) ((:: read) assert))) nil)))))) ((, nil) nil))) nil))))) ⟫

/-
If a context is explicitly produced, keep it.
Otherwise, assume this is a free-standing well-typed value,
and wrap it in an empty context.

Also, if a context only contains quoted values,
then we can just lift it.
-/
def run_context (Γ_elem : Expr) (c : Expr) : Except Error Expr := do
  match ← do_step ⟪₂ (:: exec (:: :Γ_elem :c)) ⟫ with
  | ⟪₂ , :Γ :C ⟫ => pure ⟪₂ , :Γ :C ⟫
  | t => do_step ⟪₂ (:: exec (:: :mk_singleton_ctx :t)) ⟫

def flatten_normal_assert (e : Expr) : Expr :=
  dbg_trace s!"to flatten: {e}"
  match e with
  | ⟪₂ , :Γ (, :Δ :Ξ) ⟫ =>
    (do
    if (← Δ.as_list).length ≥ (← Γ.as_list).length then
      let Γ' := (← Γ.as_list).map (fun Γ => (do_step ⟪₂ (:: exec (:: :Γ (, :Δ :Ξ))) ⟫).toOption.getD Γ)
        |> Expr.from_list
      .some ⟪₂ , :Γ' (, nil nil) ⟫
    else
      .none).getD ⟪₂ , :Γ (, :Δ :Ξ) ⟫
  | ⟪₂ quoted :e ⟫ => ⟪₂ quoted (#flatten_normal_assert e) ⟫
  | e => e

def unfold_quoted_list : Expr → Option Expr
  | ⟪₂ (:: (quoted :x) :xs) ⟫ => do
    ⟪₂ (:: (:: assert (quoted :x)) (#← unfold_quoted_list xs)) ⟫
  | ⟪₂ nil ⟫ => ⟪₂ nil ⟫
  | _ => .none

def flatten_context (Γ : Expr) : Expr :=
  match Γ with
  | ⟪₂ :: (:: assert (quoted (, :tys (, nil nil)))) nil ⟫ =>
    (do Option.some ⟪₂ (#← unfold_quoted_list tys) ⟫)
      |> (Option.getD · Γ)
  | e => e

/-
Substitutes the given (, Δ Ξ) pair into all assertions of the Γ context.
Prepends an assertions to all of the output values.

Does not detect whether nil values were produced.

Attaches an empty Δ and Ξ context.
-/
def freeze_context (Γ : Expr) (c : Expr) : Except Error Expr :=
  -- ((:: ((:: assert) quoted ((, ((:: quoted Data) ((:: quoted Data) nil))) ((, nil) nil)))) nil)
  dbg_trace s!"to freeze: {Γ}"
  match Γ with
  | ⟪₂ (:: :x :xs) ⟫ => do
    let x' ← do_step ⟪₂ (:: exec (:: :x :c)) ⟫
    .ok ⟪₂ :: (:: assert (# flatten_normal_assert x')) (#← freeze_context xs c) ⟫
  | ⟪₂ nil ⟫ => .ok ⟪₂ nil ⟫
  | e => .error <| .not_type e

def guard_is_ty (Γ : Expr) : Except Error Unit :=
  match Γ with
  | ⟪₂ , :_Γ (, :_Δ :_Ξ) ⟫ => pure ()
  | t => .error <| .not_type t

def n_args (Γ : Expr) : ℕ := (do
  let all_asserts ← Γ.as_list
  return all_asserts.length - 1).getD 0

/-
To check equality of types:
- types will always be in the form (, (:: f (:: g nil)) (, Δ Ξ))

for some values, Δ may be already filled in.

Also, Δ may not have enough values in it to compare. If Δ does not have enough values,
that is, one of the assertions will produce nil, simply plug in a list with unique values
into both types. TODO: This seems suspicious.

Also note, this may need to be done recursively.
For example, if a type mentions another context, you might want to normalize it, too
before comparing.

Note that types are uniquely identified by the triple (, Γ (, Δ Ξ))

So, we can do recursive descent and compare each one by normalization.
-/
def tys_are_eq (expected actual at_app : Expr) : Except Error Unit :=
  match expected, actual with
  | ⟪₂ , :Γ₁ (, :Δ₁ :Ξ₁) ⟫, ⟪₂ , :Γ₂ (, :Δ₂ :Ξ₂) ⟫ => do
    /-
      To compare the types, see how many input assertions the contexts are making.
      Then, extend the smallest of the two Δ registers with unique quoted data
      until enough have been supplied.

      Use the same context for both.
      Use the larger of the two contexts if possible.

      Note that the Δ context will contain existing values.
      So we should extend by as many args are left.

      Also note that we aren't using these test contexts to type-check.
      Just to compare def eq.

      Also note that the type shouldn't be looking inside the element, so
      its value doesn't matter, as long as it is somewhat unique.
    -/
    let dummy_args := (List.range (max (n_args Γ₁) (n_args Γ₂))).map (fun arg_n =>
      (List.replicate arg_n ⟪₂ Data ⟫).foldl (fun acc x => ⟪₂ , :acc :x ⟫) ⟪₂ Data ⟫
        |> (fun test_e => ⟪₂ quoted :test_e ⟫))
        |> Expr.from_list
    let Δ_test ← unwrap_with (Error.short_context Δ₁) (Expr.list_max Δ₁ Δ₂ >>= (Expr.list_concat · dummy_args))

    /-
      Now, reduce by plugging in our "fake" context, and comparing the remaining values.
    -/
    let expected' ← flatten_context <$> freeze_context Γ₁ ⟪₂ , :Δ_test :Ξ₁ ⟫
    let actual' ← flatten_context <$> freeze_context Γ₂ ⟪₂ , :Δ_test :Ξ₂ ⟫

    dbg_trace expected'
    dbg_trace actual'

    assert_eq expected' actual' at_app
  | e₁, e₂ => Except.error <| .combine (.not_type e₁) (.not_type e₂)

def infer (e : Expr) (with_dbg_logs : Bool := false) : Except Error Expr :=
  match e with
  | ⟪₂ map ⟫
  | ⟪₂ assert ⟫
  | ⟪₂ next ⟫
  | ⟪₂ fst ⟫
  | ⟪₂ snd ⟫
  | ⟪₂ both ⟫
  | ⟪₂ exec ⟫
  | ⟪₂ read ⟫
  | ⟪₂ apply ⟫
  | ⟪₂ quote ⟫
  | ⟪₂ push_on ⟫ => pure ⟪₂ , (:: :ass_data nil) (, nil nil) ⟫
  | ⟪₂ S ⟫ => pure s.s_rule
  | ⟪₂ I ⟫ =>
    let α := ⟪₂ (:: fst (:: read assert)) ⟫
    pure ⟪₂ , (:: :ass_data (:: :α (:: :α nil))) (, nil nil) ⟫
  | ⟪₂ K ⟫ =>
    let t_α := ⟪₂ :ass_data ⟫
    let t_β := ⟪₂ (:: (:: both (:: (:: fst (:: read assert)) (:: :ass_data (:: push_on nil)))) :mk_const_ctx) ⟫
    let t_x := ⟪₂ (:: fst (:: read assert)) ⟫
    let t_y := ⟪₂ (:: apply (:: (:: fst (:: next (:: read assert))) (:: fst (:: next (::next (:: read assert)))))) ⟫

    pure ⟪₂ , (:: :t_α (:: :t_β (:: :t_x (:: :t_y (:: :t_x nil))))) (, nil nil) ⟫
  | ⟪₂ K' ⟫ =>
    pure ⟪₂ , (::
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
  | ⟪₁ quoted :_e ⟫ => pure ⟪₂ ,
    (:: :ass_data nil)
    (, nil nil) ⟫
  | ⟪₂ :: ⟫
  | ⟪₂ , ⟫ => pure ⟪₂ ,
    (::
      :ass_data
      (::
        :ass_data
        (::
          :ass_data nil)))
      (, nil nil) ⟫
  | ⟪₂ nil ⟫ => pure ⟪₂ , (:: :ass_data nil) (, nil nil) ⟫
  | ⟪₂ Data ⟫ => pure ⟪₂ , (:: :ass_data nil) (, nil nil) ⟫
  | ⟪₂ :f :arg ⟫ => do
    dbg_trace s!"app: {⟪₂ :f :arg ⟫}"
    let t_f ← infer f with_dbg_logs
    let raw_t_arg ← infer arg with_dbg_logs

    match t_f with
    | ⟪₂ , :Γ (, :Δ :Ξ) ⟫ =>
      let Δ' := Expr.push_in ⟪₂ quoted :arg ⟫ Δ
      let Ξ' := Expr.push_in raw_t_arg Ξ

      let check_with ← Γ.list_head |> unwrap_with (.short_context Γ)

      let expected'' ← run_context check_with ⟪₂ (, :Δ' :Ξ') ⟫

      dbg_trace s!"check with: {check_with}"
      dbg_trace ⟪₂ , :Δ' :Ξ' ⟫
      dbg_trace "after sub: {expected''}"
      dbg_trace s!"app {f} {arg}: {raw_t_arg}"

      let _ ← tys_are_eq expected'' raw_t_arg e

      let Γ' ← Γ.list_pop |> unwrap_with (.short_context Γ)

      match Γ'.as_singleton with
      | .some t_out =>
        let t_out' ← run_context t_out ⟪₂ (, :Δ' :Ξ') ⟫
        guard_is_ty t_out'
        pure t_out'
      | _ =>
        pure ⟪₂ , :Γ' (, :Δ' :Ξ') ⟫
    | _ =>
      .error <| .not_type t_f

/-
We got that nested K example working.
That's nice.

But now we need to deal with flattening contexts.
Feels like this is still really ugly.

The problem is when we supply contexts inside arguments.
Then, they get quoted like normal data,
when they should almost always be noramlized.

At the very least, ty_eq should be able to recognize this.

An easy strategy we could do is:
- 
-/

#eval infer ⟪₂ I Data Data ⟫
#eval infer ⟪₂ K Data (I Data) Data Data ⟫

def infer_list (e : Expr) : List (List (Except Error Expr)) :=
  (e.any_data_as_list.getD []).map (·.any_data_as_list.getD [] |> List.map infer)

#eval infer ⟪₂ (I Data) ⟫

#eval infer ⟪₂ I Data Data ⟫
#eval infer ⟪₂ K' Data Data Data Data ⟫
#eval infer ⟪₂ K Data (I Data) Data Data ⟫

#eval Expr.display_infer <$> infer ⟪₂ S Data (I Data) (K' Data Data) (K' Data Data) (I Data) Data ⟫

#eval (infer <=< infer) ⟪₂ S ⟫

#eval infer ⟪₂ S ⟫

def example_return_K : Except Error Expr := do
  let t_x ← infer ⟪₂ K ⟫

  infer ⟪₂ I :t_x K ⟫

/-#eval do_step ⟪₂ (:: exec (:: ((:: fst) ((:: read) assert))
((, ((:: quoted ((, ((:: ((:: assert) quoted Data)) ((:: ((:: ((:: both) ((:: ((:: fst) ((:: read) assert))) ((:: ((:: assert) quoted Data)) ((:: push_on) nil))))) ((:: ((:: map) quote)) ((:: push_on) ((, nil) nil))))) ((:: ((:: fst) ((:: read) assert))) ((:: ((:: apply) ((:: ((:: fst) ((:: next) ((:: read) assert)))) ((:: fst) ((:: next) ((:: next) ((:: read) assert))))))) ((:: ((:: fst) ((:: read) assert))) nil)))))) ((, nil) nil))) ((:: quoted K) nil))) ((:: ((, ((:: ((:: assert) quoted Data)) nil)) ((, nil) nil))) ((:: ((, ((:: ((:: assert) quoted Data)) ((:: ((:: ((:: both) ((:: ((:: fst) ((:: read) assert))) ((:: ((:: assert) quoted Data)) ((:: push_on) nil))))) ((:: ((:: map) quote)) ((:: push_on) ((, nil) nil))))) ((:: ((:: fst) ((:: read) assert))) ((:: ((:: apply) ((:: ((:: fst) ((:: next) ((:: read) assert)))) ((:: fst) ((:: next) ((:: next) ((:: read) assert))))))) ((:: ((:: fst) ((:: read) assert))) nil)))))) ((, nil) nil))) nil))))) ⟫-/
#eval example_return_K

def example_return_S : Except Error Expr := do
  let t_s ← infer ⟪₂ S ⟫

  infer ⟪₂ I :t_s S ⟫

#eval example_return_S

def mk_tre (t_a t_b : Expr) : Expr :=
  ⟪₂ K' :t_a :t_b ⟫

/-
Question: if we can normalize contexts,
why are we carrying them around all the time?

theoretically, if we make an empty context, we can just make a list with a bunch of asserts,
no dependency.

Todo, tomorrow:
normalizing contexts more consistently.
Also need to make quotation a little more careful.

Need to figure out how to make quotation more consistent.

The issue is when we pass around partially applied functions.

We end up with this deeply nested context thing.

For example:

K t_k Data (K Data Data Data)


-/

def t_k : Except Error Expr :=
  infer ⟪₂ K ⟫

def nested_k_example : Except Error Expr := do
  let inner_k := ⟪₂ K' Data Data Data ⟫
  let t_inner_k ← infer inner_k

  pure ⟪₂ K' :t_inner_k Data :inner_k ⟫

-- (, ((:: ((:: fst) ((:: next) ((:: read) assert)))) ((:: ((:: fst) ((:: read) assert))) nil))) ((, ((:: quoted Data) ((:: quoted Data) ((:: quoted Data) nil)))) ((:: ((, ((:: ((:: assert) quoted Data)) nil)) ((, nil) nil))) ((:: ((, ((:: ((:: assert) quoted Data)) nil)) ((, nil) nil))) ((:: ((, ((:: ((:: assert) quoted Data)) nil)) ((, nil) nil))) nil))))

#eval infer ⟪₂ (((K' Data) Data) Data) ⟫
#eval nested_k_example >>= infer

/-
((, ((:: ((:: fst) ((:: next) ((:: read) assert)))) ((:: ((:: fst) ((:: read) assert))) nil))) ((, ((:: quoted Data) ((:: quoted Data) ((:: quoted Data) nil)))) ((:: ((, ((:: ((:: assert) quoted Data)) nil)) ((, nil) nil))) ((:: ((, ((:: ((:: assert) quoted Data)) nil)) ((, nil) nil))) ((:: ((, ((:: ((:: assert) quoted Data)) nil)) ((, nil) nil))) nil)))))
-/



/-def inspect_its_type : Option Expr := do
  let nested ← nested_k_example
  let t_nested ← infer nested

  /-
    K _ Data (K Data Data Data)
    Next argument it expects should be Data.
    Then, the next argument will be Data again.
    But, what is in the second register before popping?

    See this is really suspicious. Not sure why it only has two elements in its context.
    It's actually fine. the output type refers to the first quoted thing in the register.
    That's the "chaining" we're trying to do.
  -/

  All of this has to do with context normalization.
  A nice way around this is we can normalize the context early.
  This also has to do with quotation seemingly.

  Ideally what we do is normalize the context as soon as possible.
  The only reason we can't do that is because of this "context stealing" thing,
  where we match an argument based on its context,
  which is itself sus.

  Context stealing should not really matter.
  It's nice to have, but it can confuse things.

  --let reg_2 ← -/

#eval nested_k_example >>= infer

/-
This is K _ Data (K Data Data Data)

inner K: Data → Data
outter K: Data → (Data → Data)

Our type looks correct.
Assertions are correct.
Except, we plugged in a Data argument.

What was the type prior to that?

Type prior to that is:

We need to keep the Δ context,
so that we can check partial apps,
but we need to be more careful about how we sequence contexts9
and pass them around.

-/

/-
K _ Data (K Data Data Data) Data = K Data Data Data

K Data Data Data : Data → Data

The context looks fine. I guess there's some machinery somewhere going haywire.
-/

/-
  This is failing silently,
  not sure where.
  Last logs indicate the argument checked successfully.

  Getting stuck at the Data argument somehow.
-/

#eval nested_k_example >>=
  (fun e => infer ⟪₂ :e Data Data ⟫ true)


/-
We keep getting messed up by context normalization.
We need to figure out a more exact way to debug this.

context normalization is really annoying.

Questions:
- when we have an argument that has a Π, that is, a context that not been initialized yet,
how do we handle that?

It's really unclear when we're quoting, when we're making new contexts, when we're normalizing, etc.

We really should consolidate these things and make more concrete.

Why can't we normalize as soon as possible?
Because then we don't know what to initialize an expected context with.

We ought to attempt to remove as much extraneous shuffling as possible.

Normalization:

- we shouldn't be normalizing nil contexts.
- I wonder how much breaks if we do this.

At the very least, we should centralize it all.

- First, substitute the current context in. this is to check the current argument.
- then, we normalize both to compare

Context stealing feels super sus.

if we're checking the argument, we probably have an empty context.
we should always use theirs.

Quotation feels like probably the most sus thing right now.

Order seems vaguely wrong for stolen.
Why are we running norm_context one one but not both?

Ok, looks mostly fine.
I'm just confused on the extra nil.

There is one layer of extra nesting in expected.

We're doing too much normalization.

We only need to normalize:
- to get the current argument "checker"
- in case the types we're comparing are not exactly the same.

Also, with quotation:
- quotation is somewhat fine. Apps should work.
We're just unquoting and re-quoting kind of haphazardly.

Just seems like we're doing a lot of work. We should normalize if possible, and insert assert.

Our type list things are kind of like a list generator.
New combinator just dropped.

Oh wait I think both can actually handle this.

Maybe?

An alternative idea is to change our type assertions to natively use both,
but I don't like that.

It's more of a sequential thing.

map combinator.

Note:
we still haven't really dealt with quotation.

Note: contexts should only be frozen when
exactly one assertion remains.
-/

#eval infer ⟪₂ I Data Data ⟫

#eval infer ⟪₂ Data ⟫

/-
Notes on quoting:

Where do most of the issues with quoting happen?

App, mainly.
They also came because we had a bunch of big contexts left around.
Note, though, since we're subbing in the Δ register,
these will be quoted as well.

The main issue is we end up with a bunch of deeply quoted stuff in our final context.

Exec should handle this somewhat, though.

We already do kinda freeze the context, though, so this is confusing.

The sus part is that we don't put it in a context format.
This is where things get confusing.

Another thought:

I feel like we are insufficiently quoting things.
The purpose of quoted is to prevent non-data arguments from getting in the registers.

The quotation is fine, actually.
We should just be consistent about it.

Expected args are not themselves contexts,
just instructions, so we can always execute them successfully.

Another confusing thing:
- our tys are eq should be able to compare raw values and nil contexts.
Note that some of our types don't produce a context / type object from the assert function

If we're going to normalize anyway in apps, I feel like we should be using contexts all the time?

check_with will produce a context that we compare against the argument.
The argument will itself be a context.

So, we should be also producing a context.

The challenge is the S type. I don't want to add contexts in one layer, and then mess up S. We'll try it though.

Note that freeze_context is pretty much perfect for this.

I think there are definitely places where we aren't adding an extra layer.

This is another inconsistency, I think.
We need to actually put it in an empty context.

For this one, especially, we should either render the α,
or supply an explicit context. Kinda surprised this worked, ngl.

New policy from now on:

All asserts introduce a context.
Also, even simple types should have a context. It's just empty.

Assert should always introduce a context,
but there might be places where we assume it doesn't do that.

Let's not change assert yet.

HOWEVER:
The function itself should dictate fully what its context is for the assertions.
This will prevent shaddowing additionally.

TODO:
- change assert to introduce a nil context
- See where S's type breaks
- Use our new freeze function

Ok, so we won't use assert to introduce new contexts.
That feels dumb.

It's just unclear when we're making new contexts and when we're not.

I don't know what is intrinsically wrong with assert
being kind of a fixed point.

Asserts don't make a new context.
I guess it's fine as it is.

So, before we run freeze_context,
we should wrap anything that's hanging.

This is mildly suspicious though,
that we can just mix and match the comma part. We'll see

We should also use quotation consistently.

Ok this still lets us use Data as the argument,
which is nice, but confusing,
since we used ass_data.
-/

def my_example : Except Error Expr := do
  infer ⟪₂ I Data Data ⟫

#eval infer ⟪₂ :: assert nil ⟫
#eval infer ⟪₂ ((:: ((:: assert) quoted Data)) nil) ⟫
#eval infer ⟪₂ ((, ((:: ((:: assert) quoted Data)) nil)) ((, nil) nil)) ⟫
#eval infer ⟪₂ Data ⟫
#eval my_example

#eval infer ⟪₂ K ⟫

#eval infer ⟪₂ :: Data nil ⟫

/-
S type is broken, for now.
Now that pretty much all argument position elements
introduce a context, be it a nil one or one with arguments,
we can compare pretty easily.

Now, freeze context isn't necessary for the check_with.
We get the context immediately.

TODO: change assert.
I don't think this breaks much.

It feels like the most natural way to do it,

Problem:
The type of Data in ass_data is not the same as in infer.
This isn't too hard to change, but it will be annoying.

This is why it would be easier to change assert to make an empty context.

We still need to store things with frozen contexts.
Our equality needs to be able to detect asserts without beta reduction.

We're adding another context on every time when we shouldn't be.

It's the freeze context, probably.

It seems like we're adding another layer of context somewhere.

This is stupid.

I feel like this assert rule is really dumb.

Really dumb.

I feel like we should be able to detect an assert that is a final operation in forming a type,
and form the context from that instead of changing the rule for assert.

It's just like, do we want contexts or not?

It feels like we should be able to omit the context.
But if we omit the context, then we should attach something to it. idk.
Don't even remember what we've changed at this point.

The solution to the current problem is to make sure that we introduce an explicit context whenever we want one.
-/

#eval infer ⟪₂ K Data (I Data) Data Data ⟫

