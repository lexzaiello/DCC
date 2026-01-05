import Cm.Ast
import Cm.Eval
import Cm.Error

def unwrap_with {α : Type} (ε : Error) (o : Option α) : Except Error α :=
  (o.map Except.ok).getD (.error ε)

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
  try_step_n 10 ⟪₂ exec :in_e :to_do ⟫

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
  ⟪₂ , (:: (quote Data) (:: (quote Data) nil)) ⟫

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

def ass_data_here : Expr :=
  ⟪₂ (:: assert (:: Data nil)) ⟫

def reduce_unquote : Expr → Option Expr := (try_step_n 10) ∘ Expr.unquote_pure

def Expr.display_infer : Expr → Option Expr
  | ⟪₂ , :Γ :X ⟫ => do
    let out ← (← Γ.as_list).getLast?
    let out ← try_step_n 10 ⟪₂ exec :out :X ⟫
    try_step_n 10 out.unquote_pure <|> (pure out)
  | e => reduce_unquote e

/-
Substitutes a context into all of the assertions in a Γ expression.
Produces a new type object, prepending all output assertions with assert,
and attaching nil Δ and Ξ contexts.

This assumes that the expression is in β-normal form.
That is, the (, Δ Ξ) registers are nillable.

To freeze the context,

map runs exec on all the items of a list.

Then, we prepend an assert before each element.

map works in reverse, which is whack.
works on a list of functions, instead of list of data

This map function is whack.

Should be map f xs

And repeat for all members of the list, not for all members of the map.

Usually we would do this with exec. But we're already doing exec_op.

the Γ register is our context.
We're mapping over the elements in it, which are functions.

And then we want to apply the actual context to each one with exec.

(:: map (:: (:: 

(:: map (::

Feel like we can do this with just both.

If we put a both at every level, we will re-make the list.

(:: both

If we put a both around each element, we're good to go.

(:: f (:: g nil))

This is way too complicated.

I feel like map should work.

the data we're mapping over are the functions.

then, when we have an assertion in context,
exec it with the context.

except we have no way to do this.

We could just change the map definition.

But then map literally becomes exec.
This is fine.

If the context couldn't be frozen, none is returned.

Ok, the map definition matches now.

Could use map on that again.

But map works the reverse way.

Oh just pipe the execs into each other.

What if we use a normal map? Then I think we need exec.
We need both.

We already kinda have dynamic exec. both does dynamic exec.

so we can do normal map?

map = both, so make map the other way.

so, map is dead, but we can use both.

both Γ C does what we want.

Then, we pipe into map to add our asserts.

(:: (:: both :Γ) (:: map quote))

But we want to put asserts in.
-/
def freeze_context (Γ : Expr) (c : Expr) : Option Expr :=
  try_step_n 10 ⟪₂ exec (:: (:: both :Γ) (:: map quote)) :c ⟫

#eval try_step_n 10 ⟪₂ exec (:: map quote) (:: Data nil) ⟫
#eval try_step_n 10 ⟪₂ exec (:: both ((:: ((:: assert) Data)) nil)) (, (:: Data nil) nil) ⟫
#eval freeze_context ⟪₂ ((:: ((:: assert) Data)) nil) ⟫ ⟪₂ , (:: Data nil) nil ⟫

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

def tys_are_eq : Expr → Expr → Bool
  

def infer (e : Expr) (with_dbg_logs : Bool := false) : Except Error Expr :=
  match e with
  | ⟪₂ map ⟫
  | ⟪₂ assert ⟫
  | ⟪₂ next ⟫
  | ⟪₂ fst ⟫
  | ⟪₂ snd ⟫
  | ⟪₂ both ⟫
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
    let t_β := ⟪₂ (:: both (:: (:: fst (:: read assert)) (:: :ass_data (:: push_on nil)))) ⟫
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
  | ⟪₂ quoted :_e ⟫ => pure ⟪₂ ,
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
  | ⟪₂ exec ⟫ => pure ⟪₂ ,
    (:: :ass_data (:: :ass_data (:: :ass_data nil)))
    (, nil nil) ⟫
  | ⟪₂ :f :arg ⟫ => do
    let t_f ← infer f with_dbg_logs
    let raw_t_arg ← infer arg with_dbg_logs
    let t_arg := (norm_all_contexts ∘ norm_context) raw_t_arg

    match t_f with
    | ⟪₂ quoted (, :Γ (, :Δ :Ξ)) ⟫
    | ⟪₂ , :Γ (, :Δ :Ξ) ⟫ =>
      let Δ' := Expr.push_in ⟪₂ quoted :arg ⟫ Δ
      let Ξ' := Expr.push_in raw_t_arg Ξ

      let check_with ← Γ.list_head |> unwrap_with (.short_context Γ)

      let expected' ← do_or_unquote ⟪₂ , :Δ' :Ξ' ⟫ check_with |> unwrap_with (.stuck ⟪₂ exec :check_with (, :Δ' :Ξ') ⟫)
      let stolen := try_step_n! 10 <| norm_context <| steal_context raw_t_arg expected'

      let unquoted_expected := (norm_all_contexts <$> reduce_unquote stolen).getD stolen
      let unquoted_actual   := (norm_all_contexts <$> reduce_unquote t_arg).getD t_arg

      let _ ← assert_eq (Expr.unquote_once expected') raw_t_arg e
        <|> assert_eq unquoted_expected unquoted_actual e

      let Γ' ← Γ.list_pop |> unwrap_with (.short_context Γ)

      match Γ'.as_singleton with
      | .some t_out =>
        do_or_unquote ⟪₂ (, :Δ' :Ξ') ⟫ t_out |> unwrap_with (.stuck ⟪₂ exec :t_out (, :Δ' :Ξ') ⟫)
      | _ =>
        pure ⟪₂ , :Γ' (, :Δ' :Ξ') ⟫
    | _ =>
      .error <| .not_type t_f

def infer_list (e : Expr) : List (List (Except Error Expr)) :=
  (e.any_data_as_list.getD []).map (·.any_data_as_list.getD [] |> List.map infer)

#eval infer ⟪₂ I Data Data ⟫
#eval infer ⟪₂ K' Data Data Data Data ⟫
#eval infer ⟪₂ K Data (I Data) Data Data ⟫

#eval Expr.display_infer <$> infer ⟪₂ S Data (I Data) (K' Data Data) (K' Data Data) (I Data) Data ⟫

#eval (infer <=< infer) ⟪₂ S ⟫

#eval infer ⟪₂ S ⟫

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

#eval nested_k_example >>= infer

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
-/

#eval infer ⟪₂ Data ⟫
