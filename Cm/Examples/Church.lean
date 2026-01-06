import Cm.Ast
import Cm.Eval
import Cm.Infer

/-
Idea:
- global context,

- something similar to exec,
but for contexts.

Two issues, but they all mainly stem from deeply nested contexts.
We never know when will pop out, what form it will be in, and how to compare.

I feel like the issue is with currying.

The other issue is that the types we give to the user are also deeply nested.
If the user inputs a context with state and reads, we should have some way to sequence that.

Maybe having nested contexts overall is kinda sus.
It seems sus.

Also quotation is mega sus.

One potential thought is that we can combine contexts, somehow.

Even if the church numeral example is wrong,
it's still insane to have these humongous types to haul around.
-/

/-
I derived from S with any t_x
-/
def mk_i (t_x : Expr) : Except Error Expr := do
  /-
    γ gets x and y, should return t_x
    γ (x :t_x) Data = t_x
    γ = K (K :t_t_x Data :t_x)
    γ :t_x Data = t_x
  -/
  let t_data ← infer ⟪₂ Data ⟫
  let t_t_x ← infer t_x
  let assert_t_x := ⟪₂ K' :t_t_x :t_data :t_x ⟫
  let t_assert_t_x ← infer assert_t_x

  let aa_t_x := ⟪₂ K' :t_assert_t_x :t_x :assert_t_x ⟫

  let t_t_data ← infer t_data

  pure ⟪₂ S :t_x (K' :t_t_data :t_x :t_data) :aa_t_x (K' :t_x :t_data) (K' :t_data :t_x Data) ⟫

def my_examplebruh : Except Error Expr := do
  let t_data ← infer ⟪₂ Data ⟫
  let my_i ← mk_i t_data
  pure ⟪₂ :my_i Data ⟫

#eval my_examplebruh >>= infer

def my_examplebruh2 : Except Error Expr := do
  let t_data ← infer ⟪₂ K ⟫
  let my_i ← mk_i t_data
  pure ⟪₂ :my_i ⟫

#eval my_examplebruh2
  >>= infer

#eval Expr.display_infer <$> (my_example >>= infer)

def mk_i_example (x : Expr) : Except Error Expr := do
  let t_x ← infer x
  (fun e => ⟪₂ :e :x ⟫) <$> mk_i t_x

/-
I works, but we're probably messing up in at least one place.
-/

def mk_flse (t_a t_b : Expr) : Except Error Expr := do
  let my_i ← ⟪₂ (#mk_i t_b) ⟫
  let t_my_i ← infer my_i

  pure ⟪₂ K' :t_my_i :t_a :my_i ⟫

def mk_flse_test (a b : Expr) : Except Error Expr := do
  let t_a ← infer a
  let t_b ← infer b

  let my_false ← mk_flse t_a t_b

  pure ⟪₂ :my_false :a :b ⟫

#eval infer ⟪₂ Data ⟫
#eval Expr.display_infer <$> (infer ⟪₂ Data ⟫)
#eval Expr.display_infer <$> (mk_flse_test ⟪₂ Data ⟫ ⟪₂ Data ⟫
  >>= infer)

#eval (mk_flse_test ⟪₂ K ⟫ ⟪₂ S ⟫
  >>= infer)
  >>= (fun t_out => do
    pure (t_out == (← infer ⟪₂ S ⟫)))

def church_t_f (t_in t_out : Expr) : Expr :=
  ⟪₂ , (:: (:: fst (:: read assert)) (:: (:: fst (:: next (:: read assert))) nil)) (, (:: :t_in (:: :t_out nil)) nil) ⟫

def church_t_x (t_in _t_out : Expr) : Expr :=
  ⟪₂ , (:: (:: fst (:: read assert)) nil) (, (:: :t_in nil) nil) ⟫

def church_t_n_f_app (t_in t_out : Expr) : Expr :=
  ⟪₂ , (:: (:: fst (:: read assert)) (:: (:: fst (:: next (:: read assert))) nil)) (, (:: :t_in (:: :t_out nil)) nil) ⟫

def s_outermost_β (t_in t_out : Expr) : Except Error Expr := do
  let t_f := church_t_f t_in t_out
  let t_f_app := church_t_n_f_app t_in t_out
  let t_t_f_app ← infer t_f_app
  pure ⟪₂ K' :t_t_f_app :t_f :t_f_app ⟫

def test_s_outermost_β : Except Error Expr := do
  let t_data ← infer ⟪₂ Data ⟫
  let β ← s_outermost_β t_data t_data

  let my_f := ⟪₂ I :t_data ⟫

  pure ⟪₂ :β :my_f ⟫

/-
γ receives f and (n f), and output t_in → t_out
n f : t_in → t_out?
-/
def s_outermost_γ (t_in t_out : Expr) : Except Error Expr := do
  let t_f := church_t_f t_in t_out
  let t_t_f ← infer t_f
  let ret_nf := ⟪₂ K' :t_t_f :t_f :t_f ⟫
  let t_ret_nf ← infer ret_nf
  pure ⟪₂ K' :t_ret_nf :t_f :ret_nf ⟫

def test_outer_γ : Except Error Expr := do
  let t_data ← infer ⟪₂ Data ⟫
  let my_f := ⟪₂ I :t_data ⟫

  let t_f := church_t_f t_data t_data

  let my_zero ← mk_flse t_f t_data

  let γ ← s_outermost_γ t_data t_data
  dbg_trace infer ⟪₂ (:my_zero :my_f) ⟫
  pure ⟪₂ :γ :my_f (:my_zero :my_f) ⟫

#eval test_outer_γ >>= infer

/-
S(S(KS)K) n f

n : (t_in → t_out) → t_in → t_out

n f : t_in → t_out

((S(KS)K) f) (n f)

((S(KS)K) f) = ((KS) f) (K f) = S (K f)

S (K f) (n f) : γ

S (K f) (n f) : t_in → t_out

S(S(KS)K) n f x
-/

/-
Church numerals:

zero f x = x

This is the same as false.

succ n f x = f (n f x)

succ = S(S(KS)K)

succ n f x =

S(S(KS)K)nfx
=
((S(KS)K) f) (n f) x

((S(KS)K) f) =
((KS) f) (K f)

=
S (K f) (n f) x

f (n f x)

Types for this gonna be GNARLY.

Outer S first:

n : t_f → t_x → t_x

n : (in → out) → in → out
assume we have t_f = α → β

α = (→ t_in t_out)
β = (K t_out)
γ gets f and n, in that order
γ =

S(S(KS)K)nfx
=
((S(KS)K) f) (n f) x

(S(KS)K) f =
  (((KS) f) (K f))

=
S (K f)

Innermost S, and K

S (K f) (n f) x

=

(K f x) (n f x)

inner most K has the type that's pretty obvious

K t_f t_x f x

t_f = (t_in -> t_out) t_in

so, β is the type of (n f)

that would be (in → out)

α = (in → out)
β = (K (in → out))
γ = (K (K (in → out)))

ezpz, I think.
-/

#eval infer ⟪₂ I Data ⟫

def church_succ_k_f (t_in t_out : Expr) : Expr :=
  let t_f := church_t_f t_in t_out
  let t_x := t_in

  ⟪₂ K' :t_f :t_x ⟫

def test_kf : Except Error Expr := do
  let t_data ← infer ⟪₂ Data ⟫
  let my_f := ⟪₂ I :t_data ⟫

  let kf := church_succ_k_f t_data t_data

  infer ⟪₂ :kf :my_f Data ⟫

/-
S (K f) (n f) x

S (K f) (n f) x
= f (n f x)

K f x = f

Innermost S.

z = x
x : t_in

β = t_out
γ = (t_in → t_out)

α = t_in
β = K t_out
γ = K (K t_out)

this is the S in KS
-/
def church_succ_innermost_s (t_in t_out : Expr) : Except Error Expr := do
  let t_t_out ← infer t_out
  let t_t_α ← infer t_in

  let α := t_in
  let β := ⟪₂ K' :t_t_α :t_t_out :α ⟫
  let k_t_out := ⟪₂ K' :t_t_out :t_in :t_out ⟫
  let t_k_t_out ← infer k_t_out
  let γ := ⟪₂ K' :t_k_t_out :t_in :k_t_out ⟫

  pure ⟪₂ S :α :β :γ ⟫

/-
((S(KS)K) f) (n f) x

Got innermost S and innermost K,
now need the K that returns the innermost S.

(((KS) f) (K f))
S (K f)
This is how it works.

This is very obvious.
α = t_s
β = t_f
-/

def church_succ_return_s_k (t_in t_out : Expr) : Except Error Expr := do
  let t_my_s ← infer (← church_succ_innermost_s t_in t_out)

  pure ⟪₂ K' :t_my_s (#church_t_f t_in t_out) ⟫

def return_s (t_in t_out : Expr) : Except Error Expr := do
  pure ⟪₂ (#← (church_succ_return_s_k t_in t_out)) (#← (church_succ_innermost_s t_in t_out)) ⟫

#eval (church_succ_innermost_s ⟪₂ Data ⟫ ⟪₂ Data ⟫)
  >>= infer

#eval return_s ⟪₂ Data ⟫ ⟪₂ Data ⟫ >>= infer

/-
Now need the S on the very far left

((S(KS)K) f)
K f : t_x → t_f
(KS) f (K f)
S (K f)

S (K f)

n f : t_in → t_out
x : t_in
S (K f) : (t_in → t_out) → (t_in → t_out)

S far left

S α = t_f
S β = t_x → t_f
S γ = (t_in → t_out) → (t_in → t_out)

S (K f) (n f) x

f (n f x)

((S(KS)K) f) (n f) x

S (K f) (n f) x

S (KS) K f
S (K f)

K f : t_x → t_f

α = t_f
β = K _ t_f (#church_t_f t_in t_out)
γ = K (K t_inner_s)

Far left is is hard to make ourselves.

(S(KS)K) f
= S (K f) --

((S(KS)K) f) (n f) x

S(KS)K) f = S (K f)

S (K f) : (type of n f) → (type of x) → t_out

n f : t_in → t_out
n_f = , (:: (:: fst (:: read assert)) (:: (:: fst (:: next (:: read assert))) nil)) (, (:: :t_in (:: :t_out nil)))
γ = (t_in → t_out) → t_in → t_out
γ = , (:: (:: fst (:: read assert)) (:: (:: fst (:: next (:: read assert))) (:: (:: fst (:: next (:: next (:: read asssert)))) nil))) (, (:: :n_f (:: :t_in (:: :t_out nil))) nil)

(S(KS)K) f

(KS f) (K f)
= S (K f) -- γ is this type

S (K f) (n f) x

S (K f) : (t_in → t_out) → t_in → t_out
-/

def t_k_f_app (t_in t_out : Expr) : Except Error Expr := do match ← infer (church_succ_k_f t_in t_out) with
  | ⟪₂ , :Γ :C ⟫ =>
    let Γ' ← ((Γ.list_pop).map Except.ok).getD (Except.error <| Error.not_type Γ)
    pure ⟪₂ , :Γ' :C ⟫
  | x => pure x

def far_left_s_γ (t_in t_out : Expr) : Except Error Expr := do
  let α := church_t_f t_in t_out

  let t_nf := ⟪₂ , (:: (:: fst (:: read assert)) (:: (:: fst (:: next (:: read assert))) nil)) (, (:: :t_in (:: :t_out nil)) nil) ⟫

  let t_γ := ⟪₂ , (::
    (:: fst (:: read assert))
    (:: (:: fst (:: next (:: read assert))) (:: (:: fst (:: next (:: next (:: read assert)))) nil))) (, (:: :t_nf (:: :t_in (:: :t_out nil))) nil) ⟫
  let t_t_γ ← infer t_γ

  let t_k_f ← t_k_f_app t_in t_out

  -- γ receives f and ((K f) : t_x → t_f)
  let ret_γ := ⟪₂ K' :t_t_γ :t_k_f :t_γ ⟫
  let t_ret_γ ← infer ret_γ

  pure ⟪₂ K' :t_ret_γ :α :ret_γ ⟫

def far_left_s_β (t_in t_out : Expr) : Except Error Expr := do
  let α := church_t_f t_in t_out
  let t_k_f ← t_k_f_app t_in t_out
  let t_t_k_f ← infer t_k_f

  pure ⟪₂ K' :t_t_k_f :α :t_k_f ⟫

def test_far_left_s_β : Except Error Expr := do
  let x := ⟪₂ Data ⟫
  let t_x ← infer x
  let my_f := ⟪₂ I :t_x ⟫

  let β ← far_left_s_β t_x t_x

  dbg_trace infer ⟪₂ (#church_succ_k_f t_x t_x) :my_f ⟫
  dbg_trace do_step ⟪₂ :β :my_f ⟫

  dbg_trace tys_are_eq (← infer ⟪₂ (#church_succ_k_f t_x t_x) :my_f ⟫) (← do_step ⟪₂ :β :my_f ⟫) ⟪₂ nil ⟫

  pure ⟪₂ :β :my_f ⟫

#eval test_far_left_s_β

def far_left_s (t_in t_out : Expr) : Except Error Expr := do
  let γ ← far_left_s_γ t_in t_out
  let α := church_t_f t_in t_out

  let β ← far_left_s_β t_in t_in

  pure ⟪₂ S :α :β :γ ⟫

#eval far_left_s ⟪₂ Data ⟫  ⟪₂ Data ⟫
  >>= infer

def test_γ_f_app : Except Error Expr := do
  let t_data ← infer ⟪₂ Data ⟫
  let my_f := ⟪₂ I :t_data ⟫

  let γ ← far_left_s_γ t_data t_data

  let my_k := ⟪₂ (#church_succ_k_f t_data t_data) :my_f ⟫

  infer ⟪₂ :γ :my_f :my_k ⟫

#eval test_γ_f_app

/-def inner_combs (t_in t_out : Expr) : Except Error Expr := do
  pure ⟪₂ (#← far_left_s t_in t_out) (#← return_s t_in t_out) (#church_succ_innermost_k t_in t_out) ⟫-/

--def outermost_s (t_in t_out : Expr) : Except Error Expr := do
  

#eval far_left_s ⟪₂ Data ⟫ ⟪₂ Data ⟫

--def church_succ_outer_s (t_in t_out : Expr) : Except Error Expr := do
  

--def zero (t_in t_out : Expr) : Except Error Expr := do
  

/-
Potentially based design decision for later:
- don't normalize β normal value contexts.
-/
