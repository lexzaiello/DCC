import Cm.Ast
import Cm.Eval
import Cm.Infer

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

  /-
    It keeps getting stuck at the x argument.
    Why is this?
    x : ∀ (x : α) (y : β x), γ x y
    We've seen that γ works already.
  -/

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

def test_my_i : Except Error Expr := do
  let t_data ← infer ⟪₂ Data ⟫

  mk_i t_data

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

def church_t_f (t_in t_out : Expr) : Expr :=
  ⟪₂ , (:: (:: assert (quoted :t_in)) (:: (:: assert (quoted :t_out)) nil)) (, nil nil) ⟫

def church_t_x (t_in _t_out : Expr) : Expr :=
  ⟪₂ , (:: (:: assert (quoted :t_in)) nil) (, nil nil) ⟫

def church_succ_innermost_k (t_in t_out : Expr) : Expr :=
  let t_f := church_t_f t_in t_out
  let t_x := t_in

  ⟪₂ K' :t_f :t_x ⟫


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
  let my_s ← church_succ_innermost_s t_in t_out
  let t_my_s ← infer my_s

  let t_x := church_t_x t_in t_out
  let t_f := church_t_f t_in t_out

  --α = t_in
  --β = K t_out
  --γ = K (K t_out)

  -- innermost S : (t_x → t_f) → t_out → t_out
  let t_x_t_f := ⟪₂ , (:: (:: assert (quoted :t_x)) (:: (:: assert (quoted :t_f)) nil)) (, nil  nil) ⟫
  let t_my_s := ⟪₂ , (:: (:: assert (quoted :t_x_t_f)) (:: (:: assert (quoted :t_out)) (:: (:: assert (quoted :t_out)) nil))) (, nil nil) ⟫


  pure ⟪₂ K' :t_my_s (#church_t_f t_in t_out) ⟫

def return_s (t_in t_out : Expr) : Except Error Expr := do
  pure ⟪₂ (#← (church_succ_return_s_k t_in t_out)) (#← (church_succ_innermost_s t_in t_out)) ⟫

#eval return_s ⟪₂ Data ⟫ ⟪₂ Data ⟫ >>= infer

#eval return_s ⟪₂ Data ⟫ ⟪₂ Data ⟫

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

S (KS) K f
S (K f)

K f : t_x → t_f

α = t_f
β = K _ t_f (#church_t_f t_in t_out)
γ = K (K t_inner_s)
-/

def far_left_s (t_in t_out : Expr) : Except Error Expr := do
  let α := church_t_f t_in t_out

  -- K f : t_x → t_f
  let t_k_right : Expr := ⟪₂ ,
      (:: (:: assert (quoted :t_in)) (:: (:: assert (quoted (#church_t_f t_in t_out))) nil))
      (, nil nil) ⟫
  let t_t_k_right ← infer t_k_right

  -- γ = (t_in → t_out) → (t_in → t_out)
  let t_γ : Expr := ⟪₂ , (::
    (:: assert (quoted (#church_t_f t_in t_out)))
    (:: (:: assert (quoted (#t_in)))
      (:: (:: assert (quoted (#t_out))) nil))) (, nil nil) ⟫
  let t_t_γ ← infer t_γ

  let ret_γ := ⟪₂ K' :t_t_γ :t_k_right :t_γ ⟫
  let t_ret_γ ← infer ret_γ
  let γ := ⟪₂ K' :t_ret_γ (#church_t_f t_in t_out) :ret_γ ⟫

  let β := ⟪₂ K' :t_t_k_right :α :t_k_right ⟫

  pure ⟪₂ S :α :β :γ ⟫

def inner_combs (t_in t_out : Expr) : Except Error Expr := do
  pure ⟪₂ (#← far_left_s t_in t_out) (#← return_s t_in t_out) (#church_succ_innermost_k t_in t_out) ⟫

#eval flatten_context ⟪₂ ((:: ((:: assert) quoted ((, ((:: ((:: assert) quoted Data)) ((:: ((:: assert) quoted Data)) nil))) ((, nil) nil)))) ((:: ((:: assert) quoted ((, ((:: ((:: assert) quoted Data)) ((:: ((:: assert) quoted ((, ((:: ((:: assert) quoted Data)) ((:: ((:: assert) quoted Data)) nil))) ((, nil) nil)))) nil))) ((, nil) nil)))) ((:: ((:: assert) quoted ((, ((:: ((:: assert) quoted ((, ((:: ((:: assert) quoted Data)) ((:: ((:: assert) quoted Data)) nil))) ((, nil) nil)))) ((:: ((:: assert) quoted Data)) ((:: ((:: assert) quoted Data)) nil)))) ((, nil) nil)))) nil))) ⟫
#eval inner_combs ⟪₂ Data ⟫ ⟪₂ Data ⟫ >>= infer

def outermost_s (t_in t_out : Expr) : Except Error Expr := do
  

#eval far_left_s ⟪₂ Data ⟫ ⟪₂ Data ⟫

--def church_succ_outer_s (t_in t_out : Expr) : Except Error Expr := do
  

--def zero (t_in t_out : Expr) : Except Error Expr := do
  
