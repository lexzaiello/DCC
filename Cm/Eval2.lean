import Cm.Ast
import Cm.Error

def unwrap_with {α : Type} (ε : Error) (o : Option α) : Except Error α :=
  (o.map Except.ok).getD (.error ε)

def Expr.is_comb : Expr → Bool
  | ⟪₂ K ⟫
  | ⟪₂ S ⟫
  | ⟪₂ I ⟫
  | ⟪₂ K' ⟫ => true
  | ⟪₂ :f :_x ⟫ => f.is_comb
  | _ => false

def assert_not_fn : Expr → Expr
  | ⟪₂ read ⟫ => ⟪₂ read ⟫
  | ⟪₂ :: :a :b ⟫ => ⟪₂ :: :a :b ⟫
  | ⟪₂ nil ⟫ => ⟪₂ nil ⟫
  | e => ⟪₂ :: assert :e ⟫

/-
If an application includes instructions,
it must be lifted into another application
-/
def maybe_apply (es : List Expr) : Option Expr :=
  match es with
  | .cons f xs =>
    if f.is_comb then
      ⟪₂ quoted (#(xs.map Expr.unquote_pure).foldl Expr.app (f.unquote_pure)) ⟫
    else
      ⟪₂ :: (:: exec (#Expr.from_list (es.map assert_not_fn))) apply ⟫
  | _ => .none

def do_apply (es : List Expr) : Option Expr :=
  match es with
  | .cons f xs =>
    ⟪₂ quoted (#(xs.map Expr.unquote_pure).foldl Expr.app (f.unquote_pure)) ⟫
  | _ => .none

/-def wrap_assert : Expr → Expr
  | ⟪₂ -/

/-
Why should exec_op have to worry about the details of next?
Why can't we just make the list? Why do we have to assert?
We need the next stuff because otherwise.... what?
Actual values shouldn't have any issue.
Why don't we just return the value if it fails.

Why don't we just fail instead?

Why don't we pop the next and
make a new exec?

exec in exec_op and exec in step
are the only places where we should be dropping
next.

I feel like exec_op shouldn't be making new exec's.
We just have no way of distinguishing what we're actually trying to execute.

This is my question:
why are we running exec in exec_op and not step?

This is the problem. If we drop next in exec_op,
then everything gets confused.

Why don't we just drop beforehand? What?

We should be able to detect this in exec.
-/

def last_next (op ctx : Expr) : Except Error Expr :=
  match op, ctx with
  | ⟪₂ :: next :f ⟫, ⟪₂ :: :_x nil ⟫ => pure f
  | ⟪₂ :: next :f ⟫, ⟪₂ :: :x :xs ⟫ => last_next f xs
  | _, _ => Except.error <| .stuck op

def exec_op (my_op : Expr) (ctx : Expr) : Except Error Expr :=
  match my_op, ctx with
  | ⟪₂ nil ⟫, _c => pure ⟪₂ nil ⟫
  | ⟪₂ :: exec nil ⟫, _ => pure ⟪₂ nil ⟫
  | ⟪₂ :: exec (:: :x :xs) ⟫, c => do
    let xs' ← exec_op ⟪₂ :: exec :xs ⟫ c
    match xs' with
    | ⟪₂ :: exec :e ⟫ =>
      (last_next x c >>= (fun x' => pure ⟪₂ :: exec (:: :x' :e) ⟫))
      <|> (do pure ⟪₂ :: exec (:: (:: assert (#← (exec_op x c))) :e) ⟫)
    | ⟪₂ nil ⟫ =>
      (last_next x c >>= (fun x' => pure ⟪₂ :: exec (:: :x' nil) ⟫))
      <|> (do pure ⟪₂ :: (#← (exec_op x c)) nil ⟫)
    | e =>
      (last_next x c >>= (fun x' => pure ⟪₂ :: exec (:: :x' (:: assert :e)) ⟫))
      <|> (do pure ⟪₂ :: (#← (exec_op x c)) :e ⟫)
  | ⟪₂ read ⟫, ⟪₂ :: :x :_xs ⟫ => pure x
  | ⟪₂ assert ⟫, c => pure c
  | ⟪₂ :: :f quote ⟫, c => do
    let c' ← exec_op f c
    pure ⟪₂ :: assert :c' ⟫
  | ⟪₂ :: assert :x ⟫, _ => pure x
  | ⟪₂ quote ⟫, c => pure ⟪₂ :: assert :c ⟫
  | ⟪₂ :: next :f ⟫, ⟪₂ nil ⟫
  | ⟪₂ :: next :f ⟫, ⟪₂ :: :_x nil ⟫ => Except.error <| .stuck my_op
  | ⟪₂ :: next :f ⟫, ⟪₂ :: :_x :xs ⟫ => exec_op f xs
  | ⟪₂ :: read :f ⟫, ⟪₂ :: :x :_xs ⟫ => exec_op f x
  | ⟪₂ :: :f (:: push_on :l) ⟫, c => do
    let c' ← exec_op f c
    pure ⟪₂ :: :c' :l ⟫
  | ⟪₂ (:: push_on :l) ⟫, c => pure ⟪₂ :: :c :l ⟫
  | ⟪₂ :: both (:: :f :g) ⟫, c => do
    let f' ← exec_op f c
    let g' ← exec_op g c

    pure ⟪₂ :: :f' :g' ⟫
  | ⟪₂ :: (:: exec (:: :a :b)) apply ⟫, c => do
    let e' ← exec_op ⟪₂ :: exec (:: :a :b) ⟫ c

    match e' with
    | ⟪₂ :: exec :e ⟫ =>
      pure ⟪₂ :: (:: exec :e) apply ⟫
    | e' =>
      unwrap_with (.stuck ⟪₂ :: exec (:: (:: :my_op nil) :ctx)⟫) (e'.as_list >>= do_apply)
  | ⟪₂ :: (:: both :e) apply ⟫, c => do
    let e' ← exec_op ⟪₂ :: both :e ⟫ c
    (match e' with
    | ⟪₂ :: :a :b ⟫ =>
      maybe_apply [a, b]
    | _ => .none) |> unwrap_with (.stuck ⟪₂ :: exec (:: (:: :my_op nil) :ctx) ⟫)
  | ⟪₂ :: (:: exec :f) (:: (:: push_on apply) (:: both (:: assert exec) assert)) ⟫, c => do
    match ← exec_op ⟪₂ :: exec :f ⟫ c with
    | ⟪₂ :: exec :f ⟫ =>
      pure ⟪₂ :: (:: exec :f) (:: (:: push_on apply) (:: both (:: assert exec) assert)) ⟫
    | e =>
      pure ⟪₂ :: (:: exec :e) apply ⟫
  | _, _ => .error <| .stuck ⟪₂ :: exec (:: (:: :my_op nil) :ctx) ⟫

/-def exec_op_no_next_elim (my_op : Expr) (ctx : Expr) : Except Error Expr :=
  match my_op, ctx with
  | ⟪₂ nil ⟫, _c => pure ⟪₂ nil ⟫
  | ⟪₂ :: exec nil ⟫, _ => pure ⟪₂ nil ⟫
  | ⟪₂ :: exec (:: :x :xs) ⟫, c => do
    let x' ← exec_op x c
    let xs' ← exec_op ⟪₂ :: exec :xs ⟫ c

    pure ⟪₂ :: :x' :xs' ⟫
  | ⟪₂ read ⟫, ⟪₂ :: :x :_xs ⟫ => pure x
  | ⟪₂ next ⟫, ⟪₂ :: :_x :xs ⟫ => pure xs
  | ⟪₂ :: :f quote ⟫, c => do
    let c' ← exec_op f c
    pure ⟪₂ :: assert :c' ⟫
  | ⟪₂ :: assert :x ⟫, _ => pure x
  | ⟪₂ quote ⟫, c => pure ⟪₂ :: assert :c ⟫
  | ⟪₂ :: next :f ⟫, ⟪₂ :: :_x :xs ⟫ => exec_op f xs
  | ⟪₂ :: read :f ⟫, ⟪₂ :: :x :_xs ⟫ => exec_op f x
  | ⟪₂ :: :f (:: push_on :l) ⟫, c => do
    let c' ← exec_op f c
    pure ⟪₂ :: :c' :l ⟫
  | ⟪₂ (:: push_on :l) ⟫, c => pure ⟪₂ :: :c :l ⟫
  | ⟪₂ :: both (:: :f :g) ⟫, c => do
    let f' ← exec_op f c
    let g' ← exec_op g c

    pure ⟪₂ :: :f' :g' ⟫
  | ⟪₂ :: (:: exec (:: :a :b)) apply ⟫, c => do
    let e' ← exec_op ⟪₂ :: exec (:: :a :b) ⟫ c
      >>= ((unwrap_with (.stuck ⟪₂ :: exec (:: (:: :my_op nil) :ctx)⟫) ∘ Expr.as_list) >=> (pure ∘ (List.map Expr.unquote_pure)))

    match e' with
    | .cons x xs =>
      pure <| ⟪₂ quoted (#xs.foldl Expr.app x) ⟫
    | _ => .error <| .stuck ⟪₂ :: exec (:: (:: :my_op nil) :ctx) ⟫
  | ⟪₂ :: (:: both :e) apply ⟫, c => do
    match ← exec_op ⟪₂ :: both :e ⟫ c with
    | ⟪₂ :: :f :x ⟫ => do
      pure ⟪₂ quoted ((#f.unquote_pure) (#x.unquote_pure)) ⟫
    | _ => .error <| .stuck ⟪₂ :: exec (:: (:: :my_op nil) :ctx) ⟫
  | _, _ => .error <| .stuck ⟪₂ :: exec (:: (:: :my_op nil) :ctx) ⟫-/

#eval exec_op ⟪₂ :: exec (:: (:: next read) (:: (:: next read) nil)) ⟫ ⟪₂ :: Data nil ⟫
  >>= (fun op => exec_op op ⟪₂ :: Data nil ⟫)

#eval exec_op ⟪₂ :: (:: exec (:: read (:: (:: next read) nil))) apply ⟫ ⟪₂ :: (quoted I) nil ⟫
  >>= (fun op => exec_op op ⟪₂ :: Data nil ⟫)

def step (e : Expr) : Except Error Expr :=
  match e with
  | ⟪₂ :: exec (:: :ops :Γ) ⟫ =>
    match ops with
    | ⟪₂ (:: :x nil) ⟫ =>
      exec_op x Γ
    | l => l.mapM_list (Except.error <| .stuck e) (fun e => (exec_op e Γ) <|> (pure e))
  | ⟪₂ I :_α :x ⟫ => pure x
  | ⟪₂ K :_α :_β :x :_y ⟫
  | ⟪₂ K' :_α :_β :x :_y ⟫ => pure x
  | ⟪₂ S :_α :_β :_γ :x :y :z ⟫ => pure ⟪₂ (:x :z) (:y :z) ⟫
  | ⟪₂ :: :_a :_b ⟫ => Except.error <| .stuck e
  | ⟪₂ :f :x ⟫ => do
    pure ⟪₂ (#← step f) :x ⟫
  | _ => .error <| .stuck e

/-
def step_no_step_elim (e : Expr) : Except Error Expr :=
  match e with
  | ⟪₂ :: exec (:: :ops :Γ) ⟫ =>
    match ops with
    | ⟪₂ (:: :x nil) ⟫ =>
      exec_op x Γ
    | l => l.mapM_list (Except.error <| .stuck e) (fun e => (exec_op e Γ) <|> (pure e))
  | ⟪₂ I :_α :x ⟫ => pure x
  | ⟪₂ K :_α :_β :x :_y ⟫
  | ⟪₂ K' :_α :_β :x :_y ⟫ => pure x
  | ⟪₂ S :_α :_β :_γ :x :y :z ⟫ => pure ⟪₂ (:x :z) (:y :z) ⟫
  | ⟪₂ :: :_a :_b ⟫ => Except.error <| .stuck e
  | ⟪₂ :f :x ⟫ => do
    pure ⟪₂ (#← step f) :x ⟫
  | _ => .error <| .stuck e
-/

def try_step_n (n : ℕ) (e : Expr) : Except Error Expr := do
  if n = 0 then
    pure e
  else
    let e' ← step e
    (try_step_n (n - 1) e') <|> (pure e')

def do_step : Expr → Except Error Expr := try_step_n 30

def try_step_n! (n : ℕ) (e : Expr) : Expr := (try_step_n n e).toOption.getD e

-- Nondependent K
def k'_type : Expr :=
  let t_α := ⟪₂ Data ⟫
  -- β : α → Type
  let α := ⟪₂ read ⟫
  let t_β := ⟪₂ Data ⟫
  let β := ⟪₂ :: next read ⟫

  let t_x := α
  -- y : β x
  let t_y := β

  let t_out := α

  ⟪₂ :: :t_α (:: :t_β (:: :t_x (:: :t_y (:: :t_out nil)))) ⟫

def k_type : Expr :=
  let t_α := ⟪₂ Data ⟫
  -- β : α → Type
  let α := ⟪₂ read ⟫
  let t_β := ⟪₂ :: :α (:: push_on (:: Data nil)) ⟫
  let β := ⟪₂ :: next read ⟫
  let x := ⟪₂ :: next (:: next read) ⟫

  let t_x := α
  -- y : β x
  let t_y := ⟪₂ :: (:: exec (:: :β (:: :x nil))) apply ⟫

  let t_out := α

  ⟪₂ :: :t_α (:: :t_β (:: :t_x (:: :t_y (:: :t_out nil)))) ⟫

def i_type : Expr :=
  let t_α := ⟪₂ Data ⟫
  let α := ⟪₂ read ⟫

  ⟪₂ :: :t_α (:: :α (:: :α nil)) ⟫

#eval do_step ⟪₂ :: exec (:: :i_type (:: Data (:: Data nil))) ⟫

/-
Example k type:

K Data (I Data) Data Data

Also remember:
- our (I Data) term will be quoted.
-/

def test_ctx_k_type : Expr :=
  ⟪₂ :: Data (:: (quoted (I Data)) (:: Data (:: Data nil))) ⟫

--#eval exec_op ⟪₂ ((:: ((:: exec) ((:: ((:: next) read)) ((:: next) ((:: next) read))))) apply) ⟫ test_ctx_k_type
#eval do_step ⟪₂ :: exec (:: :k_type :test_ctx_k_type) ⟫

def test_ctx_k_partial : Expr :=
  ⟪₂ :: Data nil ⟫

/-
Applying α arg then β, then x, then y
-/
def infer_ctx_k_partial : Except Error Expr := do
  let t₁ ← do_step ⟪₂ :: exec (:: :k_type :test_ctx_k_partial) ⟫
  let t₂ ← do_step ⟪₂ :: exec (:: :t₁ (:: (quoted (I Data)) nil)) ⟫
  do_step ⟪₂ :: exec (:: :t₂ (:: Data (:: Data nil))) ⟫

#eval infer_ctx_k_partial

#eval ⟪₂ :: exec (:: :k_type :test_ctx_k_partial) ⟫

#eval (do pure <| (← infer_ctx_k_partial) == (← do_step ⟪₂ :: exec (:: :k_type :test_ctx_k_type) ⟫))

/-
Will run the function, but execute later.
-/
def lazy_exec (f g : Expr) : Expr :=
  ⟪₂ (:: both (:: (:: assert exec) (:: both (:: :f :g)))) ⟫

def lazy_exec_apply (f g : Expr) : Expr :=
  ⟪₂ (:: both (:: (:: both (:: (:: assert exec) (:: both (:: :f :g)))) (:: assert apply))) ⟫

#eval lazy_exec ⟪₂ read ⟫ ⟪₂ read ⟫
#eval lazy_exec_apply ⟪₂ read ⟫ ⟪₂ read ⟫

/-
Assert exec it thinks is suspicious.

I feel like we should use exec instead of push_on here.

I want a better pattern for this. It happens quite often.

We could just use apply instead.
Also, we should make a macro / helper for exec.

((:: exec) ((:: read) ((:: ((:: ((:: exec) ((:: ((:: assert) exec)) ((:: ((:: ((:: next) read)) quote)) ((:: ((:: assert) read)) nil))))) ((:: push_on) apply))) ((:: ((:: assert) Data)) nil))))
-/

def lazy_all (f : Expr) : Expr :=
  ⟪₂ (:: exec (:: (:: assert exec) :f)) ⟫

/-
Other lazy all:
:: (:: exec :f) (:: (:: push_on apply) (:: both (:: assert exec) assert))
-/

def lazy_all_apply (f : Expr) : Expr :=
  ⟪₂ :: (:: exec :f) (:: (:: push_on apply) (:: both (:: assert exec) assert)) ⟫

#eval lazy_all_apply ⟪₂ (:: (:: read quote) (:: (:: (:: next (:: read quote))) nil)) ⟫
#eval lazy_all_apply ⟪₂ (:: (:: read quote) (:: (:: next (:: read quote)) nil)) ⟫
def test_lazy_apply : Except Error Bool := do
  let my_l := ⟪₂ (:: (:: read quote) (:: (:: next (:: read quote)) nil)) ⟫
  let my_f := lazy_all_apply my_l
  pure <| (← exec_op my_f ⟪₂ :: Data (:: Data nil) ⟫) == (← (exec_op my_f ⟪₂ :: Data nil ⟫ >>= (exec_op · ⟪₂ :: Data nil⟫)))

#eval test_lazy_apply

/-def test_lazy_exec : Except Error Expr :=
  ⟪₂ :: exec (:: (#lazy_exec_apply -/

--((:: both) ((:: ((:: both) ((:: ((:: assert) exec)) ((:: read) ((:: push_on) read))))) ((:: assert) apply)))

def s_type : Expr :=
  let α := ⟪₂ read ⟫
  let β := ⟪₂ :: next read ⟫
  let γ := ⟪₂ :: next (:: next read) ⟫
  let y := ⟪₂ :: next (:: next (:: next (:: next read))) ⟫
  let z := ⟪₂ :: next (:: next (:: next (:: next (:: next read)))) ⟫

  let t_α := ⟪₂ Data ⟫
  let t_β := ⟪₂ :: :α (:: push_on (:: Data nil)) ⟫

  -- γ := ∀ (x : α) (y : β x), Data
  let βx := lazy_all_apply ⟪₂ :: (:: :β quote) (:: (:: assert read) nil) ⟫
  --let βx := lazy_exec_apply ⟪₂ :: :β quote ⟫ ⟪₂ :: (:: assert read) (:: (:: assert Data) nil) ⟫
  --dbg_trace βx'
  --let βx := ⟪₂ :: (:: both (:: (:: assert exec) (:: :β (:: push_on read)))) :apply_later ⟫
  let t_γ := ⟪₂ :: exec (:: :α (:: :βx (:: (:: assert Data) nil))) ⟫

  dbg_trace s!"γ: {t_γ}"
  --let t_γ := ⟪₂ :: (:: exec (:: read (:: :βx (:: assert (:: Data nil))))) apply ⟫
  --let t_γ := ⟪₂ :: both (:: read (:: :βx (:: push_on (:: Data nil)))) ⟫

  -- x : ∀ (x : α) (y : β x), γ x y
  let γxy := lazy_all_apply ⟪₂ :: (:: :γ quote) (:: (:: assert read) (:: (:: assert (:: next read)) nil)) ⟫
  let t_x := ⟪₂ :: exec (:: :α (:: :βx (:: :γxy nil))) ⟫

  -- y : ∀ (x : α), β x
  let t_y := ⟪₂ :: exec (:: :α (:: :βx nil)) ⟫

  let t_z := α

  -- S x y z : γ z (y z)
  let yz := ⟪₂ :: (:: exec (:: :y (:: :z nil))) apply ⟫
  let t_out := ⟪₂ :: (:: exec (:: :γ (:: :z (:: :yz nil)))) apply ⟫

  ⟪₂ :: :t_α (:: :t_β (:: :t_γ (:: :t_x (:: :t_y (:: :t_z (:: :t_out nil)))))) ⟫

/-
Test context for:
S Data (I Data) (K Data Data) (K Data Data) (I Data) Data
-/
def test_ctx_s_type : Expr :=
  ⟪₂ :: Data (:: (quoted (I Data)) (:: (quoted (K' Data Data)) (:: (quoted (K' Data Data)) (:: (quoted (I Data)) (:: Data nil))))) ⟫

#eval do_step ⟪₂ :: exec (:: ((:: Data) ((:: ((:: ((:: exec) ((:: ((:: assert) quoted (I Data))) ((:: read) nil)))) apply)) ((:: Data) nil))) (:: Data nil)) ⟫

#eval Expr.as_list <$> do_step ⟪₂ :: exec (:: :s_type :test_ctx_s_type) ⟫

/-
How do we deal with non-beta-normal values?
i.e., contexts?

Ideally, as much of the context is stripped out as possible.

One way we could do this is by inserting it in an exec position where it is a no-op.

The other INSANELY jank thing we could do is normalize but offset all the next's...

The one thing I like about the offset idea is that things are nice and uniform.
This is an interesting idea.

I really like it actually.
Really like it. Wait actually good ass idea.
-/
