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

def cons_exec (e₁ e₂ : Expr) : Expr :=
  match e₂ with
  | ⟪₂ :: exec :xs ⟫ =>
    ⟪₂ :: exec (:: :e₁ :xs) ⟫
  | xs => ⟪₂ :: exec (:: :e₁ :xs) ⟫

def assert_all : Expr → Expr
  | ⟪₂ :: :x :xs ⟫ => ⟪₂ :: (:: assert :x) (#assert_all xs) ⟫
  | ⟪₂ nil ⟫ => ⟪₂ nil ⟫
  | e => ⟪₂ ::assert :e ⟫

def exec_next_noop (e ctx : Expr) : Option Expr :=
  match e, ctx with
  | ⟪₂ :: next :f ⟫, ⟪₂ :: :_x nil ⟫ =>
    pure f
  | ⟪₂ :: next :f ⟫, ⟪₂ nil ⟫ => pure f
  | ⟪₂ :: next :f ⟫, ⟪₂ :: :_x :_xs ⟫ => .none
  | ⟪₂ read ⟫, ⟪₂ nil ⟫ => pure ⟪₂ read ⟫
  | _, _ => .none

def exec_op (my_op : Expr) (ctx : Expr) : Except Error Expr :=
  match my_op, ctx with
  | ⟪₂ nil ⟫, _c => pure ⟪₂ nil ⟫
  | ⟪₂ :: exec nil ⟫, _ => pure ⟪₂ nil ⟫
  | ⟪₂ :: exec (:: :x :xs) ⟫, c => do
    let xs' ← exec_op ⟪₂ :: exec :xs ⟫ c
    match exec_next_noop x c with
    | .some f' =>
      pure <| cons_exec f' xs
    | _ =>
      let x' ← exec_op x c
      match xs' with
      | ⟪₂ :: exec :xs ⟫ =>
        pure <| ⟪₂ :: exec (:: (:: assert :x') :xs) ⟫
      | xs =>
        pure <| ⟪₂ :: :x' :xs ⟫
  | ⟪₂ read ⟫, ⟪₂ :: :x :_xs ⟫ => pure x
  | ⟪₂ :: :f quote ⟫, c => do
    let c' ← exec_op f c
    pure ⟪₂ :: assert :c' ⟫
  | ⟪₂ :: assert :x ⟫, _ => pure x
  | ⟪₂ quote ⟫, c => pure ⟪₂ :: assert :c ⟫
  | ⟪₂ :: next :f ⟫, ⟪₂ nil ⟫
  | ⟪₂ :: next :f ⟫, ⟪₂ :: :_x nil ⟫ => pure f
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
  dbg_trace t₁
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
I don't think we need apply later.
We can probably do this easier with both ngl.

both list

(:: both (:: (:: assert both) :f)) this will wrap f with the oth.
-/

def lazy_all (f : Expr) : Expr :=
  ⟪₂ (:: exec (:: (:: assert exec) :f)) ⟫

def lazy_all_apply (f : Expr) : Expr :=
  ⟪₂ :: (#lazy_all f) (:: push_on apply) ⟫

#eval exec_op (lazy_all_apply ⟪₂ (:: (:: read quote) (:: (:: read quote) nil)) ⟫) ⟪₂ :: Data nil ⟫
#eval exec_op ⟪₂ ((:: ((:: both) ((:: read) read))) apply) ⟫ ⟪₂ :: Data nil ⟫

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

def my_test_γ : Expr :=
  ⟪₂ ((:: Data) ((:: ((:: ((:: quoted (I Data)) read)) apply)) ((:: Data) nil))) ⟫

#eval exec_op ⟪₂ ((:: exec) ((:: ((:: read) quote)) ((:: ((:: ((:: exec) ((:: ((:: assert) exec)) ((:: ((:: ((:: next) read)) quote)) ((:: ((:: assert) read)) nil))))) ((:: push_on) apply))) ((:: ((:: assert) Data)) nil)))) ⟫ test_ctx_s_type

def test_ctx_γ : Expr :=
  ⟪₂ :: Data (:: Data nil) ⟫

#eval do_step ⟪₂ :: exec (:: :my_test_γ :test_ctx_γ) ⟫

#eval do_step ⟪₂ :: exec (:: ((:: Data) ((:: ((:: ((:: exec) ((:: ((:: assert) quoted (I Data))) ((:: read) nil)))) apply)) ((:: ((:: ((:: exec) ((:: ((:: assert) quoted ((K' Data) Data))) ((:: read) ((:: ((:: next) read)) nil))))) apply)) nil))) (:: Data (:: Data nil))) ⟫

#eval do_step ⟪₂ :: exec (:: ((:: Data) ((:: ((:: ((:: exec) ((:: ((:: assert) quoted (I Data))) ((:: read) nil)))) apply)) nil)) (:: Data (:: Data nil))) ⟫

#eval exec_op ⟪₂ ((:: ((:: exec) ((:: ((:: assert) quoted (I Data))) ((:: read) nil)))) apply) ⟫ ⟪₂ :: Data nil ⟫

#eval Expr.as_list <$> do_step ⟪₂ :: exec (:: ((:: Data) ((:: ((:: ((:: exec) ((:: ((:: assert) quoted (I Data))) ((:: read) nil)))) apply)) ((:: Data) nil))) (:: Data (:: Data nil))) ⟫

#eval Expr.as_list <$> do_step ⟪₂ :: exec (:: :s_type :test_ctx_s_type) ⟫
#eval s_type
#eval do_step ⟪₂ :: exec (:: :s_type (:: Data nil)) ⟫
#eval do_step ⟪₂ :: exec (:: ((:: Data) ((:: ((:: Data) ((:: Data) nil))) ((:: ((:: Data) ((:: ((:: ((:: exec) ((:: ((:: assert) read)) ((:: read) nil)))) apply)) ((:: Data) nil)))) ((:: ((:: Data) ((:: ((:: ((:: exec) ((:: ((:: assert) read)) ((:: read) nil)))) apply)) ((:: ((:: ((:: exec) ((:: ((:: assert) ((:: next) read))) ((:: read) ((:: ((:: next) read)) nil))))) apply)) nil)))) ((:: ((:: Data) ((:: ((:: ((:: exec) ((:: ((:: assert) read)) ((:: read) nil)))) apply)) nil))) ((:: Data) ((:: ((:: ((:: exec) ((:: ((:: next) read)) ((:: ((:: next) ((:: next) ((:: next) ((:: next) ((:: next) read)))))) ((:: ((:: ((:: exec) ((:: ((:: next) ((:: next) ((:: next) ((:: next) read))))) ((:: ((:: next) ((:: next) ((:: next) ((:: next) ((:: next) read)))))) nil)))) apply)) nil))))) apply)) nil))))))) (:: (quoted (I Data)) nil)) ⟫


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
