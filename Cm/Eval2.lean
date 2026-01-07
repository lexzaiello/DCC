import Cm.Ast
import Cm.Error

def unwrap_with {α : Type} (ε : Error) (o : Option α) : Except Error α :=
  (o.map Except.ok).getD (.error ε)

def exec_op (my_op : Expr) (ctx : Expr) : Except Error Expr :=
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
  | _, _ => .error <| .stuck ⟪₂ :: exec (:: (:: :my_op nil) :ctx) ⟫

#eval exec_op ⟪₂ :: (:: exec (:: read (:: read nil))) apply ⟫ ⟪₂ :: Data nil ⟫

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

def try_step_n (n : ℕ) (e : Expr) : Except Error Expr := do
  if n = 0 then
    pure e
  else
    let e' ← step e
    (try_step_n (n - 1) e') <|> (pure e')

def do_step : Expr → Except Error Expr := try_step_n 30

def try_step_n! (n : ℕ) (e : Expr) : Expr := (try_step_n n e).toOption.getD e

def my_k_type : Expr :=
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

def my_i_type : Expr :=
  let t_α := ⟪₂ Data ⟫
  let α := ⟪₂ read ⟫

  ⟪₂ :: :t_α (:: :α (:: :α nil)) ⟫

#eval do_step ⟪₂ :: exec (:: :my_i_type (:: Data (:: Data nil))) ⟫

/-
Example k type:

K Data (I Data) Data Data

Also remember:
- our (I Data) term will be quoted.
-/

def test_ctx_k_type : Expr :=
  ⟪₂ :: Data (:: (quoted (I Data)) (:: Data (:: Data nil))) ⟫

--#eval exec_op ⟪₂ ((:: ((:: exec) ((:: ((:: next) read)) ((:: next) ((:: next) read))))) apply) ⟫ test_ctx_k_type
#eval do_step ⟪₂ :: exec (:: :my_k_type :test_ctx_k_type) ⟫

def test_ctx_k_partial : Expr :=
  ⟪₂ :: Data nil ⟫

/-
Applying α arg then β, then x, then y
-/
def infer_ctx_k_partial : Except Error Expr := do
  let t₁ ← do_step ⟪₂ :: exec (:: :my_k_type :test_ctx_k_partial) ⟫
  let t₂ ← do_step ⟪₂ :: exec (:: :t₁ (:: Data (:: (quoted (I Data)) nil))) ⟫
  do_step ⟪₂ :: exec (:: :t₂ (:: Data (:: (quoted (I Data)) (:: Data (:: Data nil))))) ⟫

#eval (do pure <| (← infer_ctx_k_partial) == (← do_step ⟪₂ :: exec (:: :my_k_type :test_ctx_k_type) ⟫))

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
Prepends an application after processing the context

in γ's β x, β gets seen immediately, but x does not.

we can map these as a list.

Apply later chains a function with a future list application.
-/
def apply_later (f : Expr) : Expr :=
  ⟪₂ :: (:: both (:: (:: assert exec) :f)) (:: push_on apply) ⟫

def apply_all_later (f : Expr) : Expr :=
  ⟪₂ :: (:: (:: exec (:: (:: assert exec) :f)) apply) (:: push_on apply) ⟫

/-
I don't think we need apply later.
We can probably do this easier with both ngl.

both list

(:: both (:: (:: assert both) :f)) this will wrap f with the oth.
-/

/-
This assumes f is a list.
-/
def lazy_both (f : Expr) : Expr :=
  ⟪₂ (:: both (:: (:: assert both) :f)) ⟫

def lazy_both_apply (f : Expr) : Expr :=
  ⟪₂ :: (#lazy_both f) (:: push_on apply) ⟫

def lazy_all (f : Expr) : Expr :=
  ⟪₂ (:: exec (:: (:: assert exec) :f)) ⟫

def lazy_all_apply (f : Expr) : Expr :=
  ⟪₂ :: (#lazy_all f) (:: push_on apply) ⟫

#eval exec_op (lazy_both ⟪₂ read ⟫) ⟪₂ :: Data nil ⟫
#eval exec_op (lazy_both_apply ⟪₂ read ⟫) ⟪₂ :: (:: read read) nil ⟫
#eval exec_op (lazy_all_apply ⟪₂ (:: (:: read quote) (:: (:: read quote) nil)) ⟫) ⟪₂ :: Data nil ⟫
#eval exec_op ⟪₂ ((:: ((:: both) ((:: read) read))) apply) ⟫ ⟪₂ :: Data nil ⟫

#eval do_step ⟪₂ :: exec (:: (:: (#apply_all_later ⟪₂ (:: read (:: read nil)) ⟫) nil) (:: Data nil)) ⟫

/-def test_lazy_exec : Except Error Expr :=
  ⟪₂ :: exec (:: (#lazy_exec_apply -/

--((:: both) ((:: ((:: both) ((:: ((:: assert) exec)) ((:: read) ((:: push_on) read))))) ((:: assert) apply)))

def my_s_type : Expr :=
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

  dbg_trace t_γ

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

#eval Expr.as_list <$> do_step ⟪₂ :: exec (:: :my_s_type :test_ctx_s_type) ⟫
