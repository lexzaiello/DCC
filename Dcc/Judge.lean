import Dcc.Ast
import Dcc.Eval
import Mathlib.Data.Nat.Notation

def K.type (m n : Level) : Expr := (SK
  Π Sort m, Π (Π (arg 0 I), Sort n), Π (arg 0 (ret 1)), Π (arg 1 I), (arg 0 (ret 3)))

--#eval Std.format <| ((K.type 1 1).reduce_pi (SK Sort 0)).fst

def K'.type (m n : Level) : Expr :=
  (SK Π Sort m, Π (K* (Sort n)), Π (arg 0 (ret 1)), Π (arg 1 (ret 1)), (arg 0 (ret 3)))

def S.type (m n o : Level) : Expr := (SK
    Π Sort m, -- α
    Π (Π (arg 0 I), Sort n), -- β
    Π (Π (arg 0 (ret 1)), Π (arg 1 I), Sort o), -- γ
    Π (Π (arg 0 (ret 2)), Π (arg 1 (ret 1)), (arg 2 I)), -- x
    Π (Π (arg 0 (ret 3)), (arg 1 (ret 2))), -- y
    Π (arg 0 (ret 4)), -- z
      (B (S.{[m, n, o.succ]}
        (__ ∶ Sort m)
        (__ ∶ Sort n)
        (__ ∶ Sort o)) (arg 2 (ret 1)))) -- γ z (y z)
-- ^ note that this is safe, since prior apps were type-checked, and def-eq here is deferred to term-level

/-
B C K I types should never appear, except as arguments in a nested
Π binder.

They can be reduced as such:
-/

inductive PiLeaf : Expr → Prop
  | tycomb : PiLeaf (.tycomb c)
  | app    : PiLeaf f → (PiLeaf (SK (f x)))

/-
Note:
This will cause undefined behaior unless the expression being reduced is typed-checked
-/
inductive RedPiTy : Expr → Expr → Prop
  | branch : RedPiTy (SK (α x)) α'
    → RedPiTy (SK (β x)) β'
    → RedPiTy (SK ((Π α, β) x)) (SK (Π α', β'))
  -- A leaf is either a type combinator, or an application of a type combinator
  -- otherwise, it is "substituted", and has a ty_size of 0.
  | leaf   : PiLeaf e
    → (SK (e x)).RedTyTrans e'
    → e'.IsNorm
    → RedPiTy (SK (e x)) e'

-- How many Π binders are nested. For example, in an uncurried type like K's type.
inductive PiTyDepth : Expr → ℕ → Prop
  | atom : PiLeaf x → PiTyDepth x 0
  | pi   : PiTyDepth α m → PiTyDepth β n → PiTyDepth (SK Π α, β) (m + n + 1)

inductive PiTySize : Expr → ℕ → Prop
  | leaf   : PiLeaf x → x.TySize n → PiTySize x nm
  | branch : PiTySize α m
    → PiTySize β n
    → PiTySize (SK Π α, β) (m + n)
  | app    : PiTyDepth f d → PiTySize f m → PiTySize x n
    → PiTySize (SK (f x)) (m + (n * (d + 1)))

theorem RedPiTy.is_norm : RedPiTy t t' → Expr.IsNorm t' := by
  intro h
  cases h
  · intro ⟨e', hr⟩
    cases hr
  · assumption

theorem RedPiTy.decreasing (h_size : PiTySize t n) (h_red : RedPiTy t t') : ∃ n', PiTySize t' n' ∧ n' < n := by
  induction h_red generalizing n with
  | branch _ =>
    cases h_size
    · contradiction
    rename_i size_bind _
    cases size_bind
    · contradiction
    · rename_i α x α' β β' hrα hrβ ih₁ ih₂ d n h_depth_bind h_size_x d₂ m h_size α
      cases h_depth_bind
      · contradiction
      · rename_i depth_α depth_β
        have ha := ih₁ (.app depth_α h_size h_size_x)
        have hb := ih₂ (.app depth_β α h_size_x)
        have ⟨α_n', h_size_α', h_α_n'_ineq⟩ := ha
        have ⟨β_n', h_size_β', h_β_n'_ineq⟩ := hb
        refine ⟨α_n' + β_n', .branch h_size_α' h_size_β', by grind only⟩
   | _ => sorry

/-theorem RedPiTy.decreasing (h_size : PiTySize t n) (h_red : RedPiTy t t') : ∃ n', PiTySize t' n' ∧ n' < n := by
  induction t generalizing t' n with
  | Pi α β ih₁ ih₂ =>
    cases h_red with
    | ty h_bind_size h_refl_trans h_norm =>
      induction h_refl_trans
      · contradiction
      · contradiction
  | app f x ih₁ ih₂ =>
    cases h_size with
    | app h_depth h_size_f h_size_n =>
      cases h_red with
      | step hr_α hr_β =>
        
        sorry
      | _ => sorry
  | _ => contradiction-/

def Expr.red_pi_ty (e : Expr) : ((e' : Expr) × (PLift (RedPiTy e e'))) :=
  match e with
  | SK ((Π α, β) x) =>
    let ⟨α', ⟨hα⟩⟩ := red_pi_ty (SK (α x))
    let ⟨β', ⟨hβ⟩⟩ := red_pi_ty (SK (β x))
    ⟨SK (Π α', β'), ⟨.step hα hβ⟩⟩
  | e =>
    let e' := e.reduce
    let pr := reduce_sound (e' := e') rfl
    let pn := reduce_norm (e' := e') rfl
    ⟨e', ⟨.ty pr pn⟩⟩

/-
Judgments for Π combinators work inversely.

We use "typed holes." We find the innermost type combinator,
whose size is greater than 0 (Π binders have size zero), and accumulate "typed holes" as we recurse.
-/
inductive FoldElimPi : (fold : Expr → Expr) → Expr → Expr → Prop
  | single : e.TySize (m + 1)
    → FoldElimPi fold e (fold e)
  | tail   : FoldElimPi ((Expr.app · (SK (__ ∶ α))) ∘ fold) β γ
    → FoldElimPi fold (SK Π α, β) γ

def Expr.fold_elim_pi (fold : Expr → Expr) (in_e : Expr) : (Option ((e' : Expr) × (PLift (FoldElimPi fold in_e e')))) :=
  match hneq : in_e.ty_size, heeq : in_e with
  | .zero, (SK Π α, β) => match β.fold_elim_pi ((Expr.app · (SK (__ ∶ α))) ∘ fold) with
    | .some ⟨γ, ⟨h⟩⟩ => .some ⟨γ, ⟨.tail h⟩⟩
    | .none => .none
  | .succ _n, in_e => .some ⟨fold in_e, ⟨.single (Expr.TySize.sound (heeq ▸ hneq))⟩⟩
  | _, _ => .none

inductive Judge : Expr → Expr → Prop
  | app     : Judge (SK Π α, β) f
    → Judge α x
    → Judge (SK (β x)) (SK (f x))
  | srt     : Judge (SK Sort m.succ) (SK Sort m)
  | k       : Judge (K.type m n) (SK K.{[m, n]})
  | k'      : Judge (K'.type m n) (SK K'.{[m, n]})
  | s       : Judge (S.type m n o) (SK S.{[m, n, o]})
  | pi      : FoldElimPi id (SK Π α, β) elim
    → RedPiTy elim (SK __ ∶ t_β)
    → Judge t_β (SK Π α, β)
  | hole    : Judge α (SK __ ∶ α)-- only visible to the kernel
  | conv  {α β : Expr} : Judge α x → RedPiTy α β → Expr.IsNorm β → Judge β x

def infer (e : Expr) : Option ((t : Expr) × PLift (Judge t e)) :=
  match _h_eq : e with
  | SK Sort m => .some ⟨SK Sort m.succ, ⟨.srt⟩⟩
  | SK K.{[m, n]} => .some ⟨K.type m n, ⟨.k⟩⟩
  | SK K'.{[m, n]} => .some ⟨K'.type m n, ⟨.k'⟩⟩
  | SK S.{[m, n, o]} => .some ⟨S.type m n o, ⟨.s⟩⟩
  | SK (f x) => do
    let ⟨t_f, ⟨h_t_f⟩⟩ ← infer f
    let ⟨t_x, ⟨h_t_x⟩⟩ ← infer x

    let ⟨α₂, ⟨h_t_x'⟩⟩ := t_x.red_pi_ty
    let ⟨t_f', ⟨h_t_f'⟩⟩ := t_f.red_pi_ty

    match _heqf : t_f' with
    | (SK Π α, β) =>
      if heq : α = α₂ then
        let β₁ := Judge.app (.conv h_t_f h_t_f' h_t_f'.is_norm) (.conv h_t_x (heq ▸ h_t_x') (heq ▸ h_t_x'.is_norm))
        match _hsomeq : (SK (β x)).red_pi_ty with
        | ⟨β', ⟨h⟩⟩ => .some ⟨β', ⟨β₁.conv h h.is_norm⟩⟩
      else
        .none
    | _ => .none
  | SK Π α, β =>
    match (SK Π α, β).fold_elim_pi id with
    | .some ⟨elim, ⟨h⟩⟩ =>
      match elim.red_pi_ty with
      | ⟨SK __ ∶ t_β, ⟨h_red⟩⟩ => .some ⟨t_β, ⟨.pi h h_red⟩⟩
      | _ => none
    | _ => none
  | _ => .none

#eval (infer (SK (K'.{[2, 2]} (Sort 1) (Sort 1)))).map (·.fst)
