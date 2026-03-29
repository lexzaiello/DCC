import Dcc.Ast2
import Dcc.Eval2
import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Relation

/-
Combinator version of flip.

flip' f x y = f y x
-/
def flip' : Expr :=
  SK ((Λ) ∘ (((∘) (App ∘ flip)) ∘ (pair id)))

/-
assoc ((a, b), c) = (a, (b, c))

App ((a, b), c) = (a, b) c

flip ((a, b), c) = (c, (b, a))
App (c, (b, a)) = c (b, a)
flip ∘ ⟨flip' coup c, id⟩ (b, a) = (a, (b, c))

((flip' pair id) ∘ (flip' coup)) c = ⟨(flip' coup c), id⟩

⟨id, ((pair id) ∘ (flip' coup))⟩ ((a, b), c)
= ((a, b), ⟨id, (flip' coup c)⟩)

App ∘ flip ∘ ⟨id, ((pair id) ∘ (flip' coup))⟩ = (⟨id, (flip' coup c)⟩, (a, b))
= ⟨id, (flip' coup c)⟩ (a, b) = (a, (b, c))
-/
def assoc : Expr :=
  SK App ∘ flip ∘ ⟨id, ((pair id) ∘ (flip' coup))⟩

#eval Std.format <| (SK (assoc ((Sort 0, Sort 1), Sort 2))).reduce

#eval Std.format <| (SK ((((Λ) ∘ (((∘) (App ∘ flip)) ∘ (pair id))) (Sort 0)) (Sort 1) (Sort 2))).reduce

#eval Std.format <| (SK (Λ(App ∘ flip ∘ ⟨id, Sort 0⟩) (Sort 1) (Sort 2))).reduce
#eval Std.format <| (SK (flip' (Sort 0) (Sort 1) (Sort 2))).reduce

/-
(f ≫ g) a = g (f a), as opposed to (f ∘ g) a = f (g a)
-/
def pipe : Expr :=
  SK (flip' (∘))

syntax:50 expr:50 "≫" expr:51 : expr

syntax "(" "≫" ")" : expr

macro_rules
  | `(SK $f:expr ≫ $g:expr) => `(SK (#(pipe) $f:expr $g:expr))
  | `(SK (≫)) => `(pipe)

/-
App₂ f (x, y) = f x y

⟨f, id⟩ (x, y) = (f x, y)

(App ∘ ⟨f, id⟩) (x, y) = f x y

((pair ≫ id) ≫ ((∘) App)) f = ⟨f, id⟩

((pair ≫ id)
-/
def App₂ : Expr :=
  SK (((flip' pair id)) ≫ ((∘) App))

/-
Make a lens from a couple

lens' (a, b) = { a, b }
-/
def lens' : Expr :=
  (SK (App₂ lens))

syntax "({})" : expr

macro_rules
  | `(SK ({})) => `(lens')

#eval Std.format <| (SK (App₂ (Sort 0) (Sort 1, Sort 2))).reduce

def K'.type (m n : Level) : Expr :=
  SK (Sort m, {(quot (Sort n)), Λ({fst, flip ≫ ⟨id, quot⟩ ≫ quot})})

def K.type (m n : Level) : Expr :=
  SK (Sort m, {
    (flip' coup (quot (Sort n))), Λ({
    fst, Λ({App ∘ ⟨snd, id⟩, Λ(fst ∘ fst ∘ fst)})})})

def S.type (m n o : Level) : Expr :=
  let discard_sort_o := SK (K'.{[1, m]}
    ((__ ∶ Sort n), (quot (Sort o.succ)))
    (__ ∶ Sort m)
    (K'.{[o.succ.succ, n]} (Sort o.succ) (__ ∶ Sort n) (Sort o)))
  let out_α_β_γ := SK (Λ(App ∘ flip) discard_sort_o) ∘ (App₂ S.{[m, n, o.succ]})
  SK (Sort m,
    {(flip' coup (quot (Sort n))),
      Λ({⟨id, (flip' lens (quot (quot (Sort o))))⟩,
        Λ({assoc ≫ ⟨id, ({}) ∘ id⟩,
          Λ({fst ≫ fst, -- (((α, β), γ), x)
            -- ((((α, β), γ), x), y)
            Λ({fst ≫ fst ≫ fst ≫ fst,
            -- (((((α, β), γ), x), y), z) ⟨⟨fst ≫ (⟨out_α_β_γ, id⟩ ≫ App), id⟩ ≫ App, id⟩ ≫ App
            Λ(App ∘ ⟨App ∘ ⟨App ∘ ⟨out_α_β_γ, id⟩, id⟩, id⟩)})})})})})

inductive Expr.Reduced : Expr → Expr → Prop
  | mk : Expr.RedTyReflTrans e e' → e'.IsNorm → e.Reduced e'

theorem Expr.Reduced.decreasing? (h : Expr.Reduced e e') : e'.ty_size ≤ e.ty_size :=
  let ⟨hreflred, h_norm⟩ := h
  let hreflred : Relation.ReflGen (Relation.TransGen Expr.RedTy) e e' := Relation.reflGen_transGen.symm ▸ hreflred
  match heq : hreflred with
  | .refl => Nat.le_refl e.ty_size
  | .single h => by
    change Expr.RedTyTrans _ _ at h
    exact le_of_lt h.decreasing'

inductive Expr.Reduces : Expr → Expr → Prop
  | mk : Expr.RedTyTrans e e' → e'.IsNorm → e.Reduces e'

/-
Pair-like objects like (a, b) can be projected.
However, if snd is applied to something that is not a pair,
no projection occurs.
-/
inductive Expr.Projects : Expr → Expr → Expr → Prop
  | fst : Expr.Reduced e e' → Expr.IsRedex (SK (fst e')) → (SK (fst e')).Reduces e'' → Expr.Projects (SK fst) e e''
  | snd : Expr.Reduced e e' → Expr.IsRedex (SK (snd e')) → (SK (snd e')).Reduces e'' → Expr.Projects (SK snd) e e''

theorem Expr.Reduces.decreasing : Expr.Reduces e e' → e'.ty_size < e.ty_size
  | ⟨hred, _e⟩ => hred.decreasing'

theorem Expr.RedTyTrans.fst_decreasing (h_redex : Expr.IsRedex (SK (fst e)))
  (h : Expr.RedTyTrans (SK (fst e)) a) : a.ty_size < e.ty_size := by
  induction heq : h with
  | single h_red =>
    cases h_red
    repeat (simp only [ty_size]; grind only)
  | tail h_trans h_single =>
    rename_i b c ih
    have dec₁ := ih h_trans
    have dec₂ := h_single.decreasing'
    grind only

-- IsRedex here is essentially a proof that e is some kind of pair-like object
theorem Expr.RedTyTrans.snd_decreasing (h_redex : Expr.IsRedex (SK (snd e)))
  (h : Expr.RedTyTrans (SK (snd e)) a) : a.ty_size < e.ty_size := by
  induction heq : h with
  | single h_red =>
    cases h_red
    repeat (simp only [ty_size]; grind only)
  | tail h_trans h_single =>
    rename_i b c ih
    have dec₁ := ih h_trans
    have dec₂ := h_single.decreasing'
    grind only

theorem Expr.Projects.decreasing (h : Expr.Projects π e e'') : e''.ty_size < e.ty_size :=
  match heq : h with
  | .fst h_red' h_redex ⟨h_red, h_norm⟩ => by
    let h_dec_le := h_red'.decreasing?
    let h := h_red.fst_decreasing h_redex
    linarith
  | .snd h_red' h_redex ⟨h_red, h_norm⟩ => by
    let h_dec_le := h_red'.decreasing?
    let h := h_red.snd_decreasing h_redex
    linarith

inductive DefEq : Expr → Expr → Prop
  | single : Expr.Reduced a c → Expr.Reduced b c → DefEq a b
  | pair   : (SK fst).Projects t₁ α₁
    → (SK fst).Projects t₂ α₂
    → (SK snd).Projects t₁ β₁
    → (SK snd).Projects t₂ β₂
    → DefEq α₁ α₂
    → DefEq (SK (β₁ (__ ∶ α₁))) (SK (β₂ (__ ∶ α₁))) -- here, need to apply x. we can do structural recursion.
    → DefEq t₁ t₂

inductive Judge : Expr → Expr → Prop
  | k    : Judge (K.type m n) (SK K.{[m, n]})
  | k'   : Judge (K'.type m n) (SK K'.{[m, n]})
  | s    : Judge (S.type m n o) (SK S.{[m, n, o]})
  | srt  : Judge (SK Sort m.succ) (SK Sort m)
  | app  : Judge (SK t_f) f
    → (SK (fst t_f)).Reduces α₁
    → Judge α₂ x
    → DefEq α₁ α₂
    → Judge (SK ((snd t_f) x)) (SK (f x))
  | pair : Judge (SK Sort 1) (SK ⟨α, β⟩)
  | coup : Judge (SK Sort 1) (SK (α, β))
  | lens : Judge (SK Sort 1) (SK ({α, β} _e))

def Expr.mk_reduced (e : Expr) : ((e' : Expr) × (PLift (e.Reduced e'))) :=
  ⟨e.reduce, ⟨⟨reduce_sound rfl, reduce_norm rfl⟩⟩⟩

def Expr.mk_reduces (e : Expr) : Option ((e' : Expr) × (PLift (e.Reduces e'))) :=
  match heq : e.reduce!? with
  | .none => .none
  | .some t' =>
    let h_norm := reduce!?_norm heq
    let ht := reduce!?_sound heq
    .some ⟨t', ⟨⟨ht, h_norm⟩⟩⟩

def Expr.project (π e : Expr) : Option ((e' : Expr) × (PLift (Expr.Projects π e e'))) := do
  let ⟨e', ⟨h⟩⟩ := e.mk_reduced
  if h_redex : (SK (π e')).IsRedex then
    let ⟨e'', ⟨red⟩⟩ ← (SK (π e')).mk_reduces
    match π with
    | SK fst =>
      .some ⟨e'', ⟨.fst h h_redex red⟩⟩
    | SK snd =>
      .some ⟨e'', ⟨.snd h h_redex red⟩⟩
    | _ => .none
  else
    .none

def Expr.mk_def_eq (t₁ t₂ : Expr) : Option (PLift (DefEq t₁ t₂)) := do
  let ⟨t₁', ⟨h₁'⟩⟩ := t₁.mk_reduced
  let ⟨t₂', ⟨h₂'⟩⟩ := t₂.mk_reduced

  if h_same : t₁' = t₂' then
      .some ⟨.single (h_same ▸ h₁') h₂'⟩
  else
    let ⟨α₁, ⟨h_r_α₁⟩⟩ ← (SK fst).project t₁
    let ⟨α₂, ⟨h_r_α₂⟩⟩ ← (SK fst).project t₂

    let ⟨β₁, ⟨h_r_β₁⟩⟩ ← (SK snd).project t₁
    let ⟨β₂, ⟨h_r_β₂⟩⟩ ← (SK snd).project t₂

    let _dec₁ := h_r_α₁.decreasing
    let _dec₄ := h_r_β₁.decreasing

    let ⟨h₁⟩ ← mk_def_eq α₁ α₂
    let ⟨h₂⟩ ← mk_def_eq (SK (β₁ (__ ∶ α₁))) (SK (β₂ (__ ∶ α₁)))

    .some ⟨.pair h_r_α₁ h_r_α₂ h_r_β₁ h_r_β₂ h₁ h₂⟩
termination_by t₁.ty_size

def Expr.reduce!?' (e : Expr) : Option ((e' : Expr) × (PLift (RedTyTrans e e' ∧ e'.IsNorm))) :=
  match heq : e.reduce!? with
  | .some e' =>
    .some ⟨e', ⟨⟨reduce!?_sound (e' := e') heq, reduce!?_norm (e' := e') heq⟩⟩⟩
  | _ => .none

def infer (e : Expr) : Option ((t : Expr) × (PLift (Judge t e))) :=
  match e with
  | (SK S.{[m, n, o]}) => .some ⟨S.type m n o, ⟨.s⟩⟩
  | (SK K.{[m, n]}) => .some ⟨K.type m n, ⟨.k⟩⟩
  | (SK K'.{[m, n]}) => .some ⟨K'.type m n, ⟨.k'⟩⟩
  | (SK Sort m) => .some ⟨(SK Sort m.succ), ⟨.srt⟩⟩
  | SK ⟨_a, _b⟩ => .some ⟨SK Sort 1, ⟨.pair⟩⟩
  | SK (_a, _b) => .some ⟨SK Sort 1, ⟨.coup⟩⟩
  | SK ({_a, _b} _e) => .some ⟨SK Sort 1, ⟨.lens⟩⟩
  | (SK (f x)) => do
    let ⟨t_f, ⟨j_f⟩⟩ ← infer f
    let ⟨t_x, ⟨j_x⟩⟩ ← infer x

    let ⟨α, ⟨hdq⟩⟩ ← (SK (fst t_f)).mk_reduces

    let ⟨defeq⟩ ← Expr.mk_def_eq α t_x
    .some ⟨_, ⟨Judge.app j_f hdq j_x defeq⟩⟩
  | _e => .none

def infer_conv (e : Expr) : Option ((t' : Expr) × (PLift (∃ t, Judge t e ∧ t.Reduced t'))) := do
  let ⟨t, ⟨h_t⟩⟩ ← infer e
  let ⟨t', ⟨h_red⟩⟩ := t.mk_reduced
  .some ⟨t', ⟨t, h_t, h_red⟩⟩

#eval Std.format <| (·.fst) <$> infer_conv (SK (K'.{[3, 3]} (Sort 2) (Sort 2) (Sort 1) (Sort 1)))

#eval Std.format <| (SK ({snd ∘ fst,Λ(fst ∘ fst ∘ fst)} ((Sort 2, Sort 2), Sort 1))).reduce

#eval Std.format <| (SK (fst ({snd ∘ fst,Λ(fst ∘ fst ∘ fst)} ((Sort 2, Sort 2), Sort 1)))).reduce

#eval Std.format <| (·.fst) <$> infer_conv (SK ((K'.{[3, 3]} (Sort 2) (Sort 2) (Sort 1))))
#eval Std.format <| (·.fst) <$> infer_conv (SK (K.{[3, 2]} (Sort 2)
  (K'.{[3, 3]} (Sort 2) (Sort 2) (Sort 1)) (Sort 1) (Sort 0)))

#eval Std.format <| (·.fst) <$> infer_conv (SK (K'.{[4, 4]} (Sort 3) (Sort 3) (Sort 2)))

def test_S' : Option Expr := do
  (·.fst) <$> infer_conv (SK (S.{[3, 3, 3]} (Sort 2) (K'.{[4, 3]} (Sort 3) (Sort 2) (Sort 2))))

def test_S : Option Expr := do
  (·.fst) <$> infer_conv (SK (S.{[3, 3, 3]} (Sort 2) (K'.{[4, 3]} (Sort 3) (Sort 2) (Sort 2))
  (K'.{[1, 3]} (Sort 2, (quot (Sort 3))) (Sort 2) (K'.{[4, 3]} (Sort 3) (Sort 2) (Sort 2)))
  (K'.{[3, 3]} (Sort 2) (Sort 2))
  (K'.{[3, 3]} (Sort 2) (Sort 2) (Sort 1))
  (Sort 1)))

#eval Std.format <| (·.fst) <$> infer_conv (SK (K'.{[1, 3]} (Sort 3, (quot Sort 3)) (Sort 2) (K'.{[4, 4]} (Sort 3) (Sort 3) (Sort 2))))

#eval Std.format <| (·.fst) <$> infer_conv (SK ((K'.{[4, 4]} (Sort 3) (Sort 3) (Sort 2))))

--(K'.{[1, 3]} ({snd ∘ fst,Λ(fst ∘ fst ∘ fst)} ((Sort 3, Sort 3), Sort 2)) (Sort 2) (K'.{[4, 4]} (Sort 3) (Sort 3) (Sort 2)))

#eval Std.format <| (SK (fst ((snd (fst ({⟨id, (Λ(App ∘ flip ∘ ⟨id, lens⟩)
      (quot
         Sort 3))⟩,{Λ(Λ(⟨snd, ⟨lens ∘ (Λ(App ∘ flip ∘ ⟨id, (∘)⟩)
          snd) ∘ snd, Λ(Λ(snd ∘ ⟨App ∘ ⟨snd, snd⟩, snd⟩))⟩⟩ ∘ App ∘ flip ∘ ⟨id, (pair
         id) ∘ Λ(App ∘ flip ∘ ⟨id, coup⟩)⟩)),{Λ(Λ(Λ(⟨snd, (Λ(App ∘ flip ∘ ⟨id, (∘)⟩)
           snd) ∘ snd⟩ ∘ fst ∘ fst))),{snd ∘ fst ∘ fst ∘ fst ∘ fst,Λ(Λ(Λ(Λ(Λ(⟨⟨App ∘ ⟨App ∘ ⟨S.{[3,
               3,
               4]} ∘ snd, snd⟩, (quot (quot (quot Sort 3)))⟩ ∘ fst, snd⟩, snd⟩)))))}}}}
   (Sort 2, (((K'.{[4, 3]} Sort 3) Sort 2) Sort 2))))) (Sort 1)))).reduce

#eval (SK (fst ((snd ({snd ∘ fst,Λ(fst ∘ fst ∘ fst)}
   ((({snd ∘ fst,Λ(fst ∘ fst ∘ fst)} ((Sort 3, Sort 3), Sort 2)), Sort 2), (((K'.{[4, 4]} Sort 3) Sort 3) Sort 2)))) (Sort 1)))).reduce

#eval Std.format <| test_S
#eval Std.format <| (SK (snd ({Sort 2,{(((K'.{[4, 3]} Sort 3) Sort 2)
     Sort 2),(((K'.{[1, 3]} (Sort 2, (quot Sort 3))) Sort 2) (((K'.{[4, 3]} Sort 3) Sort 2) Sort 2))}}))).reduce

#eval Std.format <| test_S
