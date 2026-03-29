import Dcc.Ast2
import Dcc.Eval2
import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Relation

/-
Π extensionality. we can compare Π exactly, but we need to simulate the argument x as well when
we determine equality.

fst is concrete. snd needs "substitution." this is a very frequent operation. can we prove the size decreases
there, too? at least, the reduction of (pair-like x) decreases? certainly, but we can't recurse on it in
def-eq compute.

we need better def-eq anyway. we don't need to reduce necessarily.

syntax-directed def-eq.

we always apply x to snd.

we can carry the "context" as an argument. similar to RunPi.
RunPi (arg : Expr) : Expr → Expr → Prop.

we don't need to reduce to get snd.
we can just make Projects structural.

projects size of is decreasing.

we can do fold argument.

single is the terminal endpoint.
can carry fold argument.

accumulate holes in fold, once you reach single, you reduce with fold.
-/

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
K' type using lenses without (α, x):

K'.{[m, n]} : (Sort m, {
  quot (Sort n), {
    Λ(fst), Λ(Λ(fst ≫ snd))
  }
})

K.{[m, n]} : (Sort m, {
  flip' coup (quot (Sort n)), {
    Λ(fst), {
      Λ(Λ(App ∘ ⟨snd, id⟩)), Λ(Λ(Λ(fst ∘ fst ∘ fst)))
    }
  }
}
-/

#eval Std.format <| (SK (App₂ (Sort 0) (Sort 1, Sort 2))).reduce

def K'.type (m n : Level) : Expr :=
  SK (Sort m, {(quot (Sort n)), Λ({fst, Λ({fst ≫ snd, Λ(fst ≫ fst ≫ fst)})})})

def K.type (m n : Level) : Expr :=
  SK (Sort m, {
    (flip' coup (quot (Sort n))), Λ({
    fst, Λ({App ∘ ⟨snd, id⟩, Λ(fst ∘ fst ∘ fst)})})})

def S.type (m n o : Level) : Expr :=
  SK (Sort m,
    {snd ≫ (flip' coup (quot (Sort n))),
      {Λ(⟨snd, (((≫) snd) ∘ snd) ≫ (flip' pair (quot (Sort o)))⟩),
        {Λ(Λ(assoc ≫ (⟨snd, ⟨snd ≫ (((≫) snd) ≫ lens),
                   (Λ(Λ(snd ∘ ⟨App ∘ ⟨snd, snd⟩, snd⟩)))⟩⟩))),
          {Λ(Λ(Λ(fst ≫ fst ≫ ⟨snd, snd ≫ ((≫) snd)⟩))),
            {fst ≫ fst ≫ fst ≫ fst ≫ snd,
            Λ(Λ(Λ(Λ(Λ(⟨⟨((App ∘ ⟨App ∘ ⟨snd ≫ S.{[m, n, o.succ]}, snd⟩,
            (quot (quot (quot (Sort o))))⟩) ∘ fst), snd⟩, snd⟩)))))}}}}})

inductive Expr.Reduced : Expr → Expr → Prop
  | mk : Expr.RedTyReflTrans e e' → e'.IsNorm → e.Reduced e'

inductive Expr.Reduces : Expr → Expr → Prop
  | mk : Expr.RedTyTrans e e' → e'.IsNorm → e.Reduces e'

/-
Pair-like objects like (a, b) can be projected.
However, if snd is applied to something that is not a pair,
no projection occurs.
-/
inductive Expr.Projects : Expr → Expr → Expr → Prop
  | fst : Expr.IsRedex (SK (fst e)) → (SK (fst e)).Reduces e' → Expr.Projects (SK fst) e e'
  | snd : Expr.IsRedex (SK (snd e)) → (SK (snd e)).Reduces e' → Expr.Projects (SK snd) e e'

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

theorem Expr.Projects.decreasing (h : Expr.Projects π e e') : e'.ty_size < e.ty_size :=
  match h with
  | .fst h_redex ⟨h_red, h_norm⟩ =>
    h_red.fst_decreasing h_redex
  | .snd h_redex ⟨h_red, h_norm⟩ =>
    h_red.snd_decreasing h_redex

inductive DefEq : (fold : Expr → Expr) → Expr → Expr → Prop
  | single : Expr.Reduced (fold a) c → Expr.Reduced (fold b) c → DefEq fold a b
  | pair   : (SK fst).Projects t₁ α₁
    → (SK fst).Projects t₂ α₂
    → (SK snd).Projects t₁ β₁
    → (SK snd).Projects t₂ β₂
    → DefEq fold α₁ α₂
    → DefEq ((fun e => (SK (e (__ ∶ α₁)))) ∘ fold) β₁ β₂ -- here, need to apply x. we can do structural recursion.
    → DefEq fold t₁ t₂

inductive Judge : Expr → Expr → Prop
  | k    : Judge (K.type m n) (SK K.{[m, n]})
  | k'   : Judge (K'.type m n) (SK K'.{[m, n]})
  | s    : Judge (S.type m n o) (SK S.{[m, n, o]})
  | srt  : Judge (SK Sort m.succ) (SK Sort m)
  | app  : Judge (SK t_f) f
    → (SK (fst t_f)).Reduces α₁
    → Judge α₂ x
    → DefEq (fun e => e) α₁ α₂
    → (SK (snd t_f)).Reduces β
    → Judge (SK (β x)) (SK (f x))
  | coup : Judge (SK Sort 1) (SK (α, β))
  | pair : Judge (SK Sort 1) (SK ⟨α, β⟩)
  | conv  {α β : Expr} : Judge α x → α.Reduces β → Judge β x
  | conv' {α β : Expr} : Judge β x → α.Reduces β → Judge α x

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
  if h : (SK (π e)).IsRedex then
    let ⟨e', ⟨red⟩⟩ ← (SK (π e)).mk_reduces
    match π with
    | SK fst =>
      .some ⟨e', ⟨.fst h red⟩⟩
    | SK snd =>
      .some ⟨e', ⟨.snd h red⟩⟩
    | _ => .none
  else
    .none

def Expr.mk_def_eq (fold : Expr → Expr) (t₁ t₂ : Expr) : Option (PLift (DefEq fold t₁ t₂)) := do
  let ⟨t₁', ⟨h₁⟩⟩ := (fold t₁).mk_reduced
  let ⟨t₂', ⟨h₂⟩⟩ := (fold t₂).mk_reduced
  if h_same : t₁' = t₂' then
      .some ⟨.single (h_same ▸ h₁) h₂⟩
  else
    let ⟨α₁, ⟨h_r_α₁⟩⟩ ← (SK fst).project t₁
    let ⟨α₂, ⟨h_r_α₂⟩⟩ ← (SK fst).project t₂

    let ⟨β₁, ⟨h_r_β₁⟩⟩ ← (SK snd).project t₁
    let ⟨β₂, ⟨h_r_β₂⟩⟩ ← (SK snd).project t₂

    let _dec₁ := h_r_α₁.decreasing
    let _dec₂ := h_r_β₁.decreasing
    let _dec₃ := h_r_α₂.decreasing
    let _dec₄ := h_r_β₂.decreasing

    let ⟨h₁⟩ ← mk_def_eq fold α₁ α₂
    let ⟨h₂⟩ ← mk_def_eq ((fun e => SK (e (__ ∶ α₁))) ∘ fold) β₁ β₂

    .some ⟨.pair h_r_α₁ h_r_α₂ h_r_β₁ h_r_β₂ h₁ h₂⟩
termination_by t₁.ty_size

def Expr.reduce!?' (e : Expr) : Option ((e' : Expr) × (PLift (RedTyTrans e e' ∧ e'.IsNorm))) :=
  match heq : e.reduce!? with
  | .some e' =>
    .some ⟨e', ⟨⟨reduce!?_sound (e' := e') heq, reduce!?_norm (e' := e') heq⟩⟩⟩
  | _ => .none

def Judge.convD (h_t : Judge t e) : ((t' : Expr) × (PLift (Judge t' e))) :=
  match heq : t.reduce!? with
  | .none => ⟨t, ⟨h_t⟩⟩
  | .some t' =>
      let h_norm := reduce!?_norm heq
      let ht := reduce!?_sound heq
      ⟨t', ⟨.conv h_t ⟨ht, h_norm⟩⟩⟩

def infer (e : Expr) : Option ((t : Expr) × (PLift (Judge t e))) :=
  match e with
  | (SK K.{[m, n]}) => .some ⟨K.type m n, ⟨.k⟩⟩
  | (SK K'.{[m, n]}) => .some ⟨K'.type m n, ⟨.k'⟩⟩
  | (SK Sort m) => .some ⟨(SK Sort m.succ), ⟨.srt⟩⟩
  | (SK (_α, _β)) => .some ⟨(SK Sort 1), ⟨.coup⟩⟩
  | (SK ⟨_α, _β⟩) => .some ⟨(SK Sort 1), ⟨.pair⟩⟩
  | (SK (f x)) => do
    let ⟨t_f, ⟨j_f⟩⟩ ← infer f
    let ⟨t_x, ⟨j_x⟩⟩ ← infer x

    let ⟨α, ⟨hdq⟩⟩ ← (SK (fst t_f)).mk_reduces
    let ⟨_β, ⟨hdq₂⟩⟩ ← (SK (snd t_f)).mk_reduces

    let ⟨defeq⟩ ← Expr.mk_def_eq (fun e => e) α t_x
    .some (Judge.convD (Judge.app j_f hdq j_x defeq hdq₂))
  | _ => .none -- TODO: K type, S type

#eval Std.format <| (·.fst) <$> infer (SK (K'.{[3, 3]} (Sort 2) (Sort 2) (Sort 1) (Sort 1)))

#eval Std.format <| (SK ({snd ∘ fst,Λ(fst ∘ fst ∘ fst)} ((Sort 2, Sort 2), Sort 1))).reduce

#eval Std.format <| (SK (fst ({snd ∘ fst,Λ(fst ∘ fst ∘ fst)} ((Sort 2, Sort 2), Sort 1)))).reduce

#eval Std.format <| (·.fst) <$> infer (SK ((K'.{[3, 3]} (Sort 2) (Sort 2) (Sort 1))))
#eval Std.format <| (·.fst) <$> infer (SK (K.{[3, 2]} (Sort 2)
  (K'.{[3, 3]} (Sort 2) (Sort 2) (Sort 1)) (Sort 1) (Sort 0)))

#eval Std.format <| (SK (((snd ({snd ∘ fst,Λ(fst ∘ fst ∘ fst)} ((Sort 2, Sort 2), Sort 1))) (Sort 1)))).reduce

#eval Std.format <| (SK (fst ({(Λ(App ∘ flip ∘ ⟨id, coup⟩) (quot Sort 2)),Λ({fst,Λ({App ∘ ⟨snd, id⟩,Λ(Λ(Λ(fst ∘ fst ∘ fst)))})})} Sort 2))).reduce
