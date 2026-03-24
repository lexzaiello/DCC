import Dcc.Ast
import Dcc.Eval
import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Relation

/-
(B (C I arg) I) head
I head
(C I arg) (I head)
I head arg

-/

def Expr.push_ctx (Γ x : Expr) : Expr :=
  SK (B (C I x) Γ)

def K.type (m n : Level) : Expr := SK ⟨⟨Sort m, arg 0 (C cons (K* Sort n)), ret 1, arg 1 (ret 1), ret 3⟩, I⟩

--#eval Std.format <| ((K.type 1 1).reduce_pi (SK Sort 0)).fst

def K'.type (m n : Level) : Expr :=
  SK ⟨⟨Sort m, (K* (Sort n)), (arg 0 (ret 1)), (arg 1 (ret 1)), (arg 0 (ret 3))⟩, I⟩

def S.type (m n o : Level) : Expr := SK
    ⟨⟨Sort m, -- α
    arg 0 (C cons (K* Sort n)), -- β
    (B (B (C cons) (C cons (K* Sort o))) (C I)),
    (C (B B (B B cons)) cons), -- x
    (B (B K* K*) cons), -- y
    (arg 0 (ret 4)), -- z
      (B (S.{[m, n, o.succ]}
        (__ ∶ Sort m)
        (__ ∶ Sort n)
        (__ ∶ Sort o)) (arg 2 (ret 1)))⟩, I⟩

def Expr.reduce!? (e : Expr) : Option ((e' : Expr) × (PLift (Expr.RedTyTrans e e' ∧ IsNorm e'))) :=
  let e' := e.reduce
  let proof : Relation.ReflTransGen Expr.RedTy e e' := reduce_sound rfl
  let norm : IsNorm e' := reduce_norm rfl
  if heq : e = e' then
    .none
  else
    .some ⟨e', ⟨by
    rw [← Relation.reflGen_transGen] at proof
    match heq₂ : proof with
    | .refl => contradiction
    | .single h =>
      rename_i heq
      exact ⟨h, heq ▸ norm⟩⟩⟩

inductive JudgePi : (args : Expr) → Expr → Expr → Prop
  | tail : (SK (args α)).RedTyTrans α'
    → JudgePi (args.push_ctx (SK (__ ∶ α'))) t_β xs
    → JudgePi args t_β (SK (cons α xs))
  | base : (SK (args cod)).RedTyTrans (SK __ ∶ Sort m)
    → JudgePi (SK Sort m) args (SK cod)

def infer_pi (head spine : Expr) : Option ((t : Expr) × PLift (JudgePi spine t head)) :=
  match _h_eq : head, spine with
  | SK (cons α xs), args =>
    match (SK (args α)).reduce!? with
    | .some ⟨α', ⟨hrt, _h_norm⟩⟩ =>
      let _h_size_dec := hrt.decreasing'
      match infer_pi xs (args.push_ctx (SK (__ ∶ α'))) with
      | .some ⟨t_β, ⟨h_pi⟩⟩ => .some ⟨t_β, ⟨.tail hrt h_pi⟩⟩
      | .none => .none
    | .none => .none
  | _, _ => .none

/-
Attempt to normalize a terminal codomain, if possible.
A terminal codomain is the final cons in a Π list.
If a proof of TyTransRed can be produced, it is valid.

The TySize must be greater than zero. A cons list, for
example, has a TySize of zero, and is not eligible.

This is the only case in which types are normalized
during conversion.

The only other case types are normalized is in the app constructor.
-/

inductive Expr.IsCons : Expr → Prop
  | mk : Expr.IsCons (SK (cons a b))

def Expr.is_not_cons (e : Expr) : Option (PLift (¬ e.IsCons)) := by
  cases e
  repeat exact .some (.up (fun h => by contradiction))
  case app f x =>
    cases f
    repeat exact .some (.up (fun h => by contradiction))
    case app f' x' =>
      cases f'
      repeat exact .some (.up (fun h => by contradiction))
      · exact .none
      repeat exact .some (.up (fun h => by contradiction))

inductive Expr.RunPi : Expr → Expr → Prop
  -- this measure doesn't actually work
  | pi  : (¬ cod.IsCons)
    → (SK (args cod)).RedTyTrans cod'
    → RunPi (SK ⟨cod, args⟩) cod'
  | red : Expr.RedTyTrans α α' → α.RunPi α'

inductive Expr.PiSize : Expr → ℕ → Prop
  | base : ¬ t.IsCons
    → Expr.TySize t n
    → Expr.PiSize t n
  | cons : Expr.PiSize x m
    → Expr.PiSize xs n
    → Expr.PiSize (SK ⟨x, xs⟩) (m + n)

theorem Expr.PiSize.unique (h₁ : Expr.PiSize e n) (h₂ : e.PiSize m) : m = n := by
  induction h₁ generalizing m
  induction h₂ generalizing n
  · rename_i h_ty₁ _ h_ty₂
    exact (h_ty₁.unique (by assumption)).symm
  · rename_i contra _
    exfalso; exact contra .mk
  · rename_i x m xs n hp₁ hp₂ ih₁ ih₂
    cases h₂
    · rename_i h _
      exfalso; exact h .mk
    · rename_i hp₃ hp₄
      have ha := ih₁ hp₃
      have hb := ih₂ hp₄
      grind only

theorem Expr.run_pi_decreasing : Expr.RunPi t t' → Expr.PiSize t m → Expr.PiSize

inductive Judge : Expr → Expr → Prop
  | app     : Judge (SK ⟨(cons α xs), args⟩) f
    → (SK (args α)).RedTyTrans α'
    → Judge α' x
    → Judge (SK ⟨xs, #(args.push_ctx x)⟩) (SK (f x))
  | srt     : Judge (SK Sort m.succ) (SK Sort m)
  | k       : Judge (K.type m n) (SK K.{[m, n]})
  | k'      : Judge (K'.type m n) (SK K'.{[m, n]})
  | s       : Judge (S.type m n o) (SK S.{[m, n, o]})
  | pi      : JudgePi args t_β tys
    → Judge t_β (SK ⟨tys, args⟩)
  | hole    : Judge α (SK __ ∶ α) -- only visible to the kernel
  | conv  {α β : Expr} : Judge α x → α.RunPi β → Expr.IsNorm β → Judge β x

def Judge.conv?_ty (h_t : Judge α x) : Option ((t' : Expr) × (PLift (Judge t' x))) :=
  match Expr.reduce!? α with
  | .some ⟨t', ⟨h_r, h_norm⟩⟩ => .some ⟨t', ⟨.conv h_t (.red h_r) h_norm⟩⟩
  | _ => .none

def Judge.conv? (h_t : Judge α x) : Option ((t' : Expr) × (PLift (Judge t' x))) :=
  match α with
  | SK ⟨cod, args⟩ =>
    match cod.is_not_cons with
    | .some ⟨h⟩ =>
      match (SK (args cod)).reduce!? with
      | .some ⟨t', ⟨h_r, h_norm⟩⟩ => .some ⟨t', ⟨Judge.conv h_t (.pi h h_r) h_norm⟩⟩
      | _ => .none
    | _ => h_t.conv?_ty
  | _ => h_t.conv?_ty

def Judge.convD (h_t : Judge α x) : (t' : Expr) × (PLift (Judge t' x)) :=
  h_t.conv?.getD ⟨α, ⟨h_t⟩⟩

def infer (e : Expr) : Option ((t : Expr) × PLift (Judge t e)) :=
  match _h_eq : e with
  | SK Sort m => .some ⟨SK Sort m.succ, ⟨.srt⟩⟩
  | SK K.{[m, n]} => .some ⟨K.type m n, ⟨.k⟩⟩
  | SK K'.{[m, n]} => .some ⟨K'.type m n, ⟨.k'⟩⟩
  | SK S.{[m, n, o]} => .some ⟨S.type m n o, ⟨.s⟩⟩
  | SK ⟨tys, args⟩ => (infer_pi tys args).map (fun ⟨t, ⟨j_t⟩⟩ => ⟨t, ⟨.pi j_t⟩⟩)
  | SK (f x) => do
    let ⟨t_f, ⟨h_t_f⟩⟩ ← infer f
    let ⟨t_x, ⟨h_t_x⟩⟩ ← infer x

    let ⟨t_f, ⟨h_t_f⟩⟩ := h_t_f.convD
    let ⟨t_x, ⟨h_t_x⟩⟩ := h_t_x.convD

    match t_f with
    | (SK ⟨⟨α, xs⟩, args⟩) =>
      match (SK (args α)).reduce!? with
      | .some ⟨α', ⟨h_red_α, _h_norm⟩⟩ =>
        if heq : α' = t_x then
          let β' := (SK ⟨xs, #(args.push_ctx x)⟩)
          let h_app := Judge.app (x := x) (f := f) h_t_f h_red_α (by rw [heq]; exact h_t_x)
          .some h_app.convD
        else
          .none
      | _ => .none
    | _ => .none
  | _ => .none

#eval Std.format <$> (infer (SK (K'.{[2, 2]} (Sort 1) (Sort 1) (Sort 0) (Sort 0)))).map (·.fst)

theorem app_size_dec : Judge t x → Expr.RedTm x x' → Judge t' x' → Expr.PiSize t m → Expr.PiSize t' n → n < m := by
  intro h_t₀ h_red_tm h_t' h_size₀ h_size'
  
