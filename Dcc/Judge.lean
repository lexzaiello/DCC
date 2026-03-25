import Dcc.Ast
import Dcc.Eval
import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Relation

/-
arguments register is like an "environment."

- fst and snd are mildly no-go, because raw BCI need to handle everything. we're not doing raw BCI, though, BCKI.

couples vs pairs.

pairs are data, projections on them, etc.

couples are functions that turn into pairs.

⟨f, g⟩ (a, b) = ⟨f a, g b⟩

we can still duplicate in linear logic, though.
this is an interesting thought.

(β : α → Type)

create a new pair via Λ

⟨x, y⟩ (a, b) = (x a, y b)


-/

/-
(B (C I arg) I) head
I head
(C I arg) (I head)
I head arg

can we side-step more suss-ness with push-ctx?

| cons      : RedTy (SK (args cod)) α'
    → RedTy (SK ⟨cod, args⟩) α'

SK (args cod) = α' → 
  (SK ⟨cod, args⟩) = α'

we are hitting normal forms in the arguments context too early.

we should only ever be able to hit that reduction until the very end.

why are we reducing for x : α? no.

push_ctx super sus.

I want something like

why is any of this running in the program?

we need an equational theory of the "context" version.

this version is kinda sus.

Λ(⟨K*, K* Type⟩)

Λ(x)yz = x (y, z)

⟨K*

⟨

ingredients we need:
- fst for pairs: fst (x, y) = x
- snd for pairs: snd (x, y) = y
- mpair / coupling matching: ⟨f, g⟩ (a, b) = (f a, g b)
- B / comp / ∘, same as always
- Λ par app: Λ(x)yz = x(y, z)
  - ac? App(Λ(x)y, z) = x(y, z)
- potentially ! from linear logic for the global argument type duplication
- composition, obviously

actually probably don't need duplication, since each step type argument produces a couple,
which we can view and manipulate later.

if we want to expand the "context" (previous step), we can just tack nil on.

would be cool if we had a combinator to selectively duplicate. explicit, though.

need a decreasing measure for that.

- "chain" combinator

(α, β) is the type of the domain and codomain

convention is α is static, apply x to β.

can make a Π combinator built with our CAM primitives.

need a combinator that consumes fst, and applies it to snd.

- can do this with Eval(f, x) = f(x)
- don't actually clone, just pass in the previous α to get β, map over that.

ac is just like a more pair-y way of doing Λ.

App(Λ(x)y, z) = x(y, z)

turns data into computation.

App ∘ ⟨Fst, Snd⟩

App ∘

if we want things fully linear, we might not even want fst / snd.

we probably want instead:
fst(a, b) = a(b)
snd(a, b) = b(a)

α → β is: (α isn't evaluated, but β has context )
(α, Λ(fst) β)

to get β, add x to the context:

((nil, α), x)

Λ(fst) β ((nil, α), x)
= fst (β ((nil, α), x)) = β

Summary of ingredients:
- nil
- Λ, skipping app for now
- fst
-snd
- couples (a, b)
- pairs ⟨a, b⟩
- composition, as before. doesn't need to be a combinator, though, just a ∘ b, due to Λ.
- grow context with (fst, x)

this is quite nice, because we don't need cons as a combinator now.
derived from Λ

nil as identity is kinda nice. pairs well with fst / snd. can get rid of K*.

nil inside types is probably useful, too, since it shows us the end of a type kinda.



fst / snd is probably necessary, though.

we can derive these rules, though.

App ∘ ⟨Fst, Snd⟩ respectively.


-/

def Expr.push_ctx (Γ x : Expr) : Expr :=
  SK (B (C I x) Γ)

def K.type (m n : Level) : Expr := SK ⟨
  ⟨Sort m, arg 0 (C cons (K* Sort n)), ret 1, arg 1 (ret 1), ret 3⟩, I⟩

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
  | conv  {α β : Expr} : Judge α x → α.RedTyTrans β → Expr.IsNorm β → Judge β x

def Judge.conv? (h_t : Judge α x) : Option ((t' : Expr) × (PLift (Judge t' x))) :=
  match Expr.reduce!? α with
  | .some ⟨t', ⟨h_r, h_norm⟩⟩ => .some ⟨t', ⟨.conv h_t h_r h_norm⟩⟩
  | _ => .none

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
  
