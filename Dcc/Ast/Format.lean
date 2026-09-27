import Dcc.Ast.Core
import Dcc.Ast.Dsl

namespace GenericExpr

open Std (ToFormat Format format) in
def toFormat.{u} {τ : Type u}
  (e : GenericExpr τ) (pretty : Bool := False) : Std.Format :=
  let sepD (l : List Std.Format) (sep : Std.Format := .line) (indent : ℕ := 2) : Std.Format :=
    .nest indent (.fill (.joinSep l sep))
  let paren (s : Std.Format) : Std.Format :=
    .bracket "(" (.fill s) ")"

  let comb (pre : Std.Format) (points : List Std.Format) (paren : Std.Format → Std.Format := paren) : Std.Format :=
    paren (pre ++ " " ++ (.group (sepD points (indent := min pre.pretty.length.succ 30))))

  open Dsl in match e with
  | .const _ | .hole _ => "⋯"
  | DCC? True => "True"
  | DCC? False => "False"
  | DCC? Bool => "Bool"
  | DCC? (Bool.Ind motive x y) => comb "Bool.Ind" [motive.toFormat pretty, x.toFormat pretty, y.toFormat pretty]
  | DCC? (Map A B x y) => comb "Map" [A.toFormat pretty, B.toFormat pretty, x.toFormat pretty, y.toFormat pretty]
  | DCC? (Assoc A B C) => comb "Assoc" [A.toFormat pretty, B.toFormat pretty, C.toFormat pretty]
  | DCC? (≃.Ind motive x) => comb "≃.Ind" [motive.toFormat pretty, x.toFormat pretty]
  | DCC? (≃.1 x y) => comb "≃.1" [x.toFormat pretty, y.toFormat pretty]
  | DCC? (≃.2 x y) => comb "≃.2" [x.toFormat pretty, y.toFormat pretty]
  | DCC? (≃.3 x y) => comb "≃.3" [x.toFormat pretty, y.toFormat pretty]
  | DCC? (≃.4 x y) => comb "≃.4" [x.toFormat pretty, y.toFormat pretty]
  | DCC? (≃.1.apply x y) => comb "≃.1.apply" [x.toFormat pretty, y.toFormat pretty]
  | DCC? (≃.2.apply x y) => comb "≃.2.apply" [x.toFormat pretty, y.toFormat pretty]
  | DCC? (≃.env.1 x y) => comb "≃.env.1" [x.toFormat pretty, y.toFormat pretty]
  | DCC? (≃.env.2 x y) => comb "≃.env.2" [x.toFormat pretty, y.toFormat pretty]
  | DCC? (⊥.Ind motive) => comb "⊥.Ind" [motive.toFormat pretty]
  | DCC? (≃.mk a b c d) => comb "≃.mk" [a.toFormat pretty, b.toFormat pretty, c.toFormat pretty, d.toFormat pretty]
  | DCC? (Unify τ_A τ_B A B) => comb "Unify" [τ_A.toFormat pretty, τ_B.toFormat pretty, A.toFormat pretty, B.toFormat pretty]
  | DCC? (≃ A B) => comb "≃" [A.toFormat pretty, B.toFormat pretty]
  | DCC? (? m) => comb "?" [m.toFormat pretty]
  | (DCC? ⊤)                   => "⊤"
  | (DCC? ⊥)                   => "⊥"
  | (DCC? ∗)                   => "∗"
  | DCC? (Unbang x) => comb "Unbang" [x.toFormat pretty]
  | DCC? (Dom x) => comb "Dom" [x.toFormat pretty]
  | DCC? (Cod x) => comb "Cod" [x.toFormat pretty]
  | DCC? (Dom₂ x) => comb "Dom₂" [x.toFormat pretty]
  | DCC? (Uncoup x) => comb "Uncoup" [x.toFormat pretty]
  | DCC? (Swap B C) => comb "Swap" [B.toFormat pretty, C.toFormat pretty]
  | (DCC? (!<> f))             => comb "!<>" [f.toFormat pretty]
  | (DCC? ($<> f))                => comb "$<>" [f.toFormat pretty]
  | (DCC? (& x))                => comb "&" [x.toFormat pretty]
  | (DCC? (* A))              => comb "*" [A.toFormat pretty]
  | (DCC? (! x))                => comb "!" [x.toFormat pretty]
  | (DCC? (Eval α β x))       => comb "Eval" [α.toFormat pretty, β.toFormat pretty, x.toFormat pretty]
  | (DCC? (`β x))             => comb s!"`{β.toFormat pretty}" [x.toFormat pretty]
  | (DCC? (Id α))               => comb "Id" [α.toFormat pretty]
  | (DCC? Sort m)              => .paren ("Sort " ++ (Std.format m))
  | (DCC? (Fst β))             => comb "Fst" [β.toFormat pretty]
  | (DCC? (Snd β))             => comb "Snd" [β.toFormat pretty]
  | (DCC? (Λ α β e))          => comb "Λ" [α.toFormat pretty, β.toFormat pretty, e.toFormat pretty]
  | (DCC? (!Λ α β e))         => comb "!Λ" [α.toFormat pretty, β.toFormat pretty, e.toFormat pretty]
  | (DCC? (Π α β))             =>
    comb "Π" [α.toFormat pretty, β.toFormat pretty]
  | (DCC? (⟨,⟩B a b))           =>
    comb s!"⟨,⟩{B.toFormat pretty}" [a.toFormat pretty, b.toFormat pretty]
  | (DCC? (,B a b))           =>
    comb s!",{B.toFormat pretty}" [a.toFormat pretty, b.toFormat pretty]
  | (DCC? (Σ β))             => comb "Σ" [β.toFormat pretty]
  | (DCC? (Σ α β))             => comb "Σ" [α.toFormat pretty, β.toFormat pretty]
  | (DCC? (= x y))             => comb "=" [x.toFormat pretty, y.toFormat pretty]
  | (DCC? (Eql f_α))            => comb "Eql" [f_α.toFormat pretty]
  | (DCC? (refl f_α))           => comb "refl" [f_α.toFormat pretty]
  | (DCC? (∘ f g))               =>
    comb "∘" [f.toFormat pretty, g.toFormat pretty]
  | (DCC? (f x))               =>
    if pretty then
      match (DCC? (f x)) with
      | _ => (paren (f.toFormat pretty ++ .line ++ (x.toFormat pretty)))
    else (paren (f.toFormat pretty ++ .line ++ (x.toFormat pretty)))
termination_by e

end GenericExpr

instance GenericExpr.instFormat : Std.ToFormat (GenericExpr τ) := ⟨GenericExpr.toFormat⟩
instance GenericExpr.instRepr   : Repr (GenericExpr τ) := ⟨fun e _ => Std.Format.paren ("DCC?" ++ .line ++ (.group (GenericExpr.toFormat e)))⟩

open Dsl in
#eval (DCC ((Π (Id ((Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1))) (`Sort 1 (`⊤ Sort 2))) ⊤))

