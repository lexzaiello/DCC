import Dcc.Ast.Core
import Dcc.Ast.Dsl

namespace Expr

open Std (ToFormat Format format) in
def toFormat (e : Expr) (pretty : Bool := False) : Std.Format :=
  let sepD (l : List Std.Format) (sep : Std.Format := .line) (indent : ℕ := 2) : Std.Format :=
    .nest indent (.joinSep l sep)
  let paren (s : Std.Format) : Std.Format :=
    .bracket "(" (.fill s) ")"

  let comb (pre : Std.Format) (points : List Std.Format) (paren : Std.Format → Std.Format := paren) : Std.Format :=
    paren ((.align Bool.false) ++ (pre ++ " " ++ (.group (sepD points (indent := min pre.pretty.length.succ 30)))))

  open Dsl in match e with
  | .hole _ => "⋯"
  | DCC True => "True"
  | DCC False => "False"
  | DCC Bool => "Bool"
  | DCC (Bool.Rec motive x y) => comb "Bool.Rec" [motive.toFormat pretty, x.toFormat pretty, y.toFormat pretty]
  | DCC (Dup B x) => comb "Dup" [B.toFormat pretty, x.toFormat pretty]
  | DCC (Map A B x y) => comb "Map" [A.toFormat pretty, B.toFormat pretty, x.toFormat pretty, y.toFormat pretty]
  | DCC (Assoc A B C) => comb "Assoc" [A.toFormat pretty, B.toFormat pretty, C.toFormat pretty]
  | DCC (⊥.Rec motive) => comb "⊥.Rec" [motive.toFormat pretty]
  | DCC (? m) => comb "?" [m.toFormat pretty]
  | (DCC ⊤)                   => "⊤"
  | (DCC ⊥)                   => "⊥"
  | (DCC ∗)                   => "∗"
  | DCC (Swap B C) => comb "Swap" [B.toFormat pretty, C.toFormat pretty]
  | (DCC (!<> f))             => comb "!<>" [f.toFormat pretty]
  | (DCC ($<> f))                => comb "$<>" [f.toFormat pretty]
  | (DCC (& x))                => comb "&" [x.toFormat pretty]
  | (DCC (* A))              => comb "*" [A.toFormat pretty]
  | (DCC (! x))                => comb "!" [x.toFormat pretty]
  | (DCC (Eval α β x))       => comb "Eval" [α.toFormat pretty, β.toFormat pretty, x.toFormat pretty]
  | (DCC (`β x))             => comb s!"`{β.toFormat pretty}" [x.toFormat pretty]
  | (DCC (Id α))               => comb "Id" [α.toFormat pretty]
  | (DCC Sort m)              => .paren ("Sort " ++ (Std.format m))
  | (DCC (Fst β))             => comb "Fst" [β.toFormat pretty]
  | (DCC (Snd β))             => comb "Snd" [β.toFormat pretty]
  | (DCC (Λ α β e))          => comb "Λ" [α.toFormat pretty, β.toFormat pretty, e.toFormat pretty]
  | (DCC (!Λ α β e))         => comb "!Λ" [α.toFormat pretty, β.toFormat pretty, e.toFormat pretty]
  | (DCC (Π α β))             =>
    comb "Π" [α.toFormat pretty, β.toFormat pretty]
  | (DCC (⟨,⟩B a b))           =>
    comb s!"⟨,⟩{B.toFormat pretty}" [a.toFormat pretty, b.toFormat pretty]
  | (DCC (,B a b))           =>
    comb s!",{B.toFormat pretty}" [a.toFormat pretty, b.toFormat pretty]
  | (DCC (Σ α β))             => comb "Σ" [α.toFormat pretty, β.toFormat pretty]
  | (DCC (= A x y))             => comb "=" [A.toFormat pretty, x.toFormat pretty, y.toFormat pretty]
  | (DCC (Eql f_α))            => comb "Eql" [f_α.toFormat pretty]
  | (DCC (refl f_α))           => comb "refl" [f_α.toFormat pretty]
  | (DCC (∘ f g))               =>
    comb "∘" [f.toFormat pretty, g.toFormat pretty]
  | (DCC (f x))               =>
    if pretty then
      match (DCC (f x)) with
      | _ => (paren (f.toFormat pretty ++ .line ++ (x.toFormat pretty)))
    else (paren (f.toFormat pretty ++ .line ++ (x.toFormat pretty)))
termination_by e

end Expr

instance Expr.instFormat : Std.ToFormat (Expr) := ⟨Expr.toFormat⟩
instance Expr.instRepr   : Repr (Expr) := ⟨fun e _ => Std.Format.paren ("DCC" ++ .line ++ (.group (Expr.toFormat e)))⟩

open Dsl in
#eval (DCC ((Π (= ((Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1)) ((Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1)) ((Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1) (Sort 1))) (`Sort 1 (`⊤ Sort 2))) ⊤))

