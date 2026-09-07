import Dcc.Eta.Nbe2.RedSpine
import Dcc.Eta.Nbe2.Hole
import Dcc.Eta.Nbe2.Domain
import Dcc.Eta.Nbe2.RedHole
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

universe u
variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace GenericExpr

/-
Combinators which can be reduced to a canonical form that is well-behaved:
- doesn't contain more holes
- Is an atomic expression with no further functions in it.
-/
inductive ReadbackAtom : (f : GenericExpr τ_c)
  → (h_dom : Domain f A)
  → (e_h : Hole A lv x)
  → (hlt : f.max_hole < lv)
  → (hrt : ViewAppHole f x lv hlt e_h.max_hole)
  → (f' : GenericExpr τ_c) → Type u
  | id    {h_dom : Domain f A} {e_h : Hole A lv x}
    {hrt : ViewAppHole f x lv hlt e_h.max_hole} :
    (heq : hrt.reduction.fst = x) → ReadbackAtom f h_dom e_h hlt hrt (DCC? Id(A))
  | fst   {h_dom : Domain f (DCC? Coup(B))} {e_h : Hole (DCC? Coup(B)) lv (DCC? ⟦_B⟧(x, y))}
    {hrt : ViewAppHole f (DCC? ⟦_B⟧(x, y)) lv hlt e_h.max_hole} :
    (heq : hrt.reduction.fst = x) → ReadbackAtom f h_dom e_h hlt hrt (DCC? Fst(B))
  | snd   {h_dom : Domain f (DCC? Coup(B))} {e_h : Hole (DCC? Coup(B)) lv (DCC? ⟦_B⟧(x, y))}
    {hrt : ViewAppHole f (DCC? ⟦_B⟧(x, y)) lv hlt e_h.max_hole} :
    (heq : hrt.reduction.fst = y) → ReadbackAtom f h_dom e_h hlt hrt (DCC? Snd(B))
  | quot  {h_dom : Domain f A} {e_h : Hole A lv x}
    {hrt : ViewAppHole f x lv hlt e_h.max_hole} :
    (heq : hrt = .quot (x' := x') hred hgt)
    → ReadbackAtom f h_dom e_h hlt hrt (DCC? `(A, x'))

def ViewAppHole.readback_atom? {f : GenericExpr τ_c}
  (h_dom : Domain f A)
  (e_h : Hole A lv x) (hlt : f.max_hole < lv)
  (hrt : ViewAppHole f x lv hlt e_h.max_hole) : Option (Σ' f', ReadbackAtom f h_dom e_h hlt hrt f') :=
  match hrt with
  | .quot _ _ => .some ⟨_, .quot rfl⟩
  | hrt =>
    if heq : hrt.reduction.fst = x then
      .some ⟨_, .id heq⟩
    else
      match A with
      | DCC? Coup(_B) =>
        match x with
        | DCC? ⟦__B⟧(x, y) =>
          have _hneq : x ≠ y := e_h.coup_points_neq
          if heq : hrt.reduction.fst = x then
            .some ⟨_, .fst heq⟩
          else if heq : hrt.reduction.fst = y then
            .some ⟨_, .snd heq⟩
          else .none
        | _ => .none
      | _ => .none

def ReadbackAtom.complete {f : GenericExpr τ_c}
  {h_dom : Domain f A}
  {e_h   : Hole A lv x}
  {hlt   : f.max_hole < lv}
  {hrt   : ViewAppHole f x lv hlt e_h.max_hole}
  (h     : ReadbackAtom f h_dom e_h hlt hrt f') : hrt.readback_atom? h_dom e_h = .some ⟨f', h⟩ := by
  unfold ViewAppHole.readback_atom?
  split
  case h_1 =>
    cases h
    case quot =>
      expose_names
      cases hrt_1.unique hred
      cases hrt_1.eq hred
      simp
    case id =>
      rename_i heq
      simp [ViewAppHole.reduction] at heq
      cases heq
      grind
    case fst | snd =>
      rename_i e_h hr hrt heq
      simp [ViewAppHole.reduction] at heq
      cases heq
      have h₁ := e_h.min_hole
      have h₂ := e_h.max_hole
      grind
  case h_2 =>
    split
    case isTrue hrt' hn heq =>
      cases hrt.eq hrt'
      cases h
      case id | quot => grind
      case fst heq' | snd heq' => cases heq'.symm.trans heq
    case isFalse hrt' hn heq =>
      cases hrt.eq hrt'
      cases h
      case id => grind
      case fst heq' | snd heq' =>
        rename_i B _B x y e_h
        have hneq := e_h.coup_points_neq
        aesop
      case quot heq' =>
        cases heq'
        grind

def ReadbackAtom.ext (hr₁ : RedSpineNorm (DCC? (f x)) B)
  (hr₂    : RedSpineNorm (DCC? (g x)) B)
  (h_dom₁ : Domain f A)
  (h_dom₂ : Domain g A)
  (e_h    : Hole A lv x)
  (hlt₁   : f.max_hole < lv)
  (hlt₂   : g.max_hole < lv)
  (hrt₁   : f.ViewAppHole x lv hlt₁ e_h.max_hole)
  (hrt₂   : g.ViewAppHole x lv hlt₂ e_h.max_hole)
  (hrb₁   : ReadbackAtom f h_dom₁ e_h hlt₁ hrt₁ f')
  (hrb₂   : ReadbackAtom g h_dom₂ e_h hlt₂ hrt₂ g') : f' = g' := by
  let hr₃  := hrt₁.reduction.snd
  let hr₄  := hrt₂.reduction.snd
  cases hrb₁ with
  | snd heq₁ =>
    cases hrb₂ with
    | snd heq₂ => rfl
    | fst heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      expose_names
      have hneq := e_h.coup_points_neq
      simp_all
    | id heq₂ =>
      have heqa := hr₃.unique hr₁
      have heqb := hr₄.unique hr₂
      have h := ((heq₁.symm.trans heqa).trans heqb.symm).trans heq₂
      cases h
    | quot heq₂ =>
      have heqa := hr₃.unique hr₁
      have heqb := hr₄.unique hr₂
      expose_names
      have heqa' : y = B := by
        simp_all [ViewAppHole.reduction]
      cases heqa'
      cases heq₂
      simp [ViewAppHole.reduction] at heqb
      cases heqb
      have ha := e_h.max_hole
      have hb := e_h.min_hole
      have hc := hr₁.max_hole_preserved
      cases hb
      simp_all
      grind
  | fst heq₁ =>
    cases hrb₂ with
    | fst heq₂ => rfl
    | snd heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      expose_names
      have hneq := e_h.coup_points_neq
      simp_all
    | id heq₂ =>
      have heqa := hr₃.unique hr₁
      have heqb := hr₄.unique hr₂
      have h := ((heq₁.symm.trans heqa).trans heqb.symm).trans heq₂
      cases h
    | quot heq₂ =>
      have heqa := hr₃.unique hr₁
      have heqb := hr₄.unique hr₂
      expose_names
      have heqa' : x = B := by
        simp_all [ViewAppHole.reduction]
      cases heqa'
      cases heq₂
      simp [ViewAppHole.reduction] at heqb
      cases heqb
      have ha := e_h.max_hole
      have hb := e_h.min_hole
      have hc := hr₁.max_hole_preserved
      cases hb
      simp_all
      grind
  | id =>
    cases hrb₂ with
    | snd heq' | fst heq' =>
      expose_names
      have ha := hr₁.max_hole_preserved
      have hb := hr₂.max_hole_preserved
      have hc := e_h.max_hole
      have hd := e_h.min_hole
      let h := heq ▸ hrt₁.reduction.snd
      cases h.unique hr₁
      let h' := heq' ▸ hrt₂.reduction.snd
      cases h'.unique hr₂
    | id => rfl
    | quot heq' =>
      cases heq'
      expose_names
      have ha := hr₁.max_hole_preserved
      have hb := hr₂.max_hole_preserved
      have hc := e_h.max_hole
      have hd := e_h.min_hole
      have he := hred.max_hole_preserved
      cases hrt₁
      any_goals (
        focus
        try (
          simp [ViewAppHole.reduction] at heq
          cases heq
          expose_names
          cases hrt.unique hr₁
          cases hr₂.unique hred
          cases hd
          have h : x.max_hole = x.min_hole := by grind
          grind)
        done)
      case fst | snd | unbox =>
        simp [ViewAppHole.reduction] at heq
        cases heq
      case eql =>
        simp [ViewAppHole.reduction] at heq
  | quot heq₁ =>
    cases hrb₂ with
    | fst heq' | snd heq' =>
      expose_names
      have ha := hr₁.max_hole_preserved
      have hb := hr₂.max_hole_preserved
      have hc := e_h.max_hole
      have hd := e_h.min_hole
      let h := heq₁ ▸ hrt₁.reduction.snd
      cases h.unique hr₁
      let h' := heq' ▸ hrt₂.reduction.snd
      simp_all [ViewAppHole.reduction]
      cases heq₁
      simp [ViewAppHole.reduction] at hr₁
      simp [ViewAppHole.reduction] at hr₂
      simp [ViewAppHole.reduction] at hr₃
      simp [ViewAppHole.reduction] at h
      cases hr₂.unique hr₄
      have h := heq' ▸ h'.max_hole_preserved
      grind
    | quot heq' =>
      expose_names
      let h := heq₁ ▸ hrt₁.reduction.snd
      cases h.unique hr₁
      let h' := heq' ▸ hrt₂.reduction.snd
      cases h'.unique hr₂
      rfl
    | id heq' =>
      expose_names
      have ha := hr₁.max_hole_preserved
      have hb := hr₂.max_hole_preserved
      have hc := e_h.max_hole
      have hd := e_h.min_hole
      let h := heq₁ ▸ hrt₁.reduction.snd
      cases h.unique hr₁
      let h' := heq' ▸ hrt₂.reduction.snd
      have he := h'.max_hole_preserved
      cases heq₁
      simp_all [← h'.unique hr₂]
      cases hrt₂
      · expose_names
        simp [ViewAppHole.reduction] at heq'
        cases heq'
        grind
      any_goals (
        focus
        try (
          expose_names
          simp [ViewAppHole.reduction] at heq'
          cases heq'
          simp [ViewAppHole.reduction] at hr₁
          simp [ViewAppHole.reduction] at h
          simp [ViewAppHole.reduction] at hr₂
          cases hrt.unique hr₂
          grind)
        done)
      case fst | snd | unbox =>
        simp [ViewAppHole.reduction] at heq'
        cases heq'
      case eql => simp [ViewAppHole.reduction] at heq'

end GenericExpr
