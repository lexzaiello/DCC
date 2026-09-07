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
ViewAppHole cases that can be condensed to a single combinator

ReadbackHead should always have size ≤ f since Domain.size <
and x' <

These are all "shortcuts" in the reduction: steps that produce a
normal form with no further spine reduction, and which can accept no further arguments.
These are mutually exclusive.
-/
inductive ReadbackHead : (f : GenericExpr τ_c)
  → (h_dom : Domain f A)
  → (e_h : Hole A lv x)
  → (hlt : f.max_hole < lv)
  → (hrt : ViewAppHole f x lv hlt e_h.max_hole)
  → (f' : GenericExpr τ_c) → Type u
  | id    {h_dom : Domain f A} {e_h : Hole A lv x}
    {hrt : ViewAppHole f x lv hlt e_h.max_hole} :
    (heq : hrt.reduction.fst = x) → ReadbackHead f h_dom e_h hlt hrt (DCC? Id(A))
  | fst   {h_dom : Domain f (DCC? Coup(B))} {e_h : Hole (DCC? Coup(B)) lv (DCC? ⟦_B⟧(x, y))}
    {hrt : ViewAppHole f (DCC? ⟦_B⟧(x, y)) lv hlt e_h.max_hole} :
    (heq : hrt.reduction.fst = x) → ReadbackHead f h_dom e_h hlt hrt (DCC? Fst(B))
  | snd   {h_dom : Domain f (DCC? Coup(B))} {e_h : Hole (DCC? Coup(B)) lv (DCC? ⟦_B⟧(x, y))}
    {hrt : ViewAppHole f (DCC? ⟦_B⟧(x, y)) lv hlt e_h.max_hole} :
    (heq : hrt.reduction.fst = y) → ReadbackHead f h_dom e_h hlt hrt (DCC? Snd(B))
  | quot  {h_dom : Domain f A} {e_h : Hole A lv x}
    {hrt : ViewAppHole f x lv hlt e_h.max_hole} :
    (heq : hrt = .quot (x' := x') hred hgt)
    → ReadbackHead f h_dom e_h hlt hrt (DCC? `(A, x'))
  | fmap  {h_dom : Domain f (DCC? !(A))} {e_h : Hole (DCC? !(A)) lv (DCC? &(x))}
    {hrt : ViewAppHole f (DCC? &(x)) lv hlt e_h.max_hole} :
    (heq : hrt.reduction.fst = (DCC? &((g x))))
    → ReadbackHead f h_dom e_h hlt hrt (DCC? $<g>)
  | map   {h_dom : Domain f (DCC? !(A))} {e_h : Hole (DCC? !(A)) lv (DCC? &(x))}
    {hrt : ViewAppHole f (DCC? &(x)) lv hlt e_h.max_hole} :
    (heq : hrt.reduction.fst = (DCC? !((g x))))
    → ReadbackHead f h_dom e_h hlt hrt (DCC? !<g>)
  | unbox {h_dom : Domain f (DCC? !(A))} {e_h : Hole (DCC? !(A)) lv (DCC? &(x))}
    {hrt : ViewAppHole f (DCC? &(x)) lv hlt e_h.max_hole} :
    (heq : hrt.reduction.fst = x)
    → ReadbackHead f h_dom e_h hlt hrt (DCC? *(A))
  | pair  {h_dom : Domain f (DCC? !(A))} {e_h : Hole (DCC? !(A)) lv (DCC? &(x))}
    {hrt : ViewAppHole f (DCC? &(x)) lv hlt e_h.max_hole} :
    (heq : hrt.reduction.fst = (DCC? ⟦(B x)⟧((M x), (N x (M x))))) -- Coup holes will not contain any apps. Prove this to elim
    → ReadbackHead f h_dom e_h hlt hrt (DCC? ⟦B⟧⟨M, N⟩)
  | eql   {h_dom : Domain f (DCC? !(A))} {e_h : Hole (DCC? !(A)) lv (DCC? &(x))}
    {hrt : ViewAppHole f (DCC? &(x)) lv hlt e_h.max_hole} :
    (heq : hrt.reduction.fst = (DCC? x = x))
    → ReadbackHead f h_dom e_h hlt hrt (DCC? (Eql(`(⊤, A)) &(∗)))
  | sigma {h_dom : Domain f A} {e_h : Hole A lv x}
    {hrt     : ViewAppHole f x lv hlt e_h.max_hole} :
    (heq     : hrt.reduction.fst = (DCC? Coup((g x))))
    → (h_dom_g : Domain (DCC? (g x)) τ_fst)
    → ReadbackHead f h_dom e_h hlt hrt (DCC? (Σ(`(⊤, τ_fst), `(⊤, g)) ∗))

/-
What are the possible par cases, assuming that h is a well-typed hole at Domain A?

- Show that curries are the only possible par cases are where B is Λ(..., ..., ...) hole
- Show that for all g where Domain g A and g does not contain the hole, then there is a ReadbackHead
-/

def RedSpineStar.no_self_app (h : RedSpineStar x (DCC? (f x))) : False :=
  match h.cases_head with
  | .inl ⟨h⟩ => nomatch h
  | .inr h => by
    have h_dec := h.decreasing
    grind

def RedSpineNorm.par_is_some_curr₁
  (h_dom  : Domain f A)
  (h_pure : A.ViewBangCoup → False)
  (hmem   : lv ≤ max_hole x)
  (hlt    : f.max_hole < lv)
  (hrt    : RedSpineNorm (DCC? (f x)) (DCC? (g x))) : Σ' A B g', g = (DCC? Λ(A, B, g')) := by
  match heq : hrt.head with
  | ⟨e', hr, hn⟩ =>
    cases hn
    case fstc =>
      cases h_dom.unique Domain.fst
      exact (h_pure (by constructor)).elim
    case sndc =>
      cases h_dom.unique Domain.snd
      exact (h_pure (by constructor)).elim
    case eval =>
      cases h_dom.unique Domain.eval
      exact (h_pure (by constructor)).elim
    case eql =>
      cases h_dom.unique Domain.eql₁
      exact (h_pure (by constructor)).elim
    case map =>
      cases h_dom.unique Domain.map
      exact (h_pure (by constructor)).elim
    case fmap =>
      cases h_dom.unique Domain.fmap
      exact (h_pure (by constructor)).elim
    case unbox =>
      cases h_dom.unique Domain.unbox
      exact (h_pure (by constructor)).elim
    case pair =>
      cases h_dom.unique Domain.pair
      exact (h_pure (by constructor)).elim
    case curr' =>
      cases h_dom.unique Domain.curr'₁
      exact (h_pure (by constructor)).elim
    case id =>
      cases h_dom.unique Domain.id
      have h := heq ▸ hrt.head_rest
      simp at h
      exact h.no_self_app.elim
    case quot =>
      cases h_dom.unique Domain.quot
      have h := heq ▸ hrt.head_rest
      simp at h
      have h₁ := h.max_hole_preserved
      grind
    case curr =>
      cases h_dom.unique Domain.curr₁
      have h := heq ▸ hrt.head_rest
      simp at h
      match h.cases_head with
      | .inl ⟨h⟩ => cases h
      | .inr h =>
        have h' := par_is_some_curr₁ (by sorry) (by sorry) (by sorry) (by sorry) ⟨h, by sorry⟩
        sorry
    case sigma =>
      sorry
    case comp =>
      sorry

def ViewAppHole.readback_head?₁ {f : GenericExpr τ_c} (h_dom : Domain f A)
  (e_h : Hole A lv x) (hlt : f.max_hole < lv)
  (hrt : ViewAppHole f x lv hlt e_h.max_hole) : Option (Σ' f', ReadbackHead f h_dom e_h hlt hrt f') :=
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
      | DCC? !(A) =>
        match x with
        | DCC? &(x) =>
          if heq₂ : hrt.reduction.fst = x then
            .some ⟨_, .unbox heq₂⟩
          else match heq₂ : hrt.reduction.fst with
          | (DCC? !((g x'))) =>
            if heq₃ : x' = x then by
              subst heq₃
              exact .some ⟨_, .map heq₂⟩
            else .none
          | (DCC? &((g x'))) =>
            if heq₃ : x' = x then by
              subst heq₃
              exact .some ⟨_, .fmap heq₂⟩
            else .none
          | (DCC? ⟦(B x'₁)⟧((M₁ x'₂), (N₁ x'₃ (M₂ x'₄)))) =>
            if heq₃ : (DCC? ⟦(B x)⟧((M₁ x), (N₁ x (M₁ x)))) = (DCC? ⟦(B x'₁)⟧((M₁ x'₂), (N₁ x'₃ (M₂ x'₄)))) then
              .some ⟨_, .pair (heq₃ ▸ heq₂)⟩
            else .none
          | (DCC? y = z) =>
            if heq₃ : (DCC? x = x) = (DCC? y = z) then
              .some ⟨_, .eql (heq₃ ▸ heq₂)⟩
            else .none
          | _ => .none
        | _ => .none
      | _ => .none

def ViewAppHole.readback_head? {f : GenericExpr τ_c} (h_dom : Domain f A)
  (e_h : Hole A lv x) (hlt : f.max_hole < lv)
  (hrt : ViewAppHole f x lv hlt e_h.max_hole) : Option (Σ' f', ReadbackHead f h_dom e_h hlt hrt f') :=
  match heq : hrt.reduction with
  | ⟨DCC? Coup((g x')), h⟩ =>
    if heq₂ : x = x' then
      .some ⟨_, .sigma (heq₂ ▸ (Sigma.ext_iff.mp heq).left) (DCC? (g x)).domain.snd⟩
    else
      hrt.readback_head?₁ (by assumption)
  | _ => hrt.readback_head?₁ (by assumption)

@[aesop unsafe 50% forward (rule_sets := [DccForceReduce])]
def ReadbackHead.complete₁ {f : GenericExpr τ_c}
  {h_dom : Domain f A}
  {e_h   : Hole A lv x}
  {hlt   : f.max_hole < lv}
  {hrt   : ViewAppHole f x lv hlt e_h.max_hole}
  (h     : ReadbackHead (τ_c := τ_c) f h_dom e_h hlt hrt f')
  (hneq  : ∀ {g}, hrt.reduction.fst ≠ (DCC? Coup((g x)))) : hrt.readback_head?₁ h_dom e_h = .some ⟨f', h⟩ := by
  induction heq₀ : h
  case sigma => grind
  case id =>
    unfold ViewAppHole.readback_head?₁
    split
    case h_1 heq =>
      simp [ViewAppHole.reduction] at heq
      grind
    · aesop
  case fst =>
    unfold ViewAppHole.readback_head?₁
    expose_names
    split
    case h_1 hrt' hn' =>
      have h := ViewAppHole.quot_nmem (ViewAppHole.quot hrt' hn') hrt' (by rfl) (A := B.coup) (e_h := e_h_1) (hlt := hlt_1)
      have heq₁ := hrt'.complete
      simp [ViewAppHole.reduction] at heq
      cases heq
      cases heq₀
      grind
    case h_2 =>
      simp [heq]
      intro h
      cases h
  case snd =>
    unfold ViewAppHole.readback_head?₁
    expose_names
    split
    case h_1 hrt' hn' =>
      have h := ViewAppHole.quot_nmem (ViewAppHole.quot hrt' hn') hrt' (by rfl) (A := B.coup) (e_h := e_h_1) (hlt := hlt_1)
      have heq₁ := hrt'.complete
      simp [ViewAppHole.reduction] at heq
      cases heq
      cases heq₀
      grind
    case h_2 =>
      have hneq : y ≠ _B.mkc x_1 y := fun h => nomatch h
      simp [heq, hneq]
      exact e_h_1.coup_points_neq.symm
  case quot =>
    unfold ViewAppHole.readback_head?₁
    expose_names
    subst heq
    simp
  case fmap | map | eql | pair =>
    unfold ViewAppHole.readback_head?₁
    expose_names
    cases heq₀.symm
    split
    case h_1 hrt' hn' =>
      have heq' := hrt'.complete
      simp [ViewAppHole.reduction] at heq
      grind
    case h_2 hrt' xn =>
      simp [heq]
      try (have hneq : g.app x_1 ≠ x_1 := fun h => nomatch h)
      try (simp [hneq])
      try (have hneq : (g.app x_1).box ≠ x_1 := fun h => nomatch h)
      try (simp [hneq])
      try (have hneq : (g.app x_1).bang ≠ x_1 := fun h => nomatch h)
      try (simp [hneq])
      try (have hneq : (B.app x_1).mkc (M.app x_1) ((N.app x_1).app (M.app x_1)) ≠ x_1 := fun h => nomatch h)
      try (simp [hneq])
      try (have hneq : x_1.eq x_1 ≠ x_1 := fun h => nomatch h)
      try (simp [hneq])
      split
      any_goals (
        first
        | (rename_i heq''; cases heq.symm.trans heq''; try (simp))
        | simp_all)
      try (rename_i hn; exact (hn _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl).elim)
  case unbox =>
    unfold ViewAppHole.readback_head?₁
    expose_names
    cases heq₀.symm
    split
    case h_1 =>
      simp [ViewAppHole.reduction] at heq
      grind
    case h_2 hrt' xn =>
      simp [heq]
      intro h; cases h

@[aesop unsafe 50% forward (rule_sets := [DccForceReduce])]
def ReadbackHead.complete {f : GenericExpr τ_c}
  {h_dom : Domain f A}
  {e_h : Hole A lv x}
  {hlt : f.max_hole < lv}
  {hrt : ViewAppHole f x lv hlt e_h.max_hole}
  (h : ReadbackHead (τ_c := τ_c) f h_dom e_h hlt hrt f') : hrt.readback_head? h_dom e_h = .some ⟨f', h⟩ := by
  unfold ViewAppHole.readback_head?
  split
  case h_1 =>
    split
    case isTrue heq_x =>
      cases heq_x
      expose_names
      cases h
      any_goals (grind)
      case quot heq' =>
        cases heq'
        have ⟨ha, hb⟩ := Sigma.ext_iff.mp heq
        simp_all [ViewAppHole.reduction]
        cases ha; cases hb
        have h := h_1.max_hole_preserved
        grind
      case sigma h_dom' heq' =>
        have heq₁ := h_dom'.complete_fst
        have heq₂ := h_dom'.complete_snd'
        cases heq₁
        cases heq₂
        have h := (Sigma.ext_iff.mp heq).left
        simp at h
        cases h.symm.trans heq'
        rfl
    case isFalse hneq_x =>
      have hneq : ∀ {g}, hrt.reduction.fst ≠ (DCC? Coup((g x))) := by
        intro g heq
        aesop
      exact ReadbackHead.complete₁ (by assumption) (by assumption)
  case h_2 hn =>
    have hneq : ∀ {g}, hrt.reduction.fst ≠ (DCC? Coup((g x))) := by
      intro g heq
      exact hn _ _ (heq ▸ hrt.reduction.snd) (by grind)
    exact ReadbackHead.complete₁ (by assumption) (by assumption)

def ReadbackHead.ext (hr₁ : RedSpineNorm (DCC? (f x)) B)
  (hr₂    : RedSpineNorm (DCC? (g x)) B)
  (h_dom₁ : Domain f A)
  (h_dom₂ : Domain g A)
  (e_h    : Hole A lv x)
  (hlt₁   : f.max_hole < lv)
  (hlt₂   : g.max_hole < lv)
  (hrt₁   : f.ViewAppHole x lv hlt₁ e_h.max_hole)
  (hrt₂   : g.ViewAppHole x lv hlt₂ e_h.max_hole)
  (hrb₁   : ReadbackHead f h_dom₁ e_h hlt₁ hrt₁ f')
  (hrb₂   : ReadbackHead g h_dom₂ e_h hlt₂ hrt₂ g') : f' = g' := by
  let hr₃  := hrt₁.reduction.snd
  let hr₄  := hrt₂.reduction.snd
  cases hrb₁ with
  | sigma heq₁ =>
    cases hrb₂ with
    | sigma heq₂ =>
      expose_names
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      cases heqa
      cases heqb
      cases heq'
      cases h_dom_g.unique h_dom_g_1
      rfl
    | pair heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      grind
    | fst heq₂ | snd heq₂ | quot heq₂ | eql heq₂ | unbox heq₂ | fmap heq₂ | map heq₂ | id heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      try (simp [ViewAppHole.reduction] at heq')
      try (cases heq')
      try (grind)
  | pair heq₁ =>
    cases hrb₂ with
    | sigma heq₂ | pair heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      grind
    | quot heq₂ | eql heq₂ | unbox heq₂ | fmap heq₂ | map heq₂ | id heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      try (simp [ViewAppHole.reduction] at heq')
      try (cases heq')
      try (grind)
  | unbox heq₁ =>
    cases hrb₂ with
    | unbox heq₂ => rfl
    | sigma heq₂ | quot heq₂ | eql heq₂ | pair heq₂ | fmap heq₂ | map heq₂ | id heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      try (simp [ViewAppHole.reduction] at heq')
      try (cases heq')
      try (grind)
  | eql heq₁ =>
    cases hrb₂ with
    | eql heq₂ => rfl
    | sigma heq₂ | unbox heq₂ | pair heq₂ | fmap heq₂ | map heq₂ | quot heq₂ | id heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      cases heq'
      try (grind)
  | map heq₁ =>
    cases hrb₂ with
    | map heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      simp at heq'
      simp [heq']
    | sigma heq₂ | fmap heq₂ | pair heq₂ | eql heq₂ =>
      let heqa  := (heq₁ ▸ hr₃).unique hr₁
      let heqb  := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      grind
    | id heq₂ =>
      let heqa  := (heq₁ ▸ hr₃).unique hr₁
      let heqb  := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      cases heq'
    | quot heq₂ =>
      let heqa  := (heq₁ ▸ hr₃).unique hr₁
      let heqb  := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      simp [ViewAppHole.reduction] at heq'
      cases heq'
      grind
    | unbox heq₂ =>
      let heqa  := (heq₁ ▸ hr₃).unique hr₁
      let heqb  := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      cases heq'
  | fmap heq₁ =>
    cases hrb₂ with
    | fmap heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      simp at heq'
      simp [heq']
    | sigma heq₂ | map heq₂ | pair heq₂ | eql heq₂ =>
      let heqa  := (heq₁ ▸ hr₃).unique hr₁
      let heqb  := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      grind
    | id heq₂ =>
      let heqa  := (heq₁ ▸ hr₃).unique hr₁
      let heqb  := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      cases heq'
    | quot heq₂ =>
      let heqa  := (heq₁ ▸ hr₃).unique hr₁
      let heqb  := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      simp [ViewAppHole.reduction] at heq'
      cases heq'
      grind
    | unbox heq₂ =>
      let heqa  := (heq₁ ▸ hr₃).unique hr₁
      let heqb  := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      cases heq'
  | snd heq₁ =>
    cases hrb₂ with
    | sigma heq₂ =>
      let heqa  := (heq₁ ▸ hr₃).unique hr₁
      let heqb  := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      grind
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
    | sigma heq₂ =>
      let heqa  := (heq₁ ▸ hr₃).unique hr₁
      let heqb  := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      grind
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
    | sigma heq' | pair heq' | eql heq' | unbox heq' | fmap heq' | map heq' | snd heq' | fst heq' =>
      expose_names
      have ha := hr₁.max_hole_preserved
      have hb := hr₂.max_hole_preserved
      have hc := e_h.max_hole
      have hd := e_h.min_hole
      let h := heq ▸ hrt₁.reduction.snd
      cases h.unique hr₁
      let h' := heq' ▸ hrt₂.reduction.snd
      cases h'.unique hr₂
  | quot heq₁ =>
    cases hrb₂ with
    | sigma heq₂ | pair heq₂ | unbox heq₂ | eql heq₂ | map heq₂ | fmap heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      try (simp [ViewAppHole.reduction] at heq')
      try (cases heq')
      try (grind)
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

/-
inductive ReadbackMulti :
  (f : GenericExpr τ_c)
  → (h_dom : Domain f A)
  → (e_h : Hole A lv x)
  → (hlt : f.max_hole < lv)
  → (hrt : ViewAppHole f x lv hlt e_h.max_hole)
  → (f' : GenericExpr τ_c) → Type u
  | single : (ReadbackHead f h_dom e_h hlt hrt f') → ReadbackMulti f h_dom e_h hlt hrt f'
  | par    : (∀ {f'}, ReadbackHead f h_dom e_h hlt hrt f' → False)
    → (hrt.reduction.fst = (DCC? (

Domain preservation is quite important. Otherwise, we can't say the reduction length argument,
I think.

Do we need reduction length 1?
We can show ext for ReadbackMulti pretty easily.

Does par condense curry uncurry?

Λ(Eval(x)) y (z)

Concrete example:

Λ(
-/
