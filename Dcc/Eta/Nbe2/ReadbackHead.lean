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
  | comp  {h_dom : Domain f A} {e_h : Hole A lv x}
    {hrt     : ViewAppHole f x lv hlt e_h.max_hole} :
    (heq     : hrt.reduction.fst = (DCC? (g (h x))))
    → ReadbackHead f h_dom e_h hlt hrt (DCC? g ∘ h)
  | par   {h_dom : Domain f A} {e_h : Hole A lv x}
    {hrt     : ViewAppHole f x lv hlt e_h.max_hole} :
    (heq     : hrt.reduction.fst = (DCC? (g x))) → ReadbackHead f h_dom e_h hlt hrt g
  | curr  {h_dom : Domain f A} {e_h : Hole A lv x}
    {hrt     : ViewAppHole f x lv hlt e_h.max_hole} :
    (heq     : hrt.reduction.fst = (DCC? (g ⟦B⟧(y, x)))) → ReadbackHead f h_dom e_h hlt hrt (DCC? (Λ(Dom(Uncoup(Dom(g))), Uncoup(Dom(g)), g) y))
  | curr' {h_dom : Domain f (DCC? !(A))} {e_h : Hole (DCC? !(A)) lv (DCC? &(x))}
    {hrt     : ViewAppHole f (DCC? &(x)) lv hlt e_h.max_hole} :
    (heq     : hrt.reduction.fst = (DCC? (g &(⟦B⟧(y, x))))) → ReadbackHead f h_dom e_h hlt hrt (DCC? (!Λ(Dom(Uncoup(Unbang(Dom(g)))), Uncoup(Unbang(Dom(g))), g) &(y)))
  | eval  {h_dom : Domain f (DCC? Coup(B))} {e_h : Hole (DCC? Coup(B)) lv (DCC? ⟦_B⟧(x, y))}
    {hrt : ViewAppHole f (DCC? ⟦_B⟧(x, y)) lv hlt e_h.max_hole} :
    (h_dom_B     : Domain B τ)
    → (heq       : hrt.reduction.fst = (DCC? (g x y)))
    → ReadbackHead f h_dom e_h hlt hrt (DCC? (Eval(τ, B, g)))
-- TODO: ^ above curr' breaks preservation mildly will need to hook into Judge. should do this with Uncoup and match g domain

/-
  | curr  {h_dom : Domain f A} {e_h : Hole A lv x}
    {hrt     : ViewAppHole f x lv hlt e_h.max_hole} :
    (h_dom_B : Domain B A)
    → (heq     : hrt.reduction.fst = (DCC? g ⟦B⟧(y, x))) → ReadbackHead f h_dom e_h hlt hrt (DCC? (Λ(A, B, g) y))
  | curr' {h_dom : Domain f (DCC? !(A))} {e_h : Hole (DCC? !(A)) lv (DCC? &(x))}
    {hrt     : ViewAppHole f (DCC? &(x)) lv hlt e_h.max_hole} :
    (h_dom_B : Domain B A)
    → (heq       : hrt.reduction.fst = (DCC? g &(⟦B⟧(y, x)))) → ReadbackHead f h_dom e_h hlt hrt (DCC? (!Λ(A, B, g) &(y)))
  | eval  {h_dom : Domain f (DCC? Coup(B))} {e_h : Hole (DCC? Coup(B)) lv (DCC? ⟦_B⟧(x, y))}
    {hrt : ViewAppHole f (DCC? ⟦_B⟧(x, y)) lv hlt e_h.max_hole} :
    (h_dom_B     : Domain B τ)
    → (heq       : hrt.reduction.fst = (DCC? (g x y)))
    → ReadbackHead f h_dom e_h hlt hrt (DCC? (Eval(τ, B, g)))
-/

/-
What are the possible par cases, assuming that h is a well-typed hole at Domain A?

- Show that curries are the only possible par cases are where B is Λ(..., ..., ...) hole
  - And composition
- Show that for all g where Domain g A and g does not contain the hole, then there is a ReadbackHead
-/

def RedSpineStar.no_self_app (h : RedSpineStar x (DCC? (f x))) : False :=
  match h.cases_head with
  | .inl ⟨h⟩ => nomatch h
  | .inr h => by
    have h_dec := h.decreasing
    grind

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

def ViewAppHole.readback_head_curr? {f : GenericExpr τ_c} (h_dom : Domain f A)
  (e_h : Hole A lv x) (hlt : f.max_hole < lv)
  (hrt : ViewAppHole f x lv hlt e_h.max_hole) : Option (Σ' f', ReadbackHead f h_dom e_h hlt hrt f') :=
  match hrt.reduction with
  | ⟨DCC? (g ⟦B⟧(y, x')), h⟩ =>
    if heq₂ : x = x' then
      have heq' : hrt.reduction.fst = (DCC? (g ⟦B⟧(y, x))) := by
        have h₁ := h.complete
        let h₂ := hrt.reduction.snd.complete
        grind
      .some ⟨DCC? (Λ(Dom(Uncoup(Dom(g))), Uncoup(Dom(g)), g) y), .curr heq'⟩
    else .none
  | _ => .none

def readback_head_curr_none {f : GenericExpr τ_c} (h_dom : Domain f A)
  (e_h : Hole A lv x) (hlt : f.max_hole < lv)
  (hrt : ViewAppHole f x lv hlt e_h.max_hole)
  (heq : hrt.readback_head_curr? h_dom e_h hlt = .none) : ∀ ⦃g B y⦄, hrt.reduction.fst ≠ (DCC? (g ⟦B⟧(y, x))) := by
  intro g B y heq'
  simp [ViewAppHole.readback_head_curr?] at heq
  have heq_whole' : hrt.reduction = (Sigma.mk (g.app (B.mkc y x)) (heq' ▸ hrt.reduction.snd)) := by
    grind
  simp [heq_whole'] at heq

def readback_head_curr_some {f : GenericExpr τ_c} (h_dom : Domain f A)
  (e_h : Hole A lv x) (hlt : f.max_hole < lv)
  (hrt : ViewAppHole f x lv hlt e_h.max_hole)
  {h : ReadbackHead f h_dom e_h hlt hrt f'}
  (heq : hrt.readback_head_curr? h_dom e_h hlt = .some ⟨f', h⟩) : Σ' g B y, hrt.reduction.fst = (DCC? (g ⟦B⟧(y, x))) := by
  simp [ViewAppHole.readback_head_curr?] at heq
  split at heq
  case h_1 heq_hrt =>
    split at heq
    case isTrue heq_x =>
      cases heq_x
      exact ⟨_, _, _, (Sigma.ext_iff.mp heq_hrt).left⟩
    · grind
  · grind

def ViewAppHole.readback_head_curr'? {f : GenericExpr τ_c} (h_dom : Domain f A)
  (e_h : Hole A lv x) (hlt : f.max_hole < lv)
  (hrt : ViewAppHole f x lv hlt e_h.max_hole) : Option (Σ' f', ReadbackHead f h_dom e_h hlt hrt f') :=
  match hrt.reduction with
  | ⟨DCC? (g &(⟦B⟧(y, x'))), h⟩ =>
    match x with
    | DCC? &(x) =>
      match A with
      | DCC? !(A) =>
        if heq₂ : x = x' then
          have heq' : hrt.reduction.fst = (DCC? (g &(⟦B⟧(y, x)))) := by
            have h₁ := h.complete
            let h₂ := hrt.reduction.snd.complete
            grind
          .some ⟨_, .curr' heq'⟩
        else .none
      | _ => .none
    | _ => .none
  | _ => .none

def readback_head_curr'_none {f : GenericExpr τ_c} (h_dom : Domain f A)
  (e_h : Hole A lv x) (hlt : f.max_hole < lv)
  (hrt : ViewAppHole f x lv hlt e_h.max_hole)
  (heq : hrt.readback_head_curr'? h_dom e_h hlt = .none) : ∀ ⦃A₀ x₀ g B y⦄, (A = (DCC? !(A₀))) → (x = (DCC? &(x₀))) → hrt.reduction.fst ≠ (DCC? (g &(⟦B⟧(y, x₀)))) := by
  intro A₀ x₀ g B y heq₁ heq₂ heq₃
  simp [ViewAppHole.readback_head_curr'?] at heq
  cases heq₁
  cases heq₂
  have heq_whole' : hrt.reduction = (Sigma.mk (g.app (B.mkc y x₀).box) (heq₃ ▸ hrt.reduction.snd)) := by
    grind
  simp [heq_whole'] at heq

def readback_head_curr'_some {f : GenericExpr τ_c} (h_dom : Domain f A)
  (e_h : Hole A lv x) (hlt : f.max_hole < lv)
  (hrt : ViewAppHole f x lv hlt e_h.max_hole)
  {h : ReadbackHead f h_dom e_h hlt hrt f'}
  (heq : hrt.readback_head_curr'? h_dom e_h hlt = .some ⟨f', h⟩) : Σ' A₀ x₀ g B y, (PLift (A = (DCC? !(A₀)))) × (PLift (x = (DCC? &(x₀)))) × (PLift (hrt.reduction.fst = (DCC? (g &(⟦B⟧(y, x₀)))))) := by
  simp [ViewAppHole.readback_head_curr'?] at heq
  split at heq
  case h_1 heq_hrt =>
    split at heq
    case h_1 =>
      split at heq
      case h_1 =>
        split at heq
        case isTrue heq_x =>
          cases heq_x
          expose_names
          exact ⟨A_1, x', g, B, y, ⟨rfl⟩, ⟨rfl⟩, ⟨(Sigma.ext_iff.mp heq_hrt).left⟩⟩
        · grind
      · grind
    · grind
  · grind

def ViewAppHole.readback_eval? {f : GenericExpr τ_c} (h_dom : Domain f A)
  (e_h : Hole A lv x) (hlt : f.max_hole < lv)
  (hrt : ViewAppHole f x lv hlt e_h.max_hole) : Option (Σ' f', ReadbackHead f h_dom e_h hlt hrt f') :=
  match A with
  | DCC? Coup(B) =>
    match x with
    | (DCC? ⟦_B⟧(x, y)) =>
      match hrt.reduction with
      | ⟨DCC? (g x' y'), h⟩ =>
        if heq : (DCC? (g x y)) = (DCC? (g x' y')) then
          have heq' : hrt.reduction.fst = (DCC? (g x y)) := by
            have h₁ := h.complete
            let h₂ := hrt.reduction.snd.complete
            grind
          .some ⟨_, .eval B.domain.snd heq'⟩
        else .none
      | _ => .none
    | _ => .none
  | _ => .none

def readback_head_eval_none {f : GenericExpr τ_c} (h_dom : Domain f A)
  (e_h : Hole A lv x) (hlt : f.max_hole < lv)
  (hrt : ViewAppHole f x lv hlt e_h.max_hole)
  (heq : hrt.readback_eval? h_dom e_h hlt = .none) : ∀ ⦃B _B a b g⦄, (A = DCC? Coup(B)) → (x = (DCC? ⟦_B⟧(a, b))) → hrt.reduction.fst ≠ (DCC? (g a b)) := by
  intro B _B a b g heq₁ heq₂ heq₃
  have heq_whole' : hrt.reduction = (Sigma.mk ((g.app a).app b) (heq₃ ▸ hrt.reduction.snd)) := by
    grind
  simp [ViewAppHole.readback_eval?] at heq
  aesop

def readback_head_eval_some {f : GenericExpr τ_c} (h_dom : Domain f A)
  (e_h : Hole A lv x) (hlt : f.max_hole < lv)
  (hrt : ViewAppHole f x lv hlt e_h.max_hole)
  {h : ReadbackHead f h_dom e_h hlt hrt f'}
  (heq : hrt.readback_eval? h_dom e_h hlt = .some ⟨f', h⟩) : Σ' B _B a b g, (PLift (A = DCC? Coup(B))) × (PLift (x = (DCC? ⟦_B⟧(a, b)))) × (PLift (hrt.reduction.fst = (DCC? (g a b)))) := by
  simp [ViewAppHole.readback_eval?] at heq
  split at heq
  case h_1 =>
    split at heq
    case h_1 =>
      split at heq
      case h_1 =>
        split at heq
        case isTrue =>
          expose_names
          cases h_2.left; cases h_2.right
          exact ⟨_, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, ⟨(Sigma.ext_iff.mp heq_1).left⟩⟩
        · grind
      · grind
    · grind
  · grind

def ViewAppHole.readback_head?₂ {f : GenericExpr τ_c} (h_dom : Domain f A)
  (e_h : Hole A lv x) (hlt : f.max_hole < lv)
  (hrt : ViewAppHole f x lv hlt e_h.max_hole) : Option (Σ' f', ReadbackHead f h_dom e_h hlt hrt f') :=
  match hrt.reduction with
  | ⟨DCC? (f' (g x')), h⟩ =>
    if heq₂ : (DCC? (f' (g x))) = DCC? (f' (g x')) then
      .some ⟨DCC? f' ∘ g, .comp (by
        have h₁ := h.complete
        let h₂ := hrt.reduction.snd.complete
        grind)⟩
    else .none
  | ⟨DCC? (f' x'), h⟩ =>
    if heq₂ : (DCC? (f' x)) = (DCC? (f' x')) then
      .some ⟨f', .par (by
        have h₁ := h.complete
        let h₂ := hrt.reduction.snd.complete
        grind)⟩
    else
      .none
  | ⟨DCC? Coup((g x')), h⟩ =>
    if heq₂ : x = x' then
      have heq' : hrt.reduction.fst = (DCC? Coup((g x))) := by
        have h₁ := h.complete
        let h₂ := hrt.reduction.snd.complete
        grind
      .some ⟨_, .sigma heq' (DCC? (g x)).domain.snd⟩
    else .none
  | _ => .none

def ViewAppHole.readback_head? {f : GenericExpr τ_c} (h_dom : Domain f A)
  (e_h : Hole A lv x) (hlt : f.max_hole < lv)
  (hrt : ViewAppHole f x lv hlt e_h.max_hole) : Option (Σ' f', ReadbackHead f h_dom e_h hlt hrt f') :=
  match hrt.readback_eval? h_dom e_h hlt with
  | .some ⟨_, h⟩ => .some ⟨_, h⟩
  | .none =>
    match hrt.readback_head_curr? h_dom e_h hlt with
    | .some ⟨_, h⟩ => .some ⟨_, h⟩
    | .none =>
      match hrt.readback_head_curr'? h_dom e_h hlt with
      | .some ⟨_, h⟩ => .some ⟨_, h⟩
      | .none =>
        match hrt.readback_head?₂ h_dom e_h hlt with
        | .some ⟨_, h⟩ => .some ⟨_, h⟩
        | .none =>
          match hrt.readback_head?₁ h_dom e_h hlt with
          | .some ⟨_, h⟩ => .some ⟨_, h⟩
          | .none => .none

def ReadbackHead.complete₂ {f : GenericExpr τ_c}
  {h_dom : Domain f A}
  {e_h   : Hole A lv x}
  {hlt   : f.max_hole < lv}
  {hrt   : ViewAppHole f x lv hlt e_h.max_hole}
  (h     : ReadbackHead (τ_c := τ_c) f h_dom e_h hlt hrt f')
  (heq   : Σ g f', (PLift (hrt.reduction.fst = (DCC? Coup((g x)))))
    ⊕ (PLift (hrt.reduction.fst = (DCC? (g x))))
    ⊕ (PLift (hrt.reduction.fst = (DCC? (g (f' x)))))) : hrt.readback_head?₂ h_dom e_h = .some ⟨f', h⟩ := by
  match heq with
  | ⟨_, _, .inl ⟨heq₀⟩⟩ =>
    unfold ViewAppHole.readback_head?₂
    split
    any_goals (grind)
    case h_3 heq' =>
      cases (Sigma.ext_iff.mp heq').left.symm.trans heq₀
      simp
      cases h
      any_goals (grind)
      case quot heq' =>
        cases heq'
        simp [ViewAppHole.reduction] at heq₀
        cases heq₀
        simp [ViewAppHole.reduction] at heq'
        cases heq'
        have h₁ := e_h.max_hole
        have h₂ := e_h.min_hole
        grind
      case sigma heq' =>
        expose_names
        cases (Sigma.ext_iff.mp heq'_1).left.symm.trans heq'
        have h := h_dom_g.complete
        grind
    case h_4 hn₁ hn₂ hn₃ =>
      exact (hn₃ _ _ (heq₀ ▸ hrt.reduction.snd) (by grind)).elim
  | ⟨_, _, .inr (.inl ⟨h⟩)⟩ =>
    unfold ViewAppHole.readback_head?₂
    split
    case h_1 heq' =>
      have h := (Sigma.ext_iff.mp heq').left.symm.trans h
      simp only at h
      cases h
      simp
      expose_names
      cases h_1
      any_goals (grind)
      case id heq₂ => cases heq₂.symm.trans h
      case quot heq₂ =>
        cases heq₂
        simp [ViewAppHole.reduction] at h
        cases h
        have h₁ := e_h.max_hole
        have h₂ := e_h.min_hole
        grind
      case par heq₂ =>
        cases heq₂.symm.trans h
        exact (e_h.no_app rfl).elim
    case h_2 heq' =>
      cases (Sigma.ext_iff.mp heq').left.symm.trans h
      simp
      expose_names
      cases h_1
      case id heq'' | fst heq'' | snd heq'' | fmap heq'' | map heq'' | unbox heq'' | pair heq'' | eql heq'' | sigma heq'' | comp heq'' | curr heq'' | curr' heq'' | eval heq'' =>
        cases (Sigma.ext_iff.mp heq').left.symm.trans heq''
      case quot heq_hrt =>
        cases heq_hrt
        simp [ViewAppHole.reduction] at h
        cases h
        simp [ViewAppHole.reduction] at heq'
        cases heq'
        have h₁ := e_h.max_hole
        have h₂ := e_h.min_hole
        grind
      case par heq'' =>
        cases (Sigma.ext_iff.mp heq').left.symm.trans heq''
        grind
    case h_3 heq' => cases (Sigma.ext_iff.mp heq').left.symm.trans h
    case h_4 hn₁ hn₂ hn₃ => exact (hn₂ _ _ (h ▸ hrt.reduction.snd) (by grind)).elim
  | ⟨_, _, .inr (.inr ⟨h⟩)⟩ =>
    unfold ViewAppHole.readback_head?₂
    expose_names
    have heq_whole' : hrt.reduction = (Sigma.mk (fst.app (fst_1.app x)) (h ▸ hrt.reduction.snd)) := by
      grind
    simp only [heq_whole']
    cases h_1
    case id heq' | fst heq' | snd heq' | fmap heq' | map heq' | unbox heq' | pair heq' | eql heq' | sigma heq' | curr heq' | par heq' | comp heq' | curr' heq' | eval heq' =>
      cases heq'.symm.trans h
      try (simp)
    case quot heq' =>
      have h₁ := e_h.max_hole
      have h₂ := e_h.min_hole
      cases heq'
      simp [ViewAppHole.reduction] at h
      grind

@[aesop unsafe 50% forward (rule_sets := [DccForceReduce])]
def ReadbackHead.complete₁ {f : GenericExpr τ_c}
  {h_dom : Domain f A}
  {e_h   : Hole A lv x}
  {hlt   : f.max_hole < lv}
  {hrt   : ViewAppHole f x lv hlt e_h.max_hole}
  (h     : ReadbackHead (τ_c := τ_c) f h_dom e_h hlt hrt f')
  (hneq  : ∀ {g}, hrt.reduction.fst ≠ (DCC? Coup((g x))))
  (hneq₂ : ∀ {g}, hrt.reduction.fst ≠ (DCC? (g x)))
  (hneq₃ : ∀ {a b}, hrt.reduction.fst ≠ (DCC? (a (b x))))
  (hneq₄ : ∀ {g B y}, hrt.reduction.fst ≠ (DCC? (g ⟦B⟧(y, x))))
  (hneq₅ : ∀ ⦃A₀ x₀ g B y⦄, (A = (DCC? !(A₀))) → (x = (DCC? &(x₀))) → hrt.reduction.fst ≠ (DCC? (g &(⟦B⟧(y, x₀)))))
  (hneq₆ : ∀ ⦃B _B a b g⦄, (A = (DCC? Coup(B))) → (x = (DCC? ⟦_B⟧(a, b))) → (hrt.reduction.fst ≠ (DCC? (g a b)))): hrt.readback_head?₁ h_dom e_h = .some ⟨f', h⟩ := by
  induction heq₀ : h
  case eval | curr' | curr | sigma | comp | par => grind
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

def readback_head₂_none {f : GenericExpr τ_c}
  {h_dom : Domain f A}
  {e_h : Hole A lv x}
  {hlt : f.max_hole < lv}
  {hrt : ViewAppHole f x lv hlt e_h.max_hole}
  (heq : hrt.readback_head?₂ h_dom e_h hlt = .none) : (PLift (∀ {g}, hrt.reduction.fst ≠ (DCC? Coup((g x)))))
    × (PLift (∀ {g}, hrt.reduction.fst ≠ (DCC? (g x))))
    × (PLift (∀ {a b}, hrt.reduction.fst ≠ (DCC? (a (b x))))) := by
  unfold ViewAppHole.readback_head?₂ at heq
  exact ⟨⟨fun heq' => by grind⟩, ⟨fun heq' => by
    split at heq
    case h_1 =>
      expose_names
      cases (Sigma.ext_iff.mp heq_1).left.symm.trans heq'
      simp at heq
      cases e_h.no_app rfl
    case h_2 => grind
    case h_3 => grind
    case h_4 hn₁ hn₂ hn₃ => exact (hn₂ _ _ (heq' ▸ hrt.reduction.snd) (by grind)).elim⟩, ⟨fun heq' => by grind⟩⟩

def readback_head₂_some {f : GenericExpr τ_c}
  {h_dom : Domain f A}
  {e_h : Hole A lv x}
  {hlt : f.max_hole < lv}
  {hrt : ViewAppHole f x lv hlt e_h.max_hole}
  {b   : ReadbackHead f h_dom e_h hlt hrt a}
  (heq : hrt.readback_head?₂ h_dom e_h hlt = .some ⟨a, b⟩) : (Σ' g, hrt.reduction.fst = (DCC? Coup((g x))))
    ⊕ (Σ' g, hrt.reduction.fst = (DCC? (g x)))
    ⊕ (Σ' g f', (hrt.reduction.fst = (DCC? (g (f' x))))) := by
  unfold ViewAppHole.readback_head?₂ at heq
  split at heq
  case h_1 =>
    expose_names
    exact .inr (.inr ⟨f', g, by grind⟩)
  case h_2 =>
    expose_names
    split at heq
    case isTrue =>
      exact .inr (.inl ⟨f', by grind⟩)
    case isFalse hneq => grind
  case h_3 =>
    expose_names
    exact .inl ⟨g, by grind⟩
  cases heq

@[aesop unsafe 50% forward (rule_sets := [DccForceReduce])]
def ReadbackHead.complete {f : GenericExpr τ_c}
  {h_dom : Domain f A}
  {e_h : Hole A lv x}
  {hlt : f.max_hole < lv}
  {hrt : ViewAppHole f x lv hlt e_h.max_hole}
  (h : ReadbackHead (τ_c := τ_c) f h_dom e_h hlt hrt f') : hrt.readback_head? h_dom e_h = .some ⟨f', h⟩ := by
  unfold ViewAppHole.readback_head?
  split
  case h_1 heq =>
    have ⟨_, _, _, _, _, ⟨h₁⟩, ⟨h₂⟩, ⟨h₃⟩⟩ := readback_head_eval_some h_dom e_h hlt hrt heq
    cases h₁; cases h₂
    have hn₁ := e_h.min_hole
    have hn₂ := e_h.max_hole
    expose_names
    have heq_whole' : hrt.reduction = (Sigma.mk ((fst_5.app fst_3).app fst_4) (h₃ ▸ hrt.reduction.snd)) := by
      grind
    cases h
    case id heq' | fst heq' | snd heq' | sigma heq' | comp heq' | par heq' | curr heq' => cases heq'.symm.trans h₃
    case quot heq' =>
      cases heq'
      simp [ViewAppHole.reduction] at *
      grind
    case eval h_dom_B heq' =>
      have heq_dom := h_dom_B.complete
      have heq_dom₁ := h_dom_B.complete_fst
      have heq_dom₂ := h_dom_B.complete_snd'
      cases heq'.symm.trans h₃
      simp [ViewAppHole.readback_eval?, heq_whole', heq_dom] at heq
      cases heq_dom₁
      cases heq.left
      simp_all [h_dom_B.complete_snd]
  case h_2 heq =>
    have h₁ := readback_head_eval_none h_dom e_h hlt hrt heq
    split
    case h_1 heq =>
      have ⟨g, B, y, heq⟩ := readback_head_curr_some h_dom e_h hlt hrt heq
      have heq_whole' : hrt.reduction = (Sigma.mk (g.app (B.mkc y x)) (heq ▸ hrt.reduction.snd)) := by
        grind
      have hn₁ := e_h.min_hole
      have hn₂ := e_h.max_hole
      expose_names
      cases h
      case eval heq' | curr' heq' | eql heq' | pair heq' | unbox heq' | map heq' | fmap heq'
        | id heq' | fst heq' | snd heq' | sigma heq' | comp heq' | par heq' => cases heq'.symm.trans heq
      case curr heq' =>
        cases heq'.symm.trans heq
        simp [ViewAppHole.readback_head_curr?, heq_whole'] at heq_2
        cases heq_2.left; cases heq_2.right
        rfl
      case quot heq' =>
        cases heq'
        simp [ViewAppHole.reduction] at *
        grind
    case h_2 heq_none =>
      have h₂ := readback_head_curr_none h_dom e_h hlt hrt heq_none
      split
      case h_1 heq =>
        have ⟨A₀, x₀, g, B, y, ⟨heq₁⟩, ⟨heq₂⟩, ⟨heq₃⟩⟩ := readback_head_curr'_some h_dom e_h hlt hrt heq
        cases heq₁
        cases heq₂
        have heq_whole' : hrt.reduction = (Sigma.mk (g.app (B.mkc y x₀).box) (heq₃ ▸ hrt.reduction.snd)) := by
          grind
        have hn₁ := e_h.min_hole
        have hn₂ := e_h.max_hole
        expose_names
        cases h
        case id heq' | unbox heq' | map heq' | fmap heq' | sigma heq' | curr heq' | comp heq' | par heq' | eql heq' | pair heq' =>
          cases heq'.symm.trans heq₃
        case curr' heq' =>
          cases heq'.symm.trans heq₃
          simp [ViewAppHole.readback_head_curr'?, heq_whole'] at heq
          cases heq.left; cases heq.right
          rfl
        case quot heq' =>
          cases heq'
          simp [ViewAppHole.reduction] at *
          grind
      case h_2 heq_none =>
        have h₂ := readback_head_curr'_none h_dom e_h hlt hrt heq_none
        split
        case h_1 heq =>
          have h_some_complete := readback_head₂_some heq
          match h_some_complete with
          | .inl ⟨g, heq'⟩ =>
            have heq'' := h.complete₂ ⟨_, .top, .inl ⟨heq'⟩⟩
            cases heq''.symm.trans heq
            rfl
          | .inr (.inl ⟨g, heq'⟩) =>
            have heq'' := h.complete₂ ⟨_, .top, .inr (.inl ⟨heq'⟩)⟩
            cases heq''.symm.trans heq
            rfl
          | .inr (.inr ⟨g, f', heq'⟩) =>
            have heq'' := h.complete₂ ⟨_, _, .inr (.inr ⟨heq'⟩)⟩
            cases heq''.symm.trans heq
            rfl
        case h_2 heq_none =>
          have ⟨⟨h₁⟩, ⟨h₂⟩, ⟨h₃⟩⟩ := readback_head₂_none heq_none
          have h := h.complete₁ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
          simp [h]

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
  | eval _ heq₁ =>
    cases hrb₂
    case eval h_dom₂ heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      cases heq'
      expose_names
      cases h_dom_B.unique h_dom₂
      rfl
    case quot heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      expose_names
      have heq' := heqa.trans heqb.symm
      cases heq₂
      simp [ViewAppHole.reduction] at heq'
      cases heq'
      have ha := e_h.max_hole
      have hb := e_h.min_hole
      have hc := hr₁.max_hole_preserved
      grind
    any_goals (
      focus
      try (
        case _ heq₂ =>
          let heqa := (heq₁ ▸ hr₃).unique hr₁
          let heqb := (heq₂ ▸ hr₄).unique hr₂
          have heq' := heqa.trans heqb.symm
          cases heq')
      done)
  | curr' heq₁ =>
    cases hrb₂
    case curr' heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      cases heq'
      rfl
    case quot heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      expose_names
      have heq' := heqa.trans heqb.symm
      cases heq₂
      simp [ViewAppHole.reduction] at heq'
      cases heq'
      have ha := e_h.max_hole
      have hb := e_h.min_hole
      have hc := hr₁.max_hole_preserved
      grind
    any_goals (
      focus
      try (
        case _ heq₂ =>
          let heqa := (heq₁ ▸ hr₃).unique hr₁
          let heqb := (heq₂ ▸ hr₄).unique hr₂
          have heq' := heqa.trans heqb.symm
          cases heq')
      done)
  | curr heq₁ =>
    cases hrb₂
    case curr heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      cases heq'
      rfl
    case quot heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      expose_names
      have heq' := heqa.trans heqb.symm
      cases heq₂
      simp [ViewAppHole.reduction] at heq'
      cases heq'
      have ha := e_h.max_hole
      have hb := e_h.min_hole
      have hc := hr₁.max_hole_preserved
      grind
    any_goals (
      focus
      try (
        case _ heq₂ =>
          let heqa := (heq₁ ▸ hr₃).unique hr₁
          let heqb := (heq₂ ▸ hr₄).unique hr₂
          have heq' := heqa.trans heqb.symm
          cases heq'))
  | par heq₁ =>
    cases hrb₂
    case eval heq₂ | curr' heq₂ | curr heq₂ | comp heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      cases heq'
    any_goals (
      focus
      try (
        case _ heq₂ =>
          let heqa := (heq₁ ▸ hr₃).unique hr₁
          let heqb := (heq₂ ▸ hr₄).unique hr₂
          have heq' := heqa.trans heqb.symm
          try (simp [ViewAppHole.reduction] at heq')
          try (cases heq')
          try (grind)))
  | comp heq₁ =>
    cases hrb₂
    case eval heq₂ | par heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      cases heq'
    any_goals (
      focus
      try (
        case _ heq₂ =>
          let heqa := (heq₁ ▸ hr₃).unique hr₁
          let heqb := (heq₂ ▸ hr₄).unique hr₂
          have heq' := heqa.trans heqb.symm
          try (simp [ViewAppHole.reduction] at heq')
          try (cases heq')
          try (grind)))
  | sigma heq₁ =>
    cases hrb₂ with
    | curr' heq₂ | curr heq₂ | eval _ heq₂ | par heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      cases heq'
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
    | comp heq₂ | fst heq₂ | snd heq₂ | quot heq₂ | eql heq₂ | unbox heq₂ | fmap heq₂ | map heq₂ | id heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      try (simp [ViewAppHole.reduction] at heq')
      try (cases heq')
      try (grind)
  | pair heq₁ =>
    cases hrb₂ with
    | curr' heq₂ | curr heq₂ | par heq₂ | comp heq₂ | sigma heq₂ | pair heq₂ =>
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
    | curr heq₂ | curr' heq₂ | par heq₂ | comp heq₂ | sigma heq₂ | quot heq₂ | eql heq₂ | pair heq₂ | fmap heq₂ | map heq₂ | id heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      try (simp [ViewAppHole.reduction] at heq')
      try (cases heq')
      try (grind)
  | eql heq₁ =>
    cases hrb₂ with
    | eql heq₂ => rfl
    | curr' heq₂ | curr heq₂ | par heq₂ | comp heq₂ | sigma heq₂ | unbox heq₂ | pair heq₂ | fmap heq₂ | map heq₂ | quot heq₂ | id heq₂ =>
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
    | curr heq₂ | curr' heq₂ | par heq₂ | comp heq₂ | sigma heq₂ | fmap heq₂ | pair heq₂ | eql heq₂ =>
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
    | par heq₂ | comp heq₂ | sigma heq₂ | map heq₂ | pair heq₂ | eql heq₂ =>
      let heqa  := (heq₁ ▸ hr₃).unique hr₁
      let heqb  := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      grind
    | curr' heq₂ | curr heq₂ | id heq₂ =>
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
    | eval _ heq₂ | curr heq₂ | par heq₂ | comp heq₂ =>
      let heqa  := (heq₁ ▸ hr₃).unique hr₁
      let heqb  := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      cases heq'
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
    | eval _ heq₂ | curr heq₂ | par heq₂ | comp heq₂ =>
      let heqa  := (heq₁ ▸ hr₃).unique hr₁
      let heqb  := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      cases heq'
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
  | id heq₁ =>
    cases hrb₂ with
    | eval _ heq₂ | comp heq₂ | curr' heq₂ | curr heq₂ | par heq₂ =>
      let heqa  := (heq₁ ▸ hr₃).unique hr₁
      let heqb  := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      cases heq'
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
          simp [ViewAppHole.reduction] at heq₁
          cases heq₁
          expose_names
          cases hrt.unique hr₁
          cases hr₂.unique hred
          cases hd
          have h : x.max_hole = x.min_hole := by grind
          grind)
        done)
      case fst | snd | unbox =>
        simp [ViewAppHole.reduction] at heq₁
        cases heq₁
      case eql =>
        simp [ViewAppHole.reduction] at heq₁
    | sigma heq' | pair heq' | eql heq' | unbox heq' | fmap heq' | map heq' | snd heq' | fst heq' =>
      expose_names
      have ha := hr₁.max_hole_preserved
      have hb := hr₂.max_hole_preserved
      have hc := e_h.max_hole
      have hd := e_h.min_hole
      let h := heq₁ ▸ hrt₁.reduction.snd
      cases h.unique hr₁
      let h' := heq' ▸ hrt₂.reduction.snd
      cases h'.unique hr₂
  | quot heq₁ =>
    cases hrb₂ with
    | curr' heq₂ | curr heq₂ | par heq₂ | comp heq₂ | sigma heq₂ | pair heq₂ | unbox heq₂ | eql heq₂ | map heq₂ | fmap heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      try (simp [ViewAppHole.reduction] at heq')
      try (cases heq')
      try (grind)
    | eval _ heq₂ =>
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      have heq' := heqa.trans heqb.symm
      cases heq₁
      simp [ViewAppHole.reduction] at heq'
      cases heq'
      have hn₁ := Hole.min_hole (by assumption)
      have hn₂ := Hole.max_hole (by assumption)
      grind
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
Domain preservation is quite important.

I change my mind: domain preservation is not important, because we already have ext for single,
so just generate the same hole and show the length of reduction on that.

Normal forms we havne't covered in ReadbackHead:
- comp g (h hole)
- g hole
  - e.g., Π ∘ ...

Then it's just a matter of showing we've covered everything,
or handling the remaining cases.

Well I think quot handles the remaining cases, so ReadbackHead is total on
ViewAppHole.

Then we have to handle multi-step. Reudce multi-steps.

I think this is handled with mere recursion.
Probably.

We also haven't handled the eval case.
Or curry, we may as well since it's mutually exclusive.
-/
