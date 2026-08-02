import Dcc.Eta.Ast

namespace GenericExpr

inductive ViewQuot : GenericExpr τ_c → Type u
  | quot : ViewQuot (DCC? `(_β, x))
deriving DecidableEq

@[grind, dcc_rel]
def view_quot? (e : GenericExpr τ_c) : Option (ViewQuot e) :=
  match e with
  | (DCC? `(_β, _x)) => .some .quot
  | _ => .none

@[grind ., grind =_]
theorem ViewQuot.complete (h : ViewQuot e) : view_quot? e = .some h := by
  cases h
  · simp [view_quot?]

@[dcc_rel]
def view_quot?_none_sound' (h : (view_quot? e).isNone) : (ViewQuot e → False) := fun h => by
  simp_all [h.complete]

@[grind =, grind =_]
theorem ViewQuot.complete_none (h : ViewQuot e → False) : view_quot? e = .none := by
  unfold view_quot?
  split <;> (
    first
    | exact (h (by constructor)).elim
    | grind)

@[aesop safe forward (rule_sets := [DccRel]), dcc_rel]
theorem view_quot?_none_sound (h : view_quot? e = .none) : ViewQuot e → False := fun h => by
  simp_all [h.complete]

inductive ViewFnType : GenericExpr τ_c → Type u
  | pi      : ViewFnType (DCC? (Π(f_α, f_β) x_α))
deriving DecidableEq

@[grind, dcc_rel]
def view_fn_type? (e : GenericExpr τ_c) : Option (ViewFnType e) :=
  match e with
  | (DCC? (Π(_f_α, _f_β) _x_α)) => .some .pi
  | _ => .none

@[grind ., grind =_]
theorem ViewFnType.complete (h : ViewFnType e) : view_fn_type? e = .some h := by
  cases h
  · simp [view_fn_type?]

@[grind =, grind =_]
theorem ViewFnType.complete_none (h : ViewFnType e → False) : view_fn_type? e = .none := by
  unfold view_fn_type?
  split <;> (
    first
    | exact (h (by constructor)).elim
    | grind)

@[aesop safe forward (rule_sets := [DccRel]), dcc_rel]
theorem view_fn_type?_none_sound (h : view_fn_type? e = .none) : ViewFnType e → False := fun h => by
  simp_all [h.complete]

@[aesop safe forward (rule_sets := [DccRel]), dcc_rel]
theorem view_fn_type?_none_sound' (h : (view_fn_type? e).isNone) : ViewFnType e → False := fun h => by
  simp_all [h.complete]

inductive ViewPi : GenericExpr τ_c → Type u
  | pi      : ViewPi (DCC? Π(f_α, f_β))
deriving DecidableEq

@[grind, dcc_rel]
def view_pi? (e : GenericExpr τ_c) : Option (ViewPi e) :=
  match e with
  | (DCC? Π(_f_α, _f_β))         => .some .pi
  | _ => .none

@[grind ., grind =_]
theorem ViewPi.complete (h : ViewPi e) : view_pi? e = .some h := by
  cases h
  · simp [view_pi?]

@[grind =, grind =_]
theorem ViewPi.complete_none (h : ViewPi e → False) : view_pi? e = .none := by
  unfold view_pi?
  split <;> (
    first
    | exact (h (by constructor)).elim
    | grind)

@[aesop safe forward (rule_sets := [DccRel]), dcc_rel]
theorem view_pi?_none_sound (h : view_pi? e = .none) : ViewPi e → False := fun h => by
  simp_all [h.complete]

inductive ViewBang : GenericExpr τ_c → Type u
  | bang    : ViewBang (DCC? !(α))
deriving DecidableEq

inductive ViewBangCoup : GenericExpr τ_c → Type u
  | coup    : ViewBangCoup (DCC? Coup(β))
  | bang    : ViewBangCoup (DCC? !(α))
deriving DecidableEq

inductive ViewCoupBang : GenericExpr τ_c → Type u
  | coup    : ViewCoupBang (DCC? Coup(β))
  | bang    : ViewCoupBang (DCC? !(Coup(β)))
deriving DecidableEq

@[grind, dcc_rel]
def view_bang_coup? (e : GenericExpr τ_c) : Option (ViewBangCoup e) :=
  match e with
  | (DCC? Coup(_β)) => .some .coup
  | (DCC? !(_α))    => .some .bang
  | _ => .none

@[grind, dcc_rel]
def view_coup_bang? (e : GenericExpr τ_c) : Option (ViewCoupBang e) :=
  match e with
  | (DCC? Coup(_β)) => .some .coup
  | (DCC? !(Coup(_α)))    => .some .bang
  | _ => .none

inductive IsEtaTm : GenericExpr τ_c → Type u
  | eql    : IsEtaTm (DCC? Eql(f_α))
  -- Id(α) x
  | id     : IsEtaTm (DCC? Id(α))
  -- (f ∘ g) x
  | comp   : IsEtaTm f → IsEtaTm (DCC? (f ∘ g))
  | comp'  : IsEtaTm f → IsEtaTm (DCC? (f ∘' g))
  | comp₂  : IsEtaTm f → IsEtaTm (DCC? (f ∘∘ g))
  -- Fstc(..) (x, y) -> x
  | fstc   : IsEtaTm (DCC? Fstc(β))
  | sndc   : IsEtaTm (DCC? Sndc(β))
  -- Σ(f_α, f_β) env -> Coup(...)
  | sigma  : IsEtaTm (DCC? Σ(f_α, f_β))
  -- `(β, x) y
  | quot   : IsEtaTm (DCC? `(β, x))
  -- ⟨f, g⟩ x
  | pair   : IsEtaTm (DCC? ⟦β⟧⟨f, g⟩)
  -- Λ(α, β, x) y z
  | curr   : IsEtaTm (DCC? Λ(α, β, x))
  | curr'  : IsEtaTm (DCC? !Λ(α, β, x))
  | eval   : IsEtaTm (DCC? Eval(α, β, x))
  | map    : IsEtaTm (DCC? !<f>)
  | fmap   : IsEtaTm (DCC? $<f>)
  | unmap  : IsEtaTm (DCC? *<f>)
  | deref  : IsEtaTm (DCC? *(x))
  | top    : IsEtaTm (DCC? ⊤)
  | bot    : IsEtaTm (DCC? ⊥)
  | tintro : IsEtaTm (DCC? ∗)
  | sort   : IsEtaTm (DCC? Sort m)
  | box    : IsEtaTm (DCC? &(x))
  | mk     : IsEtaTm (DCC? ⟦β⟧(x, y))
  | eq     : IsEtaTm (DCC? x = y)
  | refl   : IsEtaTm (DCC? refl(f_α))
  | const  : IsEtaTm (.const _x)
  | app    : IsEtaTm f → IsEtaTm (DCC? (f x))
deriving DecidableEq

@[grind]
def is_eta_tm? (e : GenericExpr τ_c) : Option (IsEtaTm e) :=
  match e with
  | (DCC? Eql(f_α)) => .some (by constructor)
  | (DCC? Id(α)) => .some (by constructor)
  | (DCC? f ∘ g) =>
    match f.is_eta_tm? with
    | .some h => .some (by constructor; exact h)
    | .none => .none
  | (DCC? f ∘' g) =>
    match f.is_eta_tm? with
    | .some h => .some (by constructor; exact h)
    | .none => .none
  | (DCC? f ∘∘ g) =>
    match f.is_eta_tm? with
    | .some h => .some (by constructor; exact h)
    | .none => .none
  | (DCC? Fstc(β)) => .some (by constructor)
  | (DCC? Sndc(β)) => .some (by constructor)
  | (DCC? Σ(f_α, f_β)) => .some (by constructor)
  | (DCC? `(β, x)) => .some (by constructor)
  | (DCC? ⟦β⟧⟨f, g⟩) => .some (by constructor)
  | (DCC? ⟦β⟧(x, y)) => .some (by constructor)
  | (DCC? Λ(α, β, x)) => .some (by constructor)
  | (DCC? !Λ(α, β, x)) => .some (by constructor)
  | (DCC? Eval(α, β, x)) => .some (by constructor)
  | (DCC? !<f>) => .some (by constructor)
  | (DCC? $<f>) => .some (by constructor)
  | (DCC? *(f)) => .some (by constructor)
  | (DCC? *<f>) => .some (by constructor)
  | (DCC? &(f)) => .some (by constructor)
  | (DCC? x = y) => .some (by constructor)
  | (DCC? refl(f_α)) => .some (by constructor)
  | (DCC? Sort m) => .some (by constructor)
  | (DCC? ⊤) => .some (by constructor)
  | (DCC? ⊥) => .some (by constructor)
  | (DCC? ∗) => .some (by constructor)
  | (DCC? (f x)) =>
    match f.is_eta_tm? with
    | .some h => .some (by constructor; exact h)
    | .none => .none
  | .const _x => .some (by constructor)
  | .coup _
  | .bang _
  | .pi _ _ => .none

@[grind ., grind =_, aesop safe forward (rule_sets := [DccRel])]
theorem IsEtaTm.complete (h : IsEtaTm e) : is_eta_tm? e = .some h := by
  induction h <;> simp_all [is_eta_tm?]

@[grind =, grind =_]
theorem IsEtaTm.complete_none (h : IsEtaTm e → False) : is_eta_tm? e = .none := by
  induction e
  any_goals (
    focus
    simp [is_eta_tm?]
    try split
    try (
      apply False.elim
      apply h
      constructor
      try assumption)
    try rfl)

@[aesop safe forward (rule_sets := [DccRel]), dcc_rel]
theorem is_eta_tm?_none_sound (h : is_eta_tm? e = .none) : IsEtaTm e → False := fun h => by
  simp_all [h.complete]

def is_eta_tm?_sound (_h : is_eta_tm? e = .some hr) : IsEtaTm e := hr

inductive ViewEta : GenericExpr τ_c → Type u
  | pi_type : ViewEta (DCC? (Π(f_α, f_β) env))
  | pi      : ViewEta (DCC? Π(f_α, f_β))
  | pi_comp : ViewEta (DCC? (Π(f_α, f_β) ∘' g))
  | coup    : ViewEta (DCC? Coup(β))
  | bang    : ViewEta (DCC? !(β))
deriving DecidableEq

@[grind, dcc_rel]
def view_eta? (e : GenericExpr τ_c) : Option (ViewEta e) :=
  match e with
  | (DCC? (Π(_f_α, _f_β) _env))  => .some (.pi_type)
  | (DCC? Π(_f_α, _f_β))         => .some .pi
  | (DCC? (Π(_f_α, _f_β) ∘' _g)) => .some .pi_comp
  | (DCC? Coup(_β))              => .some .coup
  | (DCC? !(_β))                 => .some .bang
  | _ => .none

@[grind ., grind =_]
theorem ViewEta.complete (h : ViewEta e) : view_eta? e = .some h := by
  cases h <;> simp [view_eta?]

@[grind =, grind =_]
theorem ViewEta.complete_none (h : ViewEta e → False) : view_eta? e = .none := by
  unfold view_eta?
  split <;> (
    first
    | exact (h (by constructor)).elim
    | grind)

@[aesop safe forward (rule_sets := [DccRel]), dcc_rel]
theorem view_eta?_none_sound (h : view_eta? e = .none) : ViewEta e → False := fun h => by
  simp_all [h.complete]

theorem IsEtaTm.complete_view_eta (h : IsEtaTm e) : view_eta? e = .none := by
  induction h <;> (simp [view_eta?]; try grind)

@[grind =_, grind .]
theorem ViewBangCoup.complete (h : ViewBangCoup e) : view_bang_coup? e = .some h := by
  cases h <;> simp [view_bang_coup?]

@[grind =, grind =_]
theorem ViewBangCoup.complete_none (h : ViewBangCoup e → False) : view_bang_coup? e = .none := by
  unfold view_bang_coup?
  split <;> (
    first
    | exact (h (by constructor)).elim
    | grind)

@[grind =_, grind .]
theorem ViewCoupBang.complete (h : ViewCoupBang e) : view_coup_bang? e = .some h := by
  cases h <;> simp [view_coup_bang?]

@[grind =, grind =_]
theorem ViewCoupBang.complete_none (h : ViewCoupBang e → False) : view_coup_bang? e = .none := by
  unfold view_coup_bang?
  split <;> (
    first
    | exact (h (by constructor)).elim
    | grind)

@[aesop safe forward (rule_sets := [DccRel]), dcc_rel]
theorem view_bang_coup?_none_sound (h : view_bang_coup? e = .none) : ViewBangCoup e → False := fun h => by
  simp_all [h.complete]

@[aesop safe forward (rule_sets := [DccRel]), dcc_rel]
theorem view_coup_bang?_none_sound (h : view_coup_bang? e = .none) : ViewCoupBang e → False := fun h => by
  simp_all [h.complete]

@[aesop safe forward (rule_sets := [DccRel]), dcc_rel]
theorem view_coup_bang?_none_sound' (h : (view_coup_bang? e).isNone) : ViewCoupBang e → False := fun h => by
  simp_all [h.complete]

end GenericExpr
