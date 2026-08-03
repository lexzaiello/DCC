import Dcc.Eta.Ast
import Dcc.Aff.Red
import Dcc.Relation
import Dcc.Types
import Mathlib.Logic.Equiv.Defs

/-
Only η rule we probably also need is:

(Π(f_α, f_β) env)
f_α env -> f_α'

if env exists at the top level, we can reduce
f_βenv -> f_β'

this gives us the Id curry reduction for free to coerce arrows nicely.
Although lowkey I want to just try the type-checker first on examples to see what works.

If things don't work, then we can upgrade to the tracer matching

Alternative:
we could make Λ quotation the canonical quotation, not `(α, β), but see if everything works first.
debug examples
-/

namespace GenericExpr

inductive EtaMap.{u} {τ_c : Type u} : (dom : GenericExpr (τ := EtaConst (τ := τ_c))) → (out : GenericExpr (τ := EtaConst (τ := τ_c))) → (hole_arg : GenericExpr (τ := EtaConst (τ := τ_c))) → (f' : GenericExpr (τ := EtaConst (τ := τ_c))) → Prop
  | id    : EtaMap dom hole_arg hole_arg (DCC? Id(dom))
  | par   : EtaMap dom (DCC? (f hole_arg)) hole_arg f
  | fstc  : EtaMap dom (DCC? &(hole(a))) (DCC? ⟦β⟧(&(hole(a)), &(hole(a + 1)))) (DCC? Fstc(β))
  | sndc  : EtaMap dom (DCC? &(hole(a + 1))) (DCC? ⟦β⟧(&(hole(a)), &(hole(a + 1)))) (DCC? Sndc(β))
  | fstc' : EtaMap dom (DCC? hole(a)) (DCC? &(⟦β⟧(&(hole(a)), &(hole(a + 1))))) (DCC? *<Fstc(β)>)
  | sndc' : EtaMap dom (DCC? hole(a + 1)) (DCC? &(⟦β⟧(&(hole(a)), &(hole(a + 1))))) (DCC? *<Sndc(β)>)

/-
hole(a) hole(a + 1)

⟦β⟧(hole(a), hole(a + 1))

This is canonically Eval id

but does it require pair?


pair is superfluous

there is some canonical eta reduction for eval.
for one thing, self application is invalid.
so hole(1) hole(1)
is not valid.

From curien's paper

App ∘ ⟨x ∘ Λ, z⟩

If ⟦β⟧(hole(1), hole(2))

reduces to hole(2) !(⊤). this eta-reduction absolutely works.
the order is just kinda wacky.

no this is fine. because our sorts are wrapped in quotation for the environment.
absolutely do the eta rule.

but the order is swapped. why did that happen?

can we change the type of ∘∘?
probably not.
-/

def map_eta.{u} {τ_c : Type u} [DecidableEq τ_c] (dom : GenericExpr (τ := EtaConst (τ := τ_c))) (out : GenericExpr (τ := EtaConst (τ := τ_c))) (hole_arg : GenericExpr (τ := EtaConst (τ := τ_c))) : Option ((f' : GenericExpr (τ := EtaConst (τ := τ_c))) × PLift (EtaMap dom out hole_arg f')) :=
  if heq : out = hole_arg then
    heq ▸ .some ⟨_, ⟨.id⟩⟩
  else
    match out, hole_arg with
    | DCC? (_f hole_arg₂), hole_arg =>
      if heq : hole_arg₂ = hole_arg then
        heq ▸ .some ⟨_, ⟨.par⟩⟩
      else .none
    | (DCC? &(hole(n))), (DCC? ⟦_β⟧(&(hole(a)), &(hole(b)))) =>
      if h₁ : b = a + 1 then
        if h₂ : n = a then by
          cases h₁; cases h₂
          exact .some ⟨_, ⟨.fstc⟩⟩
        else if h₂ : n = a + 1 then by
          cases h₁; cases h₂
          exact .some ⟨_, ⟨.sndc⟩⟩
        else .none
      else .none
    | (DCC? hole(n)), (DCC? &(⟦_β⟧(&(hole(a)), &(hole(b))))) =>
      if h₁ : b = a + 1 then
        if h₂ : n = a then by
          cases h₁; cases h₂
          exact .some ⟨_, ⟨.fstc'⟩⟩
        else if h₂ : n = a + 1 then by
          cases h₁; cases h₂
          exact .some ⟨_, ⟨.sndc'⟩⟩
        else .none
      else .none
    | _, _ => .none

@[aesop safe forward (rule_sets := [DccReduce])]
theorem EtaMap.complete.{u} {τ_c : Type u} [DecidableEq τ_c] {dom out hole_arg f' : GenericExpr (τ := EtaConst (τ := τ_c))}
  (h : EtaMap (τ_c := τ_c) dom out hole_arg f') : map_eta dom out hole_arg = .some ⟨f', ⟨h⟩⟩ := by
  dsimp [map_eta]
  cases h
  any_goals (simp)
  · intro h
    cases h

@[aesop safe forward (rule_sets := [DccReduce])]
inductive EtaResult.{u} {τ_c : Type u} [DecidableEq τ_c] : (dom : GenericExpr (τ := EtaConst (τ := τ_c))) → (out : GenericExpr (τ := EtaConst (τ := τ_c))) → (hole_arg : GenericExpr (τ := EtaConst (τ := τ_c))) → (f' : GenericExpr (τ := EtaConst (τ := τ_c))) → Prop
  | map   : (GenericExpr.contains out hole_arg)
    → EtaMap dom out hole_arg f'
    → EtaResult dom out hole_arg f'
  | quot  : (¬ GenericExpr.contains out hole_arg)
    → EtaResult dom out hole_arg (DCC? `(dom, out))

/-
TODO:
- arity 2
- handle !Λ with domain !(α), insert &(hole)
-/

inductive EtaMap₂.{u} {τ_c : Type u} : (dom₁ : GenericExpr (τ := EtaConst (τ := τ_c)))
  -- β hole₁
  → (dom₂ : GenericExpr (τ := EtaConst (τ := τ_c)))
  → (out : GenericExpr (τ := EtaConst (τ := τ_c)))
  → (hole₁ : GenericExpr (τ := EtaConst (τ := τ_c)))
  → (hole₂ : GenericExpr (τ := EtaConst (τ := τ_c)))
  → (f' : GenericExpr (τ := EtaConst (τ := τ_c))) → Prop
  | par      : EtaMap₂ dom₁ dom₂ (DCC? (f hole₁ hole₂)) hole₁ hole₂ f
  | id       : EtaMap₂ dom₁ dom₂ (DCC? (hole₁ hole₂)) (DCC? hole₁) (DCC? hole₂) (DCC? Id(dom₁))
-- hole₁ hole₂ = ⟦dom₂⟧(hole₁, hole₂) means this is Λ(dom₁, dom₂, Id(Coup(dom₂)))
-- this is basically 2 arg version of id
  | curr     : EtaMap₂ dom₁ dom₂ (DCC? ⟦dom₂⟧(hole₁, hole₂)) hole₁ hole₂ (DCC? Λ(dom₁, dom₂, Id(Coup(dom₂))))
  | curr'    : EtaMap₂ (DCC? !(α)) (DCC? !<β>)
      (DCC? &(⟦β⟧(hole₁, hole₂)))
      (DCC? &(hole₁)) (DCC? &(hole₂))
      (DCC? !Λ(α, β, Id(!(Coup(β)))))
  -- Exclusive with other two
  -- this is couple quotation
  -- if dom₂ is quotation i.e., `(dom₁, dom₂), then
  -- this is just simple double quotation `(dom₁, `(dom₂, c))

inductive TmEtaReduces.{u} {τ_c : Type u} [DecidableEq τ_c] : (level : ℕ) → (f : GenericExpr (τ := EtaConst (τ := τ_c))) → (f' : GenericExpr (τ := EtaConst (τ := τ_c))) → Prop
  | coupl : RedAffReflTrans f f'
    → IsNorm RedAff f'
    → Domain f' (DCC? Coup(β))
    → RedAffReflTrans (DCC? (f' ⟦β⟧(&(hole(level + 1)), &(hole(level + 2))))) e'
    → IsNorm RedAff e'
    → EtaResult (DCC? Coup(β)) e' (DCC? ⟦β⟧(&(hole(level + 1)), &(hole(level + 2)))) f''
    → TmEtaReduces level f f''
  | tm    : RedAffReflTrans f f'
    → IsNorm RedAff f'
    → Domain f' τ
    → (ViewCoup τ → False)
    → RedAffReflTrans (DCC? (f' hole(level + 1))) e'
    → IsNorm RedAff e'
    → EtaResult τ e' (DCC? hole(level + 1)) f''
    → TmEtaReduces level f f''
  | bang₁ : RedAffReflTrans f f'
    → IsNorm RedAff f'
    → Domain f' (DCC? !(Coup(β)))
    → RedAffReflTrans (DCC? (f' &(⟦β⟧(&(hole(level + 1)), &(hole(level + 2)))))) e'
    → IsNorm RedAff e'
    → EtaResult (DCC? !(Coup(β))) e' (DCC? &(⟦β⟧(&(hole(level + 1)), &(hole(level + 2))))) f''
    → TmEtaReduces level f f''

def mk_eta_result.{u} {τ_c : Type u} [DecidableEq τ_c] (dom : GenericExpr (τ := EtaConst (τ := τ_c)))
  (out : GenericExpr (τ := EtaConst (τ := τ_c))) (hole_arg : GenericExpr (τ := EtaConst (τ := τ_c))) : Option ((f' : GenericExpr (τ := EtaConst (τ := τ_c))) × PLift (EtaResult dom out hole_arg f')) :=
  if h₁ : out.contains hole_arg then
    match map_eta dom out hole_arg with
    | .some ⟨_, ⟨h₂⟩⟩ => .some ⟨_, ⟨.map h₁ h₂⟩⟩
    | _ => .none
  else
    .some ⟨_, ⟨.quot h₁⟩⟩

def eta_reduce_tm.{u} {τ_c : Type u} [DecidableEq τ_c] (level : ℕ)
  (f : GenericExpr (τ := EtaConst (τ := τ_c))) : Option ((f' : GenericExpr (τ := EtaConst (τ := τ_c))) × (PLift (TmEtaReduces level f f'))) :=
  match (reduce RedAff f).fst.domain? with
  | .some ⟨τ, ⟨h₁⟩⟩ =>
    match heq_coup : τ.view_coup? with
    | .some (.coup (β := β)) =>
      match mk_eta_result (DCC? Coup(β))
        (reduce RedAff (DCC? (#((reduce RedAff f).fst) ⟦β⟧(&(hole(level + 1)), &(hole(level + 2)))))).fst
        (DCC? ⟦β⟧(&(hole(level + 1)), &(hole(level + 2)))) with
      | .some ⟨_, ⟨h₂⟩⟩ =>
        .some ⟨_, ⟨.coupl (reduce_sound rfl) (reduce_norm rfl) h₁ (reduce_sound rfl) (reduce_norm rfl) h₂⟩⟩
      | _ => .none
    | .some (.bang (β := β)) =>
      match mk_eta_result (DCC? !(Coup(β)))
        (reduce RedAff (DCC? (#((reduce RedAff f).fst) &(⟦β⟧(&(hole(level + 1)), &(hole(level + 2))))))).fst
        (DCC? &(⟦β⟧(&(hole(level + 1)), &(hole(level + 2))))) with
      | .some ⟨_, ⟨h₂⟩⟩ =>
        .some ⟨_, ⟨.bang₁ (reduce_sound rfl) (reduce_norm rfl) h₁ (reduce_sound rfl) (reduce_norm rfl) h₂⟩⟩
      | _ => .none
    | .none =>
      match mk_eta_result τ
        (reduce RedAff (DCC? (#((reduce RedAff f).fst) hole(level + 1)))).fst
        (DCC? hole(level + 1)) with
      | .some ⟨_, ⟨h₂⟩⟩ =>
        .some ⟨_, ⟨.tm (reduce_sound rfl) (reduce_norm rfl) h₁ (by aesop (rule_sets := [DccRel])) (reduce_sound rfl) (reduce_norm rfl) h₂⟩⟩
      | _ => .none
  | _ => .none

-- TODO: might need quot₁ if β is not dependent on α
inductive TmEtaReduces₂.{u} {τ_c : Type u} [DecidableEq τ_c] : (level : ℕ) → (f : GenericExpr (τ := EtaConst (τ := τ_c))) → (f' : GenericExpr (τ := EtaConst (τ := τ_c))) → Prop
  | quot₂    : Domain₂ f α₀ β₀
    → (GenericExpr.is_bang α₀ = .some α)
    → (GenericExpr.is_bang_map β₀ = .some β)
    → (¬ GenericExpr.contains e' (DCC? &(hole(level + 1))))
    → (¬ GenericExpr.contains e' (DCC? &(hole(level + 2))))
    → RedAffReflTrans (DCC? (f &(hole(level + 1)) &(hole(level + 2)))) e'
    → IsNorm RedAff e'
    → TmEtaReduces₂ level f (DCC? !Λ(α, β, `(!(Coup(β)), e')))
  | quot₂'   : Domain₂ f α f_β
    → (GenericExpr.is_quote f_β = .none)
    → (GenericExpr.is_bang α = .none)
    → (GenericExpr.is_bang_map f_β = .none)
    → (¬ GenericExpr.contains e' (DCC? hole(level + 1)))
    → (¬ GenericExpr.contains e' (DCC? hole(level + 2)))
    → RedAffReflTrans (DCC? (f hole(level + 1) hole(level + 2))) e'
    → IsNorm RedAff e'
    → TmEtaReduces₂ level f (DCC? Λ(α, f_β, `(Coup(f_β), e')))
  | quot₃'   : Domain₂ f α (DCC? `(α₂, β))
    → (GenericExpr.is_bang α = .none)
    → (¬ GenericExpr.contains e' (DCC? hole(level + 1)))
    → (¬ GenericExpr.contains e' (DCC? hole(level + 2)))
    → RedAffReflTrans (DCC? (f hole(level + 1) hole(level + 2))) e'
    → IsNorm RedAff e'
    → TmEtaReduces₂ level f (DCC? `(α, `(β, e')))
  | map      : Domain₂ f α β
    → (GenericExpr.is_bang α = .none)
    → (GenericExpr.is_bang_map β = .none)
    → (GenericExpr.contains e' (DCC? hole(level + 1)) ∨ GenericExpr.contains e' (DCC? hole(level + 2)))
    → RedAffReflTrans (DCC? (f hole(level + 1) hole(level + 2))) e'
    → IsNorm RedAff e'
    → (EtaMap₂ α β e' (DCC? hole(level + 1)) (DCC? hole(level + 2)) f')
    → TmEtaReduces₂ level f f'

def map_eta₂.{u} {τ_c : Type u} [DecidableEq τ_c] (dom₁ dom₂ out hole₁ hole₂ : GenericExpr (τ := EtaConst (τ := τ_c))) : Option
  ((f' : GenericExpr (τ := EtaConst (τ := τ_c))) × PLift
  (EtaMap₂ dom₁ dom₂ out hole₁ hole₂ f')) :=
  if heqa : out = (DCC? (hole₁ hole₂)) then by
    cases heqa
    exact .some ⟨_, ⟨.id⟩⟩
  else
    match heq₁ : out with
    | (DCC? (f hole₃ hole₄)) =>
      if heq₂ : (DCC? (f hole₃ hole₄)) = (DCC? (f hole₁ hole₂)) then by
        rw [heq₂]
        exact .some ⟨_, ⟨.par⟩⟩
      else .none
    | (DCC? ⟦dom₃⟧(hole₃, hole₄)) =>
      if heq₂ : (DCC? ⟦dom₃⟧(hole₃, hole₄)) = (DCC? ⟦dom₂⟧(hole₁, hole₂)) then by
        rw [heq₂]
        exact .some ⟨_, ⟨.curr⟩⟩
      else .none
    | (DCC? &(⟦β⟧(hole₃, hole₄))) =>
      match heq₂ : dom₁, heq₃ : dom₂, heq₄ : hole₁, heq₅ : hole₂ with
      | (DCC? !(α)), (DCC? !<β₂>), (DCC? &(ha)), (DCC? &(hb)) =>
        if heq₄ : (DCC? &(⟦β⟧(hole₃, hole₄))) = (DCC? &(⟦β₂⟧(ha, hb))) then by
          rw [heq₄]
          cases heq₄
          exact .some ⟨_, ⟨.curr'⟩⟩
        else .none
      | _, _, _, _ => .none
    | _ => .none

theorem EtaMap₂.complete.{u} {τ_c : Type u} [DecidableEq τ_c]
  {dom₁ dom₂ out hole₁ hole₂ f' : GenericExpr (τ := EtaConst (τ := τ_c))} (h : GenericExpr.EtaMap₂ (τ_c := τ_c) dom₁ dom₂ out hole₁ hole₂ f') : map_eta₂ dom₁ dom₂ out hole₁ hole₂ = .some ⟨f', ⟨h⟩⟩ := by
  cases h
  case par =>
    dsimp [map_eta₂]
    simp
    intro h
    cases h
  case curr' | curr | id =>
    dsimp [map_eta₂]
    simp

def eta_reduce_tm₂.{u} {τ_c : Type u} [DecidableEq τ_c] (level : ℕ) (f : GenericExpr (τ := EtaConst (τ := τ_c))) : Option ((f' : GenericExpr (τ := EtaConst (τ := τ_c))) × (PLift (TmEtaReduces₂ level f f'))) :=
  match heq : f.domain₂? with
  | .some ⟨α₀, β₀, ⟨h⟩⟩ =>
    if h_bang : (α₀.is_bang).isSome ∧ (β₀.is_bang_map).isSome then
      let e' := (reduce RedAff (DCC? (f &(hole(level + 1)) &(hole(level + 2))))).fst
      if h_contains : ¬ e'.contains (DCC? &(hole(level + 1)))
        ∧ ¬ e'.contains (DCC? &(hole(level + 2))) then by
        exact .some ⟨(DCC? !Λ(#(α₀.is_bang.get h_bang.left), #(β₀.is_bang_map.get h_bang.right), `(!(Coup(#(β₀.is_bang_map.get h_bang.right))), e'))), ⟨.quot₂ h (by
          simp_all) (by
            simp_all) h_contains.left h_contains.right
          (reduce_sound rfl) (reduce_norm rfl)⟩⟩
      else .none
    else
      let e' := (reduce RedAff (DCC? (f hole(level + 1) hole(level + 2)))).fst
      if h_contains : ¬ e'.contains (DCC? hole(level + 1))
        ∧ ¬ e'.contains (DCC? hole(level + 2)) then
        if h_bang : α₀.is_bang = .none then
          match h_quot_eq₀ : β₀.is_quote with
          | .some ⟨α₂, β, ⟨h_quot_eq⟩⟩ =>
            .some ⟨_,
              ⟨.quot₃'
                (h_quot_eq ▸ h)
                h_bang
                (by
                  change ¬e'.contains _
                  simp [h_contains.left])
                (by
                  change ¬e'.contains _
                  simp [h_contains.right])
                  (reduce_sound rfl)
                  (reduce_norm rfl)⟩⟩
          | .none =>
            if h_bang₂ : β₀.is_bang_map = .none then
              .some ⟨_,
                ⟨.quot₂'
                  h
                  h_quot_eq₀
                  h_bang h_bang₂ h_contains.left h_contains.right (reduce_sound rfl) (reduce_norm rfl)⟩⟩
            else .none
        else .none
      else if h_contains : e'.contains (DCC? hole(level + 1))
        ∨ e'.contains (DCC? hole(level + 2)) then
        if h_bang : α₀.is_bang = .none ∧ β₀.is_bang_map = .none then
          match map_eta₂ α₀ β₀ e' (DCC? hole(level + 1)) (DCC? hole(level + 2)) with
          | .some ⟨f', ⟨hf⟩⟩ =>
            .some ⟨f', ⟨.map h h_bang.left h_bang.right h_contains (reduce_sound rfl) (reduce_norm rfl) hf⟩⟩
          | _ => .none
        else .none
      else .none
  | .none => .none

#eval (repr ∘ Sigma.fst) <$> (DCC? ((Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)) ∘'
                         Fstc(Π(Sndc(`(⊤, Sort 1)),
                                Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))) ∘'
                      Fstc((Sndc(`(⊤, Sort 1)) ∘'
                              Fstc(Π(Sndc(`(⊤, Sort 1)),
                                     Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                       `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))))).eta_reduce_tm₂ (τ_c := Unit) 0

#eval (repr ∘ Sigma.fst) <$> (DCC? ((Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)) ∘'
                         Fstc(Π(Sndc(`(⊤, Sort 1)),
                                Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))) ∘'
                      Fstc((Sndc(`(⊤, Sort 1)) ∘'
                              Fstc(Π(Sndc(`(⊤, Sort 1)),
                                     Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                       `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))))).domain₂? (τ_c := Unit)

theorem EtaResult.complete.{u} {τ_c : Type u} [DecidableEq τ_c]
  {dom out hole_arg f' : GenericExpr (τ := EtaConst (τ := τ_c))} (h : EtaResult (τ_c := τ_c) dom out hole_arg f') : mk_eta_result dom out hole_arg = .some ⟨f', ⟨h⟩⟩ := by
  dsimp [mk_eta_result]
  cases h <;> aesop (rule_sets := [DccReduce])

@[aesop safe forward (rule_sets := [DccReduce])]
theorem TmEtaReduces.complete.{u} {τ_c : Type u} [DecidableEq τ_c] {f f' : GenericExpr (τ := EtaConst (τ := τ_c))}
  (h : TmEtaReduces (τ_c := τ_c) level f f') : eta_reduce_tm level f = .some ⟨f', ⟨h⟩⟩ := by
  dsimp [eta_reduce_tm]
  induction h
  case bang₁ | coupl =>
    rename_i f f' β level e' f'' hrt₁ hn₁ h_domain hr hn hmk
    have hb := h_domain.complete
    have ha := reduce_complete_fst hr hn
    have hc := hmk.complete
    have heq := reduce_complete hrt₁ hn₁
    have heq₂ : (reduce RedAff f).fst = f' := by simp_all
    have h_domain' := h_domain.complete
    cases heq₂
    simp_all
    cases ha
    simp_all [dcc_rel]
  case tm =>
    rename_i e' f'' hrt₁ hn₁ h_dom₁ h_view hrt₂ hn₂ hmk
    have hb := h_dom₁.complete
    have ha := reduce_complete_fst hrt₁ hn₁
    have haa := reduce_complete_fst hrt₂ hn₂
    have hc := hmk.complete
    have hd := ViewCoup.complete_none (by assumption)
    rename_i f₀ f₀' τ level
    have heq₂ : (reduce RedAff f₀).fst = f₀' := by simp_all
    cases heq₂
    cases haa
    simp [hb]
    aesop

theorem eta_reduce_tm_none.{u} {τ_c : Type u} [DecidableEq τ_c] {f : GenericExpr (@EtaConst τ_c)} (heq : eta_reduce_tm level f = .none) : ¬ ∃ f', TmEtaReduces level f f' :=
  fun ⟨_, h⟩ => by
    have h := h.complete
    simp_all

theorem TmEtaReduces₂.complete.{u} {τ_c : Type u} [DecidableEq τ_c] {f f' : GenericExpr (τ := EtaConst (τ := τ_c))}
  (h : TmEtaReduces₂ (τ_c := τ_c) level f f') : eta_reduce_tm₂ level f = .some ⟨f', ⟨h⟩⟩ := by
  unfold eta_reduce_tm₂
  cases h with
  | quot₂ h_domain h₁ h₂ h_contains₁ h_contains₂ hr hn =>
    have h_red_complete := reduce_complete_fst hr hn
    have h := h_domain.complete
    simp_all
    rw [h]
    simp [h₁, h₂, h_red_complete]
    grind
  | quot₃' =>
    rename_i α α₂ β e' h_bang hn h_contains₁ h_contains₂ h_domain hr
    have h_red_complete := reduce_complete_fst hr hn
    have h := h_domain.complete
    rw [h]
    simp
    simp [h_bang, h_red_complete, h_contains₁, h_contains₂, is_quote]
    grind
  | quot₂' =>
    rename_i α β e' h_quote h_bang h_bang_map hn h_contains₁ h_contains₂ h_domain hr
    have h_red_complete := reduce_complete_fst hr hn
    have h := h_domain.complete
    rw [h]
    simp
    simp [h_bang, h_red_complete, h_contains₁, h_contains₂]
    simp [h_bang_map]
    split
    · simp_all
    case h_2 =>
      simp_all
      grind
  | map =>
    rename_i h_bang₁ h_bang₂ hn h_contains h_domain hr h_map
    have h_red_complete := reduce_complete_fst hr hn
    have h := h_domain.complete
    have hb := h_map.complete
    simp_all
    rw [h]
    simp [h_bang₁, h_bang₂]
    cases h_red_complete.symm
    cases h_contains with
    | inl hl => simp [hl, hb]
    | inr hr => simp [hr, hb]

theorem eta_reduce_tm₂_none.{u} {τ_c : Type u} [DecidableEq τ_c] {f : GenericExpr (@EtaConst τ_c)} (heq : eta_reduce_tm₂ level f = .none) : ¬ ∃ f', TmEtaReduces₂ level f f' :=
  fun ⟨_, h⟩ => by
    have h := h.complete
    simp_all

instance TmEtaReduces.instDecidable.{u} {τ_c : Type u} [DecidableEq τ_c]
  {f f' : GenericExpr (τ := EtaConst (τ := τ_c))} : Decidable (TmEtaReduces (τ_c := τ_c) level f f') :=
  if h : (f.eta_reduce_tm level).isSome then
    if heq : ((f.eta_reduce_tm level).get h).fst = f' then
      .isTrue (heq ▸ ((f.eta_reduce_tm level).get h).snd.down)
    else
      .isFalse (fun h => by
        have h := h.complete
        simp_all)
  else
    .isFalse (fun h => by
      have h := h.complete
      simp_all)

instance TmEtaReduces.instExistsDecidable.{u} {τ_c : Type u} [DecidableEq τ_c]
  {f : GenericExpr (τ := EtaConst (τ := τ_c))} : Decidable (∃ f', TmEtaReduces (τ_c := τ_c) level f f') :=
  if heq : (f.eta_reduce_tm level).isSome then
    .isTrue ⟨_, ((f.eta_reduce_tm level).get heq).snd.down⟩
  else
    .isFalse (fun ⟨_, h⟩ => by
      have h := h.complete
      simp_all)

instance TmEtaReduces₂.instDecidable.{u} {τ_c : Type u} [DecidableEq τ_c]
  {f f' : GenericExpr (τ := EtaConst (τ := τ_c))} : Decidable (TmEtaReduces₂ (τ_c := τ_c) level f f') :=
  if h : (f.eta_reduce_tm₂ level).isSome then
    if heq : ((f.eta_reduce_tm₂ level).get h).fst = f' then
      .isTrue (heq ▸ ((f.eta_reduce_tm₂ level).get h).snd.down)
    else
      .isFalse (fun h => by
        have h := h.complete
        simp_all)
  else
    .isFalse (fun h => by
      have h := h.complete
      simp_all)

instance TmEtaReduces₂.instExistsDecidable.{u} {τ_c : Type u} [DecidableEq τ_c]
  {f : GenericExpr (τ := EtaConst (τ := τ_c))} : Decidable (∃ f', TmEtaReduces₂ (τ_c := τ_c) level f f') :=
  if heq : (f.eta_reduce_tm₂ level).isSome then
    .isTrue ⟨_, ((f.eta_reduce_tm₂ level).get heq).snd.down⟩
  else
    .isFalse (fun ⟨_, h⟩ => by
      have h := h.complete
      simp_all)

inductive FnEtaReduces.{u} {τ_c : Type u} [DecidableEq τ_c] : (level : ℕ) →
  (f : GenericExpr (τ := EtaConst (τ := τ_c))) → (f' : GenericExpr (τ := EtaConst (τ := τ_c))) → Prop
  | pi   : FnEtaReduces level.succ f_α f_α'
    → FnEtaReduces level.succ.succ f_β f_β'
    → FnEtaReduces level (DCC? Π(f_α, f_β)) (DCC? Π(f_α', f_β'))
  | tm₁  : f.tm_arity = 1
    → TmEtaReduces level f f'
    → FnEtaReduces level f f'
  | tm₂  : f.tm_arity = 2
    → TmEtaReduces₂ level f f'
    → FnEtaReduces level f f'
  /-| tm'₁ : f.tm_arity = 1
    → (¬ ∃ f', TmEtaReduces level f f')
    → FnEtaReduces level f f-/
  | tm'₂ : f.tm_arity = 2
    → (¬ ∃ f', TmEtaReduces₂ level f f')
    → FnEtaReduces level f f

/-def fn_reduces.{u} {τ_c : Type u} [DecidableEq τ_c] (level : ℕ) (f : GenericExpr (τ := EtaConst (τ := τ_c))) : Option
  ((f' : GenericExpr (τ := EtaConst (τ := τ_c))) × (PLift (FnEtaReduces level f f'))) := by
    cases heq : f
    case pi f_α f_β =>
      match f_α.fn_reduces level.succ with
      | .some ⟨_, ⟨h₁⟩⟩ =>
        match f_β.fn_reduces level.succ.succ with
        | .some ⟨_, ⟨h₂⟩⟩ =>
          exact .some ⟨_, ⟨.pi h₁ h₂⟩⟩
        | _ => exact .none
      | .none => exact .none
    all_goals (
      focus
      if harity : f.arity = 1 then
          match _heq₃ : f.eta_reduce_tm level with
          | .some ⟨_f', ⟨h⟩⟩ =>
            cases heq
            exact .some ⟨_, ⟨.tm₁ (by grind) harity h⟩⟩
          | .none => cases heq; exact .some ⟨_, ⟨.tm'₁ (by grind) harity (eta_reduce_tm_none _heq₃)⟩⟩
      else if harity : f.arity = 2 then
        if heq₂ : ∃ f', TmEtaReduces₂ level f f' then
          match _heq₃ : f.eta_reduce_tm₂ level with
          | .some ⟨_f', ⟨h⟩⟩ =>
            cases heq
            exact .some ⟨_, ⟨.tm₂ (by grind) harity h⟩⟩
          | .none => exact .none
        else
          cases heq
          exact .some ⟨_, ⟨.tm'₂ (by grind) harity heq₂⟩⟩
      else exact .none)-/

@[grind]
def fn_reduces.{u} {τ_c : Type u} [DecidableEq τ_c] (level : ℕ) (f : GenericExpr (τ := EtaConst (τ := τ_c))) : Option
  ((f' : GenericExpr (τ := EtaConst (τ := τ_c))) × (PLift (FnEtaReduces level f f'))) :=
  if harity : f.tm_arity = 1 then
    match _heq₃ : f.eta_reduce_tm level with
    | .some ⟨_f', ⟨h⟩⟩ =>
      .some ⟨_, ⟨.tm₁ harity h⟩⟩
    | .none => .none
    /-| .none =>
      
      .some ⟨_, ⟨.tm'₁ harity (eta_reduce_tm_none _heq₃)⟩⟩-/
  else if harity : f.tm_arity = 2 then
    match _heq₃ : f.eta_reduce_tm₂ level with
    | .some ⟨_f', ⟨h⟩⟩ =>
      .some ⟨_, ⟨.tm₂ harity h⟩⟩
    | .none => .some ⟨_, ⟨.tm'₂ harity (eta_reduce_tm₂_none _heq₃)⟩⟩
  else
    match _heq : f with
    | (DCC? Π(f_α, f_β)) =>
      match f_α.fn_reduces level.succ with
      | .some ⟨_, ⟨h₁⟩⟩ =>
        match f_β.fn_reduces level.succ.succ with
        | .some ⟨_, ⟨h₂⟩⟩ =>
          .some ⟨_, ⟨.pi h₁ h₂⟩⟩
        | _ => .none
      | _ => .none
    | _ => .none

/-@[grind]
def fn_reduces.{u} {τ_c : Type u} [DecidableEq τ_c] (level : ℕ) (f : GenericExpr (τ := EtaConst (τ := τ_c))) : Option
  ((f' : GenericExpr (τ := EtaConst (τ := τ_c))) × (PLift (FnEtaReduces level f f'))) :=
  if heq : ∃ f_α f_β, f = (DCC? Π(f_α, f_β)) then
    match _heq : f with
    | (DCC? Π(f_α, f_β)) =>
      match f_α.fn_reduces level.succ with
      | .some ⟨_, ⟨h₁⟩⟩ =>
        match f_β.fn_reduces level.succ.succ with
        | .some ⟨_, ⟨h₂⟩⟩ =>
          .some ⟨_, ⟨.pi h₁ h₂⟩⟩
        | _ => .none
      | _ => .none
  else
    if harity : f.arity = 1 then
      match _heq₃ : f.eta_reduce_tm level with
      | .some ⟨_f', ⟨h⟩⟩ =>
        .some ⟨_, ⟨.tm₁ heq harity h⟩⟩
      | .none => .some ⟨_, ⟨.tm'₁ heq harity (eta_reduce_tm_none _heq₃)⟩⟩
    else if harity : f.arity = 2 then
      match _heq₃ : f.eta_reduce_tm₂ level with
      | .some ⟨_f', ⟨h⟩⟩ =>
        .some ⟨_, ⟨.tm₂ heq harity h⟩⟩
      | .none => .some ⟨_, ⟨.tm'₂ heq harity (eta_reduce_tm₂_none _heq₃)⟩⟩
    else .none-/

@[grind =]
theorem none_tm_eta_reduces.{u} {τ_c : Type u} [DecidableEq τ_c] {f : GenericExpr (@EtaConst τ_c)} (h : ¬ ∃ f', TmEtaReduces level f f') : f.eta_reduce_tm level = .none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro ⟨_, ⟨h⟩⟩
  grind

@[aesop safe forward (rule_sets := [DccReduce])]
theorem FnEtaReduces.complete.{u} {τ_c : Type u} [DecidableEq τ_c]
  {f f' : GenericExpr (τ := EtaConst (τ := τ_c))}
  (h : FnEtaReduces level f f') : fn_reduces (τ_c := τ_c) level f = .some ⟨f', ⟨h⟩⟩ := by
  induction h
  case pi h₁ h₂ heq₁ heq₂ =>
    dsimp [fn_reduces]
    simp [tm_arity]
    simp_all
  case tm₁ harity h₁ =>
    have h₂ := h₁.complete
    unfold fn_reduces
    simp [harity]
    aesop
  case tm₂ harity h₁ =>
    have h₂ := h₁.complete
    unfold fn_reduces
    simp [harity]
    aesop
  /-case tm'₁ harity heq₂ =>
    unfold fn_reduces
    simp [harity]
    grind-/
  case tm'₂ harity heq₂ =>
    unfold fn_reduces
    simp [harity]
    grind

instance FnEtaReduces.instExistsDecidable.{u} {τ_c : Type u} [DecidableEq τ_c]
  {f : GenericExpr (τ := EtaConst (τ := τ_c))} : Decidable (∃ f', FnEtaReduces level f f') :=
  if heq : (f.fn_reduces level).isSome then
    .isTrue ⟨_, ((f.fn_reduces level).get heq).snd.down⟩
  else
    .isFalse (fun ⟨_, h⟩ => by
      have h := h.complete
      simp_all)

/-
New ToExpr is quite simple, since eta expr and expr are just

GenericExpr τ vs GenericExpr (EtaConst τ)
-/

inductive RedEta?.{u} {τ_c : Type u} [hdecEq : DecidableEq τ_c] [hBEq : BEq τ_c] : (e₁ : GenericExpr (τ := τ_c)) → (e₄ : GenericExpr (τ := τ_c)) → Prop
  | mk₁ : FnEtaReduces 0 (expr_to_eta e₁) e₃ → (hn : ¬ e₃.contains_hole) → RedEta? e₁ (eta_to_expr e₃ hn)
  | mk₂ : FnEtaReduces 0 (expr_to_eta e₁) e₃ → (hn : e₃.contains_hole)   → RedEta? e₁ e₁

@[grind .]
theorem fn_eta_reduces_none.{u} {τ_c : Type u} [DecidableEq τ_c] {e : GenericExpr (@EtaConst τ_c)} (heq : fn_reduces level e = .none) : ¬ ∃ e', FnEtaReduces level e e' :=
  fun ⟨_, h⟩ => by
    have heq := h.complete
    simp_all

def red_eta?.{u} {τ_c : Type u} [DecidableEq τ_c] (e₁ : GenericExpr τ_c) : Option ((e₄ : GenericExpr τ_c) × PLift (RedEta? e₁ e₄)) :=
  match (expr_to_eta e₁).fn_reduces 0 with
    | .some ⟨e', ⟨h₂⟩⟩ =>
      if h_contains : e'.contains_hole then
        .some ⟨_, ⟨.mk₂ h₂ h_contains⟩⟩
      else .some ⟨_, ⟨.mk₁ h₂ h_contains⟩⟩
    | .none => .none

@[aesop safe forward (rule_sets := [DccReduce])]
theorem RedEta?.complete.{u} {τ_c : Type u} [DecidableEq τ_c] {e e' : GenericExpr (τ := τ_c)} (h : RedEta? e e') : e.red_eta? = .some ⟨e', ⟨h⟩⟩ := by
  unfold red_eta?
  induction h
  case mk₁ h₁ h₂ | mk₂ h₁ h₂ =>
    have ha := h₁.complete
    have hh : ∃ e₃, FnEtaReduces 0 (expr_to_eta e) e₃ := ⟨_, h₁⟩
    grind

instance RedEta?.instDecidable.{u} {τ_c : Type u} [hdecEq : DecidableEq τ_c] {e : GenericExpr (τ := τ_c)} : Decidable (∃ e', RedEta? (hdecEq := hdecEq) e e') :=
  match heq : e.red_eta? with
  | .some ⟨_, ⟨h⟩⟩ => .isTrue ⟨_, h⟩
  | .none =>
    .isFalse (fun ⟨_, h⟩ => by
      have h := h.complete
      simp_all)

inductive RedEta??.{u} {τ_c : Type u} [DecidableEq τ_c] : (e : GenericExpr (τ := τ_c)) → (e' : GenericExpr (τ := τ_c)) → Prop
  | pi₁  : RedEta?? f_α f_α'
    → Domain (expr_to_eta f_α) δ
    → (hn : ¬ δ.contains_hole)
    → RedEta?? env env'
    → RedAffReflTrans (DCC? (f_β env)) f_β_env
    → IsNorm RedAff f_β_env
    → RedEta?? f_β_env f_β'
    → RedEta?? (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α', `(#(eta_to_expr δ hn), f_β')) env'))
  | coup  : RedEta?? β β' → RedEta?? (DCC? Coup(β)) (DCC? Coup(β'))
  | bang  : RedEta?? β β' → RedEta?? (DCC? !(β)) (DCC? !(β'))
  | pi₂  : RedEta?? f_α f_α'
    → RedEta?? f_β f_β'
    → RedEta?? (DCC? Π(f_α, f_β)) (DCC? Π(f_α', f_β'))
  | pi₃  : RedAffReflTrans (DCC? f_α) f_α₁
    → IsNorm RedAff f_α₁
    → RedEta?? (DCC? (f_α₁ ∘' g)) f_α'
    → RedAffReflTrans (DCC? f_β) f_β₁
    → IsNorm RedAff f_β₁
    → RedEta?? (DCC? (f_β₁ ∘' g)) f_β'
    → RedEta?? (DCC? (Π(f_α, f_β) ∘' g)) (DCC? Π(f_α', f_β'))
  | tm₁  : IsEtaTm e
    → RedEta? e e' → RedEta?? e e'
  | tm₂  : IsEtaTm e
    → (¬ ∃ e', RedEta? e e')
    → RedAffReflTrans e e'
    → IsNorm RedAff e'
    → RedEta?? e e

/-def RedEta??.transport {A B : GenericExpr Unit} (hr : RedEta?? A B) : RedEta?? A.expr_to_eta B.expr_to_eta := by
  induction hr
  · simp [expr_to_eta]
    
    sorry-/

theorem red_eta?_none.{u} {τ_c : Type u} [DecidableEq τ_c] {e : GenericExpr τ_c} (heq : red_eta? e = .none) : ¬ ∃ e', RedEta? e e' :=
  fun ⟨_, h⟩ => by
    have h := h.complete
    simp_all

@[dcc_force_reduce]
def red_eta??.{u} {τ_c : Type u} [DecidableEq τ_c] (e : GenericExpr τ_c) : Option ((e' : GenericExpr τ_c) × (PLift (RedEta?? e e'))) :=
  match e.view_eta? with
  | .some (.pi_type (f_α := f_α) (f_β := f_β) (env := env)) =>
    match f_α.expr_to_eta.domain? with
    | .some ⟨δ, ⟨h₂⟩⟩ =>
      have h_dec₁ : env.size < (DCC? (Π(f_α, f_β) env)).size := by
        grind
      have h_dec₂ : f_α.size < (DCC? (Π(f_α, f_β) env)).size := by
        grind
      have h_dec₂ : (DCC? (f_α env)).size < (DCC? (Π(f_α, f_β) env)).size := by
        grind
      have h_dec₃ : (reduce RedAff (DCC? (f_β env))).fst.size < (DCC? (Π(f_α, f_β) env)).size := by
        have h := (reduce RedAff (DCC? (f_β env))).snd.down
        have h_le : (reduce RedAff (DCC? (f_β env))).fst.size ≤ (DCC? (f_β env)).size :=
          red_aff_decreasing? h
        grind
      match env.red_eta??, f_α.red_eta??, (reduce RedAff (DCC? (f_β env))).fst.red_eta?? with
      | .some ⟨_, ⟨h₄⟩⟩, .some ⟨f_α', ⟨h₅⟩⟩, .some ⟨f_β', ⟨h₆⟩⟩ =>
        if h₃ : δ.contains_hole then
          .none
        else .some ⟨_, ⟨.pi₁ h₅ h₂ h₃ h₄ (reduce_sound rfl) (reduce_norm rfl) h₆⟩⟩
      | _, _, _ => .none
    | _ => .none
  | .some (.pi (f_α := f_α) (f_β := f_β)) =>
    have h_dec₁ : f_α.size < (DCC? Π(f_α, f_β)).size := by
      grind
    have h_dec₂ : f_β.size < (DCC? Π(f_α, f_β)).size := by
      grind
    match f_α.red_eta??, f_β.red_eta?? with
    | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, ⟨h₂⟩⟩ => .some ⟨_, ⟨.pi₂ h₁ h₂⟩⟩
    | _, _ => .none
  | .some (.pi_comp (f_α := f_α) (f_β := f_β) (g := g)) =>
    have h_dec₁ : (reduce RedAff f_α).fst.size ≤ f_α.size :=
      decreasing? _ (reduce RedAff f_α).snd.down
    have h_dec₂ : (reduce RedAff f_β).fst.size ≤ f_β.size :=
      decreasing? _ (reduce RedAff f_β).snd.down
    have h_dec₃ : (DCC? (#((reduce RedAff f_α).fst) ∘' g)).size < (DCC? Π(f_α, f_β) ∘' g).size := by
      grind
    have h_dec₄ : (DCC? (#((reduce RedAff f_β).fst) ∘' g)).size < (DCC? Π(f_α, f_β) ∘' g).size := by
      grind
    match (DCC? (#((reduce RedAff f_α).fst) ∘' g)).red_eta??, (DCC? (#((reduce RedAff f_β).fst) ∘' g)).red_eta?? with
    | .some ⟨f_α', ⟨h₁⟩⟩, .some ⟨f_β', ⟨h₂⟩⟩ =>
      .some ⟨_, ⟨.pi₃ (reduce_sound rfl) (reduce_norm rfl)
        h₁ (reduce_sound rfl) (reduce_norm rfl)  h₂⟩⟩
    | _, _ => .none
  | .some (.coup (β := β)) =>
    have h_dec : β.size < (DCC? Coup(β)).size := by
      grind
    match β.red_eta?? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.coup h⟩⟩
    | _ => .none
  | .some (.bang (β := β)) =>
    have h_dec : β.size < (DCC? !(β)).size := by
      grind
    match β.red_eta?? with
    | .some ⟨_, ⟨h⟩⟩ =>
      .some ⟨_, ⟨.bang h⟩⟩
    | _ => .none
  | .none =>
    match e.is_eta_tm? with
    | .some h_tm =>
      match _heq₄ : e.red_eta? with
      | .some ⟨_, ⟨h⟩⟩ =>
        .some ⟨_, ⟨.tm₁ h_tm h⟩⟩
      | .none => .some ⟨_, ⟨.tm₂ h_tm (red_eta?_none _heq₄) (reduce_sound rfl) (reduce_norm rfl)⟩⟩
    | .none => .none
termination_by e.size

theorem red_eta??_sound.{u} {τ_c : Type u} [DecidableEq τ_c] {e e' : GenericExpr τ_c} {h : RedEta?? e e'} (_hr : red_eta?? e = .some ⟨e', ⟨h⟩⟩) : RedEta?? e e' := h

/-def red_eta??.{u} {τ_c : Type u} [DecidableEq τ_c] (e : GenericExpr τ_c) : Option ((e' : GenericExpr τ_c) × (PLift (RedEta?? e e'))) :=
  if heq : ∃ f_α f_β env, e = (DCC? (Π(f_α, f_β) env)) then
    match e with
    | (DCC? (Π(f_α, f_β) env)) =>
      match f_α.expr_to_eta.domain? with
      | .some ⟨δ, ⟨h₂⟩⟩ =>
        have h_dec₁ : env.size < (DCC? (Π(f_α, f_β) env)).size := by
          grind
        have h_dec₂ : f_α.size < (DCC? (Π(f_α, f_β) env)).size := by
          grind
        have h_dec₂ : (DCC? (f_α env)).size < (DCC? (Π(f_α, f_β) env)).size := by
          grind
        have h_dec₃ : (reduce RedAff (DCC? (f_β env))).fst.size < (DCC? (Π(f_α, f_β) env)).size := by
          have h := (reduce RedAff (DCC? (f_β env))).snd.down
          have h_le : (reduce RedAff (DCC? (f_β env))).fst.size ≤ (DCC? (f_β env)).size :=
            red_aff_decreasing? h
          grind
        match env.red_eta??, f_α.red_eta??, (reduce RedAff (DCC? (f_β env))).fst.red_eta?? with
        | .some ⟨_, ⟨h₄⟩⟩, .some ⟨f_α', ⟨h₅⟩⟩, .some ⟨f_β', ⟨h₆⟩⟩ =>
          if h₃ : δ.contains_hole then
            .none
          else
            if heq : f_β' = (DCC? (f_β env)) then
              .some ⟨_, ⟨.pi₁' h₅ h₂ h₃ h₄ (reduce_sound rfl) (reduce_norm rfl) h₆ heq⟩⟩
            else
              .some ⟨_, ⟨.pi₁ h₅ h₂ h₃ h₄ (reduce_sound rfl) (reduce_norm rfl) h₆ heq⟩⟩
        | _, _, _ => .none
      | _ => .none
  else
    if heq₂ : ∃ f_α f_β, e = (DCC? Π(f_α, f_β)) then
      match e with
      | (DCC? Π(f_α, f_β)) =>
        have h_dec₁ : f_α.size < (DCC? Π(f_α, f_β)).size := by
          grind
        have h_dec₂ : f_β.size < (DCC? Π(f_α, f_β)).size := by
          grind
        match f_α.red_eta??, f_β.red_eta?? with
        | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, ⟨h₂⟩⟩ => .some ⟨_, ⟨.pi₂ h₁ h₂⟩⟩
        | _, _ => .none
    else
      if heq₂' : ¬ (∃ g f_α f_β, e = (DCC? Π(f_α, f_β) ∘' g)) then
        if heq₂'' : ∃ β, e = (DCC? Coup(β)) then
          match e with
          | (DCC? Coup(β)) =>
            have h_dec : β.size < (DCC? Coup(β)).size := by
              grind
            match β.red_eta?? with
            | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.coup h⟩⟩
            | _ => .none
          | _ => .none
        else
          if heq₂''' : ∃ α, e = (DCC? !(α)) then
            match e with
            | DCC? !(β) =>
              have h_dec : β.size < (DCC? !(β)).size := by
                grind
              match β.red_eta?? with
              | .some ⟨_, ⟨h⟩⟩ =>
                .some ⟨_, ⟨.bang h⟩⟩
              | _ => .none
          else
            match _heq₄ : e.red_eta? with
            | .some ⟨_, ⟨h⟩⟩ =>
              .some ⟨_, ⟨.tm₁ heq heq₂ heq₂' heq₂'' heq₂''' h⟩⟩
            | .none => .some ⟨_, ⟨.tm₂ heq heq₂ heq₂' heq₂'' heq₂''' (red_eta?_none _heq₄) (reduce_sound rfl) (reduce_norm rfl)⟩⟩
      else
        match e with
        | (DCC? (Π(f_α, f_β) ∘' g)) =>
          have h_dec₁ : (reduce RedAff f_α).fst.size ≤ f_α.size :=
            decreasing? _ (reduce RedAff f_α).snd.down
          have h_dec₂ : (reduce RedAff f_β).fst.size ≤ f_β.size :=
            decreasing? _ (reduce RedAff f_β).snd.down
          have h_dec₃ : (DCC? (#((reduce RedAff f_α).fst) ∘' g)).size < (DCC? Π(f_α, f_β) ∘' g).size := by
            grind
          have h_dec₄ : (DCC? (#((reduce RedAff f_β).fst) ∘' g)).size < (DCC? Π(f_α, f_β) ∘' g).size := by
            grind
          match (DCC? (#((reduce RedAff f_α).fst) ∘' g)).red_eta??, (DCC? (#((reduce RedAff f_β).fst) ∘' g)).red_eta?? with
          | .some ⟨f_α', ⟨h₁⟩⟩, .some ⟨f_β', ⟨h₂⟩⟩ =>
            .some ⟨_, ⟨.pi₃ (reduce_sound rfl) (reduce_norm rfl)
              h₁ (reduce_sound rfl) (reduce_norm rfl)  h₂⟩⟩
          | _, _ => .none
        | _ => .none
termination_by e.size-/

@[aesop safe forward (rule_sets := [DccReduce])]
theorem RedEta??.complete.{u} {τ_c : Type u} [DecidableEq τ_c] {e e' : GenericExpr (τ := τ_c)} (h : RedEta?? e e') : e.red_eta?? = .some ⟨e', ⟨h⟩⟩ := by
  induction h
  case pi₁ =>
    rename_i f_α δ δ' env env' f_β f_β_env f_β' h₁ to_eta_expr h_domain h_to_expr h₃ hrenv hnenv h₄ hneq heq₁ heq₂
    have heq₄ := reduce_complete hrenv hnenv
    have heq₅ : (reduce RedAff (f_β_env.app env')).fst = f_β' := by
      simp_all
    unfold red_eta??
    simp
    simp [view_eta?, h_domain.complete, heq₁]
    cases heq₅
    cases heq₄
    simp_all
  case pi₂ =>
    rename_i f_α f_α' f_β f_β' h₁ h₂ heq₁ heq₂
    unfold red_eta??
    simp
    simp [view_eta?, heq₁, heq₂]
  case tm₁ e₀ e'' hn h =>
    have ha := IsEtaTm.complete_view_eta hn
    have hb := hn.complete
    have he : ∃ e', RedEta? e₀ e' := by
      exact ⟨_, h⟩
    have h₁ := h.complete
    unfold red_eta??
    rw [ha]
    simp [hb]
    grind
  case tm₂ hn₁ hn₂ hr hnorm =>
    have ha := IsEtaTm.complete_view_eta hn₁
    have hb := hn₁.complete
    have h₁ := reduce_complete hr hnorm
    rw [red_eta??]
    simp
    rw [ha]
    simp [hb]
    grind
  case pi₃ hrt₁ hn₁ hr₁ hrt₂ hn₂ hr₂ heq₁ heq₂ =>
    have heq₃ := reduce_complete hrt₁ hn₁
    have heq₄ := reduce_complete hrt₂ hn₂
    have heq₅ := reduce_complete_fst hrt₁ hn₁
    have heq₆ := reduce_complete_fst hrt₂ hn₂
    cases heq₅; cases heq₆
    unfold red_eta??
    simp_all [view_eta?]
  case coup hr₁ heq₁ =>
    unfold red_eta??
    simp [view_eta?, heq₁]
  case bang hr₁ heq₁ =>
    unfold red_eta??
    simp [view_eta?, heq₁]

instance RedEta??.instDecidable.{u} {τ_c : Type u} [DecidableEq τ_c] {e : GenericExpr τ_c}: Decidable (∃ e', RedEta?? (τ_c := τ_c) e e') :=
  match heq : e.red_eta?? with
  | .some ⟨_, ⟨h⟩⟩ => .isTrue ⟨_, h⟩
  | .none =>
    .isFalse (fun ⟨_, h⟩ => by
      have h := h.complete
      simp_all)

inductive RedEta₂.{u} {τ_c : Type u} [DecidableEq τ_c] : GenericExpr τ_c → GenericExpr τ_c → Prop
  | refl : (¬ ∃ e', RedEta?? e e') → RedEta₂ e e
  | step : RedEta?? e e' → RedEta₂ e e'

def red_eta.{u} {τ_c : Type u} [DecidableEq τ_c] (e : GenericExpr τ_c) : ((e' : GenericExpr τ_c) × (PLift (RedEta₂ e e'))) :=
  match heq₂ : e.red_eta?? with
  | .some ⟨_, ⟨h⟩⟩ => ⟨_, ⟨.step h⟩⟩
  | .none => ⟨_, ⟨.refl (fun ⟨_, h⟩ => by
    have h := h.complete
    simp_all)⟩⟩

theorem RedEta₂.complete.{u} {τ_c : Type u} [DecidableEq τ_c] {e e' : GenericExpr τ_c} (h : RedEta₂ e e') : e.red_eta = ⟨e', ⟨h⟩⟩ := by
  cases h
  case refl hn =>
    unfold red_eta
    split
    case h_1 hr _ => exact (hn ⟨_, hr⟩).elim
    · rfl
  case step h =>
    have h := h.complete
    simp [red_eta]
    split
    case h_1 =>
      simp_all
      grind
    · simp_all

/-
Top-level Π rule:

If Domain f_α = δ
and f_β env η-reduces to f_β', then

f_β' = `(δ, f_β')
-/

@[dcc_force_reduce]
theorem reduce_eta_sound.{u} {τ_c : Type u} [DecidableEq τ_c] {e e' : GenericExpr τ_c} {h : RedEta₂ e e'} (_heq : red_eta e = ⟨e', ⟨h⟩⟩) : RedEta₂ e e' := h

@[dcc_force_reduce]
abbrev red_eta'₂.{u} {τ_c : Type u} [DecidableEq τ_c] (e : GenericExpr τ_c) : GenericExpr τ_c := e.red_eta.fst

#eval (DCC Id(Sort 1) ∘' Id(Sort 1)).red_eta.fst
#eval (DCC `(Sort 1, Sort 1)).red_eta.fst
#eval (DCC Id(Sort 1)).red_eta.fst
#eval (DCC Λ(Sort 1, Id(Sort 1), Id(Coup(Id(Sort 1))) ∘' Id(Coup(Id(Sort 1))))).red_eta.fst
#eval (DCC (Λ(Sort 1, Id(Sort 1), Sndc(Coup(Id(Sort 1)))) (Sort 0))).red_eta.fst
#eval (DCC Eql(Id(Sort 2))).red_eta.fst
#eval (DCC Eql(Id(Sort 2))).red_eta.fst
#eval (DCC ((Sort 0 : Sort 1) → Sort 2)).raw_repr
#eval (DCC (Λ(Sort 1, `(Sort 1, Sort 2), `(Coup(`(Sort 1, Sort 2)), (Sort 3))))).red_eta.fst
#eval (DCC (Π(Id(Sort 3) ∘' Id(Sort 3), `(Sort 3, Π(!<Id(Sort 2)>, Eql(Id(Sort 2))))) !(Sort 2))).red_eta.fst
#eval (DCC (Π(Id(Sort 3) ∘' Id(Sort 3), `(Sort 3, Π(!<Id(Sort 2)>, Eql(Id(Sort 2)))) ∘' Id(Sort 3)) !(Sort 2))).red_eta.fst

end GenericExpr

open GenericExpr in
instance : GenericExpr τ ≃ { x : GenericExpr (@EtaConst τ) // ¬ contains_hole x} where
  toFun       := (⟨·.expr_to_eta, to_eta_no_hole⟩)
  invFun      := fun ⟨x, hn⟩ => eta_to_expr x hn
  left_inv  x := by simp [to_eta_left_inv]
  right_inv x := by simp [to_eta_right_inv]

namespace GenericExpr

namespace EtaMap

def is_norm_aff.{u} {τ_c : Type u} [DecidableEq τ_c]
  {dom out hole_arg f' : GenericExpr (@EtaConst τ_c)}
  (hr : EtaMap (τ_c := τ_c) dom out hole_arg f') (hn : IsNorm RedAff out) : IsNorm RedAff f' := by
  induction hr
  any_goals (
    focus
    intro ⟨_, h⟩
    cases h
    done)
  · exact hn.congrFun

end EtaMap

namespace EtaResult

def is_norm_aff.{u} {τ_c : Type u} [DecidableEq τ_c]
  {dom out hole_arg f' : GenericExpr (@EtaConst τ_c)}
  (hr : EtaResult (τ_c := τ_c) dom out hole_arg f') (hn : IsNorm RedAff out) : IsNorm RedAff f' :=
  match hr with
  | .map h_contains hr =>
    hr.is_norm_aff hn
  | .quot h_contains => by
    intro ⟨_, h⟩
    cases h

end EtaResult

namespace IsNorm

@[grind ., grind =>]
theorem norm_coup_fn (hn : IsNorm RedAff (DCC? (f ⟦β⟧(x, y)))) : IsNorm RedAff (DCC? (f ⟦β₂⟧(x, y))) := by
  intro ⟨_, hr⟩
  cases hr
  any_goals (
    focus
    apply hn
    constructor
    constructor
    done)
  · exact hn.congrFun ⟨_, by assumption⟩
  case congrArg h =>
    cases h with
    | sigl hr => exact hn.congrArg.sigl ⟨_, hr⟩
    | sigr hr => exact hn.congrArg.sigr ⟨_, hr⟩

end IsNorm

namespace TmEtaReduces

/-
β does not matter in functions of Coup


-/

def is_norm_aff.{u} {τ_c : Type u} [DecidableEq τ_c]
  {f f' : GenericExpr (@EtaConst τ_c)}
  (hr₁ : TmEtaReduces level f f') : IsNorm RedAff f' :=
  match hr₁ with
  | .coupl _hrt₁ _hn₁ _h_domain _hrt₂ hn₂ hr₂
  | .tm _hrt₁ _hn₁ _h_domain _hneq₁ _hrt₂ hn₂ hr₂
  | .bang₁ _hrt₁ _hn₁ _h_domain _hrt₂ hn₂ hr₂
    => hr₂.is_norm_aff hn₂

end TmEtaReduces

namespace EtaMap₂

def is_norm_aff.{u} {τ_c : Type u} [DecidableEq τ_c]
  {dom₁ dom₂ out hole₁ hole₂ f' : GenericExpr (@EtaConst τ_c)}
  (hr : EtaMap₂ (τ_c := τ_c) dom₁ dom₂ out hole₁ hole₂ f') (hn : IsNorm RedAff out) : IsNorm RedAff f' := by
  induction hr
  any_goals (
    focus
    intro ⟨_, h⟩
    cases h
    done)
  case par => exact hn.congrFun.congrFun

end EtaMap₂

namespace TmEtaReduces₂

def is_norm_aff.{u} {τ_c : Type u} [DecidableEq τ_c]
  {f f' : GenericExpr (@EtaConst τ_c)}
  (hr₁ : TmEtaReduces₂ level f f') : IsNorm RedAff f' := by
  cases hr₁
  any_goals (
    focus
    intro ⟨_, h⟩; cases h
    done)
  case map hneq₁ hneq₂ hn₁ h_contains h_domain hrt₁ hr₂ =>
    exact hr₂.is_norm_aff hn₁

end TmEtaReduces₂

namespace FnEtaReduces

def is_norm_aff.{u} {τ_c : Type u} [DecidableEq τ_c]
  {f f' : GenericExpr (@EtaConst τ_c)}
  (hn_contains : ¬ f.contains_hole)
  (hr : FnEtaReduces level f f') (hn : IsNorm RedAff f) : IsNorm RedAff f' := by
  have hn' := hn.to_eta
  induction hr
  case pi hr₁ hr₂ ih₁ ih₂ =>
    have ha := ih₁ (by simp_all [contains_hole]) hn.pil (by
      simp [expr_to_eta] at hn'
      exact hn'.pil)
    have hb := ih₂ (by simp_all [contains_hole]) hn.pir (by
      simp [expr_to_eta] at hn'
      exact hn'.pir)
    intro ⟨_, h⟩
    cases h with
    | pil hr => exact ha ⟨_, hr⟩
    | pir hr => exact hb ⟨_, hr⟩
  case tm₁ heq harity hr => exact hr.is_norm_aff
  case tm₂ hneq harity hr => exact hr.is_norm_aff
  any_goals assumption

end FnEtaReduces

namespace RedEta?

def is_norm_aff.{u} {τ_c : Type u} [DecidableEq τ_c] {A B : GenericExpr τ_c}
  (hr : RedEta? A B) (hn : IsNorm RedAff A) : IsNorm RedAff B := by
  have hn' := hn.to_eta
  induction hr
  case mk₁ hr h_contains =>
    exact (hr.is_norm_aff to_eta_no_hole hn').from_eta h_contains
  · assumption

end RedEta?

namespace RedEta??

def is_norm_aff.{u} {τ_c : Type u} [DecidableEq τ_c] {A B : GenericExpr τ_c}
  (hr : RedEta?? A B) (hn : IsNorm RedAff A) : IsNorm RedAff B := by
  have hn' := hn.to_eta
  induction hr
  case pi₁ ih₁ ih₂ ih₃ =>
    have ha := ih₁ hn.congrFun.pil hn.congrFun.pil.to_eta
    have hb := ih₂ hn.congrArg hn.congrArg.to_eta
    have hc := ih₃ (by assumption) (.to_eta (by assumption))
    intro ⟨_, h⟩
    cases h with
    | congrFun h =>
      cases h with
      | pil h => exact ha ⟨_, h⟩
      | pir h => cases h
    | congrArg h => exact hb ⟨_, h⟩
  case bang ih | coup ih =>
    have ha := ih (fun ⟨_, h⟩ => hn ⟨_, by constructor; exact h⟩)
      (IsNorm.to_eta (fun ⟨_, h⟩ => hn ⟨_, by constructor; exact h⟩))
    intro ⟨_, h⟩
    cases h
    · rename_i h
      exact ha ⟨_, h⟩
  case pi₂ ih₁ ih₂ =>
    have ha := ih₁ hn.pil hn.pil.to_eta
    have hb := ih₂ hn.pir hn.pir.to_eta
    intro ⟨_, h⟩
    cases h with
    | pil h => exact ha ⟨_, h⟩
    | pir h => exact hb ⟨_, h⟩
  case pi₃ ih₁ ih₂ =>
    have ha := ih₁ (fun ⟨_, h⟩ => by cases h) (.to_eta (fun ⟨_, h⟩ => by cases h))
    have hb := ih₂ (fun ⟨_, h⟩ => by cases h) (.to_eta (fun ⟨_, h⟩ => by cases h))
    intro ⟨_, h⟩
    cases h with
    | pil h => exact ha ⟨_, h⟩
    | pir h => exact hb ⟨_, h⟩
  case tm₁ hneq₁ hr =>
    exact hr.is_norm_aff hn
  · assumption

end RedEta??

namespace RedEta₂

def is_norm_aff.{u} {τ_c : Type u} [DecidableEq τ_c] {A B : GenericExpr τ_c}
  (hr : RedEta₂ A B) (hn : IsNorm RedAff A) : IsNorm RedAff B :=
  match hr with
  | .refl hneq => hn
  | .step h    => h.is_norm_aff hn

@[aesop safe destruct (rule_sets := [DccReduce])]
def unique.{u} {τ_c : Type u} [DecidableEq τ_c] {A B C : GenericExpr τ_c}
  (hr₁ : RedEta₂ A B) (hr₂ : RedEta₂ A C) : B = C := by
  have ha := hr₁.complete
  have hb := hr₂.complete
  simp_all

end RedEta₂

namespace RedEta??

@[aesop safe destruct (rule_sets := [DccReduce])]
def unique.{u} {τ_c : Type u} [DecidableEq τ_c] {A B C : GenericExpr τ_c}
  (hr₁ : RedEta?? A B) (hr₂ : RedEta?? A C) : B = C := by
  have ha := hr₁.complete
  have hb := hr₂.complete
  simp_all

end RedEta??

end GenericExpr
