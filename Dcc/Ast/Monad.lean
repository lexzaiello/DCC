import Dcc.Attrs
import Dcc.Ast.Core

@[dcc_rel]
def GenericExpr.bind.{u, v} {α : Type u} {β : Type v} (x : GenericExpr α) (f : α → GenericExpr β) : GenericExpr β := by
  cases x
  · exact .top
  · exact .bot
  · exact .tintro
  · exact .sort (by assumption)
  case map x =>
    exact .map (x.bind f)
  case fmap x =>
    exact .fmap (x.bind f)
  case bang x =>
    exact .bang (x.bind f)
  case box x =>
    exact .box (x.bind f)
  case unmap x =>
    exact .unmap (x.bind f)
  case unbox x =>
    exact .unbox (x.bind f)
  case eql x =>
    exact .eql (x.bind f)
  case refl x =>
    exact .refl (x.bind f)
  case fstc x =>
    exact .fstc (x.bind f)
  case sndc x =>
    exact .sndc (x.bind f)
  case id x =>
    exact .id (x.bind f)
  case eval x y z =>
    exact .eval (x.bind f) (y.bind f) (z.bind f)
  case curr x y z =>
    exact .curr (x.bind f) (y.bind f) (z.bind f)
  case curr' x y z =>
    exact .curr' (x.bind f) (y.bind f) (z.bind f)
  case pair x y z =>
    exact .pair (x.bind f) (y.bind f) (z.bind f)
  case mkc x y z =>
    exact .mkc (x.bind f) (y.bind f) (z.bind f)
  case eq x y =>
    exact .eq (x.bind f) (y.bind f)
  case comp x y =>
    exact .comp (x.bind f) (y.bind f)
  case comp' x y =>
    exact .comp' (x.bind f) (y.bind f)
  case comp₂ x y =>
    exact .comp₂ (x.bind f) (y.bind f)
  case quot x y =>
    exact .quot (x.bind f) (y.bind f)
  case pi x y =>
    exact .pi (x.bind f) (y.bind f)
  case sigma x y =>
    exact .sigma (x.bind f) (y.bind f)
  case coup x =>
    exact .coup (x.bind f)
  case app x y =>
    exact .app (x.bind f) (y.bind f)
  case const x => exact (f x)

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
def GenericExpr.functor_map (f : α → β) (x : GenericExpr α) : GenericExpr β := by
  cases x
  · exact .top
  · exact .bot
  · exact .tintro
  · exact .sort (by assumption)
  case map x =>
    exact .map (x.functor_map f)
  case fmap x =>
    exact .fmap (x.functor_map f)
  case bang x =>
    exact .bang (x.functor_map f)
  case box x =>
    exact .box (x.functor_map f)
  case unmap x =>
    exact .unmap (x.functor_map f)
  case unbox x =>
    exact .unbox (x.functor_map f)
  case eql x =>
    exact .eql (x.functor_map f)
  case refl x =>
    exact .refl (x.functor_map f)
  case fstc x =>
    exact .fstc (x.functor_map f)
  case sndc x =>
    exact .sndc (x.functor_map f)
  case id x =>
    exact .id (x.functor_map f)
  case eval x y z =>
    exact .eval (x.functor_map f) (y.functor_map f) (z.functor_map f)
  case curr x y z =>
    exact .curr (x.functor_map f) (y.functor_map f) (z.functor_map f)
  case curr' x y z =>
    exact .curr' (x.functor_map f) (y.functor_map f) (z.functor_map f)
  case pair x y z =>
    exact .pair (x.functor_map f) (y.functor_map f) (z.functor_map f)
  case mkc x y z =>
    exact .mkc (x.functor_map f) (y.functor_map f) (z.functor_map f)
  case eq x y =>
    exact .eq (x.functor_map f) (y.functor_map f)
  case comp x y =>
    exact .comp (x.functor_map f) (y.functor_map f)
  case comp' x y =>
    exact .comp' (x.functor_map f) (y.functor_map f)
  case comp₂ x y =>
    exact .comp₂ (x.functor_map f) (y.functor_map f)
  case quot x y =>
    exact .quot (x.functor_map f) (y.functor_map f)
  case pi x y =>
    exact .pi (x.functor_map f) (y.functor_map f)
  case sigma x y =>
    exact .sigma (x.functor_map f) (y.functor_map f)
  case coup x =>
    exact .coup (x.functor_map f)
  case app x y =>
    exact .app (x.functor_map f) (y.functor_map f)
  case const x => exact .const (f x)

instance GenericExpr.instMonad.{u} : Monad.{u, u} GenericExpr.{u} where
  map  := GenericExpr.functor_map
  pure := .const
  bind := GenericExpr.bind

def GenericExpr.id_map.{u} {α : Type u} (x : GenericExpr α) : _root_.id <$> x = x := by
  induction x
  case top | bot | tintro | sort =>
    dcc_simp_all [Functor.map, dcc_rel]
  any_goals (
    simp_all [Functor.map]
    dsimp [GenericExpr.functor_map] at *
    aesop)
  · simp [Functor.map, dcc_rel]

def GenericExpr.comp_map.{u} {α β γ : Type u} (g : α → β) (h : β → γ) (x : GenericExpr α) : (h ∘ g) <$> x = h <$> g <$> x := by
  induction x
  case top | bot | tintro | sort =>
    dcc_simp_all [Functor.map, dcc_rel]
  any_goals (
    simp_all [Functor.map]
    dsimp [GenericExpr.functor_map] at *
    aesop)
  · simp [Functor.map, dcc_rel]

def GenericExpr.seqRight_eq.{u} {α β : Type u} (x : GenericExpr α) (y : GenericExpr β) : x *> y = Function.const α _root_.id <$> x <*> y := by
  simp [Functor.map, SeqRight.seqRight, Seq.seq]
  induction x
  any_goals (dsimp [GenericExpr.bind, functor_map])
  any_goals (
    focus
    rename_i ih
    induction y
    any_goals (
      focus
      dsimp [functor_map] at ih
      simp [ih]
      dsimp [functor_map]
      done))
  any_goals (
    rename_i ih₁ ih₂ ih₃
    induction y
    any_goals (grind))
  case const x =>
    induction y
    any_goals (dsimp [functor_map] at *; try grind)

def GenericExpr.seqLeft_eq.{u} {α β : Type u} (x : GenericExpr α) (y : GenericExpr β) : x <* y = Function.const β <$> x <*> y := by
  simp [Functor.map, SeqLeft.seqLeft, Seq.seq]
  induction x
  any_goals (dsimp [GenericExpr.bind, functor_map])
  any_goals (
    focus
    rename_i ih
    induction y
    any_goals (
      focus
      dsimp [functor_map] at ih
      simp [ih]
      dsimp [functor_map]
      done))
  any_goals (
    focus
    induction y
    any_goals (simp_all))
  case const x =>
    induction y
    case top | bot | tintro | sort =>
      simp [GenericExpr.bind, functor_map]
    any_goals (
      focus
      dsimp [GenericExpr.bind, functor_map]
      simp_all)
    · dsimp [GenericExpr.bind, functor_map]

instance GenericExpr.instLawfulMonad.{u} : LawfulMonad.{u, u} GenericExpr.{u} where
  id_map := GenericExpr.id_map
  map_const {α β} := by constructor
  comp_map := GenericExpr.comp_map
  seqLeft_eq := GenericExpr.seqLeft_eq
  seqRight_eq := GenericExpr.seqRight_eq
  pure_seq {α β} g x := by
    simp [Pure.pure]
    change _ = GenericExpr.functor_map _ _
    simp [Seq.seq, GenericExpr.bind]
  bind_pure_comp {α β} f x := by
    change (GenericExpr.bind x (fun a => Pure.pure (f a))) = GenericExpr.functor_map _ _
    simp [Pure.pure]
    induction x
    any_goals (dsimp [GenericExpr.bind, functor_map])
    any_goals (
      simp [*])
  bind_map {α β} f x := by
    change (GenericExpr.bind f (fun x_1 => GenericExpr.functor_map x_1 x)) = _
    induction x
    any_goals (simp [Seq.seq])
  pure_bind {α β} x f := by
    change GenericExpr.bind (const _) _ = _
    simp [GenericExpr.bind]
  bind_assoc {α β γ} x f g := by
    change (GenericExpr.bind (GenericExpr.bind x f) g) = GenericExpr.bind x (fun x => GenericExpr.bind (f x) g)
    induction x
    any_goals (dsimp [GenericExpr.bind] at *; try simp [*])

instance : Functor GenericExpr where
  map := GenericExpr.functor_map

instance : LawfulFunctor GenericExpr where
  id_map {α} x := by
    induction x
    case top | bot | tintro | sort =>
      dcc_simp_all [Functor.map, dcc_rel]
    any_goals (
      simp_all [Functor.map]
      dsimp [GenericExpr.functor_map] at *
      aesop)
    · simp [Functor.map, dcc_rel]
  map_const {α β} := by constructor
  comp_map {α β γ} g h x := by
    induction x
    case top | bot | tintro | sort =>
      dcc_simp_all [Functor.map, dcc_rel]
    any_goals (
      simp_all [Functor.map]
      dsimp [GenericExpr.functor_map] at *
      aesop)
    · simp [Functor.map, dcc_rel]
