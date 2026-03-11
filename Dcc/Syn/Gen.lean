import Dcc.Syn.JudgePi
import Qq
import Lean
import Lean.Elab

open Lean (Level)

open Expr

inductive ParRed' : Expr → Expr → Type where
  | refl_K'     : ParRed' (K' m n) (K' m n)
  | refl_K      : ParRed' (K m n) (K m n)
  | refl_S      : ParRed' (S m n o) (S m n o)
  | refl_I      : ParRed' (I m) (I m)
  | refl_hole   : ParRed' (_?) (_?)
  | refl_Srt    : ParRed' (Srt m) (Srt m)
  | refl_next   : ParRed' next next
  | refl_read   : ParRed' read read
  | refl_assert : ParRed' assert assert
  | refl_app'   : ParRed' $ $
  | I           : ParRed' x x' → ParRed' ⸨(I _m) _α x⸩ x'
  | K           : ParRed' x x' → ParRed' ⸨(K _m _n) _α _β x _y⸩ x'
  | K'          : ParRed' x x' → ParRed' ⸨(K' _m _n) _α _β x _y⸩ x'
  | S           : ParRed' x x' → ParRed' y y' → ParRed' z z'
    → ParRed' ⸨(S _m _n _o) _α _β _γ x y z⸩ ⸨⸨x' z'⸩ ⸨y' z'⸩⸩
  | Pi          : ParRed' α α' → ParRed' β β' → ParRed' x x'
    → ParRed' ⸨((Π' m) α, β) x⸩ ((Π' m) ⸨α' x'⸩, ⸨β' x'⸩)
  | Pival       : ParRed' α α' → ParRed' β β' → ParRed' ((Π' m) α, β) ((Π' m) α', β')
  | next        : ParRed' f f' → ParRed' ⸨next f _x⸩ f'
  | read        : ParRed' e e' → ParRed' ⸨read e⸩ e'
  | assert      : ParRed' e e' → ParRed' ⸨assert e _x⸩ e'
  | app'        : ParRed' f f' → ParRed' g g' → ParRed' x x'
    → ParRed' ⸨${π} f g x⸩ ⸨π ⸨f' x'⸩ ⸨g' x'⸩⸩
  | app         : ParRed' f f'
    → ParRed' x x'
    → ParRed' ⸨f x⸩ ⸨f' x'⸩
deriving Repr

inductive Red' : Expr → Expr → Type
  | I      : Red' ⸨(I _m) _α x⸩ x
  | K      : Red' ⸨(K _m _n) _α _β x _y⸩ x
  | K'     : Red' ⸨(K' _m _n) _α _β x _y⸩ x
  | S      : Red' ⸨(S _m _n _o) _α _β _γ x y z⸩ ⸨⸨x z⸩ ⸨y z⸩⸩
  | Pi     : Red' ⸨((Π' m) α, β) x⸩ ((Π' m) ⸨α x⸩, ⸨β x⸩)
  | next   : Red' ⸨next f _x⸩ f
  | read   : Red' ⸨read e⸩ e
  | assert : Red' ⸨assert e _x⸩ e
  | app'   : Red' ⸨${π} f g x⸩ ⸨π ⸨f x⸩ ⸨g x⸩⸩

def gen (e : Expr) : (e' : Expr) × (ParRed' e e') :=
  match e with
  | ⸨⸨(.I _m) _α⸩ x⸩ =>
    let ⟨x', h⟩ := gen x
    ⟨x', .I h⟩
  | ⸨(.K _m _n) _α _β x _y⸩ =>
    let ⟨x', h⟩ := gen x
    ⟨x', .K h⟩
  | ⸨(.K' _m _n) _α _β x _y⸩ =>
    let ⟨x', h⟩ := gen x
    ⟨x', .K' h⟩
  | ⸨(.S _m _n _o) _α _β _γ x y z⸩ =>
    let ⟨x', h₁⟩ := gen x
    let ⟨y', h₂⟩ := gen y
    let ⟨z', h₃⟩ := gen z
    ⟨⸨⸨x' z'⸩ ⸨y' z'⸩⸩, .S h₁ h₂ h₃⟩
  | ⸨((Π' m) α, β) x⸩ =>
    let ⟨α', h₁⟩ := gen α
    let ⟨β', h₂⟩ := gen β
    let ⟨x', h₃⟩ := gen x
    ⟨((Π' m) ⸨α' x'⸩, ⸨β' x'⸩), .Pi h₁ h₂ h₃⟩
  | ((Π' m) α, β) =>
    let ⟨α', h₁⟩ := gen α
    let ⟨β', h₂⟩ := gen β
    ⟨(Π' m) α', β', .Pival h₁ h₂⟩
  | ⸨.next f _x⸩ =>
    let ⟨f', h₁⟩ := gen f
    ⟨f', .next h₁⟩
  | ⸨.read e⸩ =>
    let ⟨e', h₁⟩ := gen e
    ⟨e', .read h₁⟩
  | ⸨.assert f _x⸩ =>
    let ⟨f', h₁⟩ := gen f
    ⟨f', .assert h₁⟩
  | ⸨${π} f g x⸩ =>
    let ⟨f', h₁⟩ := gen f
    let ⟨g', h₂⟩ := gen g
    let ⟨x', h₃⟩ := gen x
    ⟨⸨π ⸨f' x'⸩ ⸨g' x'⸩⸩, .app' h₁ h₂ h₃⟩
  | ⸨f x⸩ =>
    let ⟨f', h₁⟩ := gen f
    let ⟨x', h₂⟩ := gen x

    ⟨⸨f' x'⸩, .app h₁ h₂⟩
  | K' m n => ⟨K' m n, .refl_K'⟩
  | K m n => ⟨K m n, .refl_K⟩
  | S m n o => ⟨S m n o, .refl_S⟩
  | I m => ⟨I m, .refl_I⟩
  | Srt m => ⟨Srt m, .refl_Srt⟩
  | .next => ⟨.next, .refl_next⟩
  | .read => ⟨.read, .refl_read⟩
  | .assert => ⟨.assert, .refl_assert⟩
  | .app' => ⟨.app', .refl_app'⟩
  | .hole => ⟨.hole, .refl_hole⟩

open Qq in def gen_par_red_proof (p : ParRed' e e') : Lean.Expr :=
  match p with
  | @ParRed'.refl_K' m n      => q(@ParRed.refl_K' $m $n)
  | @ParRed'.refl_K m n       => q(@ParRed.refl_K $m $n)
  | @ParRed'.refl_S m n o     => q(@ParRed.refl_S $m $n $o)
  | @ParRed'.refl_I m         => q(@ParRed.refl_I $m)
  | @ParRed'.refl_hole        => q(@ParRed.refl_hole)
  | @ParRed'.refl_Srt m       => q(@ParRed.refl_Srt $m)
  | @ParRed'.refl_next        => q(@ParRed.refl_next)
  | @ParRed'.refl_read        => q(@ParRed.refl_read)
  | @ParRed'.refl_assert      => q(@ParRed.refl_assert)
  | @ParRed'.refl_app'        => q(@ParRed.refl_app')
  | @ParRed'.I x x' m α h     =>
    let inner : Q(ParRed $x $x') := gen_par_red_proof h
    q(@ParRed.I $x $x' $m $α $inner)
  | @ParRed'.K x x' m n α β y h =>
    let inner : Q(ParRed $x $x') := gen_par_red_proof h
    q(@ParRed.K $x $x' $m $n $α $β $y $inner)
  | @ParRed'.K' x x' m n α β y h =>
    let inner : Q(ParRed $x $x') := gen_par_red_proof h
    q(@ParRed.K' $x $x' $m $n $α $β $y $inner)
  | @ParRed'.S x x' y y' z z' m n o α β γ hx hy hz =>
    let hx' : Q(ParRed $x $x') := gen_par_red_proof hx
    let hy' : Q(ParRed $y $y') := gen_par_red_proof hy
    let hz' : Q(ParRed $z $z') := gen_par_red_proof hz

    q(@ParRed.S $x $x' $y $y' $z $z' $m $n $o $α $β $γ $hx' $hy' $hz')
  | @ParRed'.Pi α α' β β' x x' m h_α h_β h_x =>
    let hx' : Q(ParRed $α $α') := gen_par_red_proof h_α
    let hy' : Q(ParRed $β $β') := gen_par_red_proof h_β
    let hz' : Q(ParRed $x $x') := gen_par_red_proof h_x

    q(@ParRed.Pi $α $α' $β $β' $x $x' $m $hx' $hy' $hz')
  | @ParRed'.Pival α α' β β' m h_α h_β =>
    let hx' : Q(ParRed $α $α') := gen_par_red_proof h_α
    let hy' : Q(ParRed $β $β') := gen_par_red_proof h_β
    q(@ParRed.Pival $α $α' $β $β' $m $hx' $hy')
  | @ParRed'.next f f' x hf   =>
    let hf : Q(ParRed $f $f') := gen_par_red_proof hf
    q(@ParRed.next $f $f' $x $hf)
  | @ParRed'.read e e' he     =>
    let he : Q(ParRed $e $e') := gen_par_red_proof he
    q(@ParRed.read $e $e' $he)
  | @ParRed'.assert e e' x he =>
    let he : Q(ParRed $e $e') := gen_par_red_proof he
    q(@ParRed.assert $e $e' $x $he)
  | @ParRed'.app' f f' g g' x x' π h_f h_g h_x =>
    let h_f : Q(ParRed $f $f') := gen_par_red_proof h_f
    let h_g : Q(ParRed $g $g') := gen_par_red_proof h_g
    let h_x : Q(ParRed $x $x') := gen_par_red_proof h_x
    q(@ParRed.app' $f $f' $g $g' $x $x' $π $h_f $h_g $h_x)
  | @ParRed'.app f f' x x' h_f h_x =>
    let h_f : Q(ParRed $f $f') := gen_par_red_proof h_f
    let h_x : Q(ParRed $x $x') := gen_par_red_proof h_x
    q(@ParRed.app $f $f' $x $x' $h_f $h_x)

syntax "red_decide" : tactic

open Lean Meta Elab Tactic in elab "red_decide" : tactic => do
  let goal ← getMainGoal
  let goalType := ← whnf (← Lean.Meta.reduceAll (← goal.getType))
  match goalType with
  | Lean.Expr.app (.app (.const ``ParRed []) x) _x' =>
    let tgt_term ← whnf (← Lean.Meta.reduceAll x)
    let e ← _root_.Expr.decode tgt_term
    let ⟨_, proof⟩ := gen e
    let expr := gen_par_red_proof proof
    goal.assign (← whnf (← Lean.Meta.reduceAll expr))
  | _ => throwError "unsupported"

def Atom.gen (e : Expr) : Atom e ∨ (∃ f x, e = ⸨f x⸩) ∨ (∃ m α β, e = (Π' m) α, β) :=
  match e with
  | (.I _m) => .inl <| .comb .I₀
  | (.K _m _n) => .inl <| .comb .K₀
  | (.K' _m _n) => .inl <| .comb .K'₀
  | (.S _m _n _o) => .inl <| .comb .S₀
  | .next => .inl <| .comb .next₀
  | .app' => .inl <| .comb .app'₀
  | .read => .inl <| .comb .read
  | .assert => .inl <| .comb .assert₀
  | .Srt _m => .inl .Srt
  | _? => .inl .hole
  | ⸨f x⸩ => .inr (.inl ⟨f, x, rfl⟩)
  | (Π' m) α, β => .inr (.inr ⟨m, α, β, rfl⟩)

def Atom.sound (_h : Atom.gen e = .inl h_atom) : Atom e :=
  match heq : Atom.gen e with
  | .inl h => h
  | _ => by simp_all

def Atom.sound' (_heq : Atom.gen e = .inr h_not_atom) : (¬ Atom e) := by
  simp_all
  match h_not_atom with
  | .inl ⟨f, x, heq⟩ | .inr ⟨m, α, β, heq⟩ =>
    intro hat
    match hat with
    | .comb h =>
      cases h
      repeat contradiction
    | .Srt =>
      contradiction

def Atom.complete (h : Atom e) : (Atom.gen e = .inl h) := by
  induction h
  repeat rfl

def diamond (h₁ : (gen a).fst = b) (h₂ : (gen a).fst = c) :
  ((d : Expr) × (PLift ((gen b).fst = d)) × (PLift ((gen c).fst = d))) := by
  let d := gen b
  refine ⟨d.fst, ?_, ?_⟩
  exact ⟨rfl⟩
  change PLift (_ = (gen b).fst)
  rw [← h₂, ← h₁]
  exact ⟨rfl⟩

def ParRed.transport_atom (h₁ : ParRed a b) (h₂ : Atom a) : (gen a).fst = b := by
  cases h₂ with
  | comb h => cases h <;> cases h₁ <;> unfold gen <;> rfl
  | _ => cases h₁; unfold gen; rfl

theorem gen_pi {m : Level} {α β x : Expr} : ∃ α' β', (gen ⸨((Π' m) α, β) x⸩).fst = ((Π' m) α', β') := by
  cases h₁ : (gen ⸨((Π' m) α, β) x⸩).fst with
  | _ =>
    unfold gen at h₁
    repeat split at h₁
    simp_all

inductive gen.eq : Expr → Expr → Prop
  | refl  : ParRed a a → gen.eq a a
  | step  : gen.eq a (gen a).fst
  | trans : gen.eq a c → gen.eq b c → gen.eq a b

@[simp] theorem gen.eq.of_gen : (gen a).fst = b → gen.eq a b := fun h => by
  rw [← h]
  exact gen.eq.step

open Expr in def gen.n_norm (n : ℕ) (e : Expr) : ((e' : Expr) × (PLift <| gen.eq e e')) :=
  match n with
  | .zero =>
    match e with
    | (K' m n) => ⟨(K' m n), ⟨.refl .refl_K'⟩⟩
    | (K m n) => ⟨(K m n), ⟨.refl .refl_K⟩⟩
    | (S m n o) => ⟨(S m n o), ⟨.refl .refl_S⟩⟩
    | (I m) => ⟨(I m), ⟨.refl .refl_I⟩⟩
    | (_?) => ⟨_?, ⟨.refl .refl_hole⟩⟩
    | (Srt m) => ⟨Srt m, ⟨.refl .refl_Srt⟩⟩
    | next => ⟨next, ⟨.refl .refl_next⟩⟩
    | .read => ⟨read, ⟨.refl .refl_read⟩⟩
    | assert => ⟨assert, ⟨.refl .refl_assert⟩⟩
    | x => ⟨(gen x).fst, ⟨.step⟩⟩
  | .succ n => by
    refine ⟨(gen ((gen e).fst)).fst, ⟨?_⟩⟩
    apply gen.eq.trans
    apply gen.eq.step
    apply gen.eq.trans
    apply gen.eq.trans
    apply gen.eq.refl
    apply ParRed.refl
    apply gen.eq.step
    apply gen.eq.refl
    apply ParRed.refl

theorem gen.eq.symm : gen.eq α β → gen.eq β α := by
  intro h
  induction h
  apply gen.eq.refl
  apply ParRed.refl
  apply gen.eq.trans
  apply gen.eq.refl
  apply ParRed.refl
  apply gen.eq.step
  apply gen.eq.trans
  repeat assumption

theorem gen.eq.diamond : gen.eq a b → gen.eq a c → (∃ d, gen.eq b d ∧ gen.eq c d) := by
  intro ha hb
  exact ⟨a, ha.symm, hb.symm⟩
