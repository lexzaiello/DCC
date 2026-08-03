import Dcc.Ast.Core

inductive Shared.{u} (α : Sort u) : Type u where
  | share : α → Shared α

def Shared.deref.{u} {α : Sort u} (s : Shared.{u} α) : α :=
  match s with
  | ⟨s⟩ => s

def Shared.deref'.{u, v} {α : Sort u} {β : α → Sort v} (f : ∀ (x : α), β x) (s : Shared.{u} α) : β s.deref :=
  match s with
  | ⟨s⟩ => f s

def Shared.map.{u, v} {α : Sort u} (f : α → Sort v) (s : Shared.{u} α) : Type v :=
  match s with
  | ⟨s⟩ => Shared (f s)

def Shared.fmap.{u, v} {α : Sort u} {β : α → Sort v} (f : ∀ (x : α), β x) (s : Shared.{u} α) : Shared.{v} (β s.deref) :=
  match s with
  | ⟨s⟩ => ⟨f s⟩

def Shared.unmap.{u, v} {α : Sort u} {β : α → Sort v} (f : ∀ (x : α), β x) (s : Shared.{u} α) : (β s.deref) :=
  match s with
  | ⟨s⟩ => f s

#check Shared.deref

#check PSigma
#check Shared.share
