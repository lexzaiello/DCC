import Dcc.Ast.Core

inductive Share.{u} (α : Sort u) : Type u where
  | share : α → Share α

def Share.deref.{u} {α : Sort u} (s : Share.{u} α) : α :=
  match s with
  | ⟨s⟩ => s

def Share.deref'.{u, v} {α : Sort u} {β : α → Sort v} (f : ∀ (x : α), β x) (s : Share.{u} α) : β s.deref :=
  match s with
  | ⟨s⟩ => f s

def Share.map.{u, v} {α : Sort u} (f : α → Sort v) (s : Share.{u} α) : Type v :=
  match s with
  | ⟨s⟩ => Share (f s)

def Share.fmap.{u, v} {α : Sort u} {β : α → Sort v} (f : ∀ (x : α), β x) (s : Share.{u} α) : Share.{v} (β s.deref) :=
  match s with
  | ⟨s⟩ => ⟨f s⟩

def Share.unmap.{u, v} {α : Sort u} {β : α → Sort v} (f : ∀ (x : α), β x) (s : Share.{u} α) : (β s.deref) :=
  match s with
  | ⟨s⟩ => f s

#check Share.deref

#check PSigma
#check Share.share
