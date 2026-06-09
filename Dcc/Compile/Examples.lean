import Dcc.Compile.Core

#eval Std.format <| dcc_compile' {Expr.infer₂} ((fun (α : Sort 0) (x : α) => x) True True.intro)
#eval Std.format <| dcc_infer' {Expr.infer₂} (fun (α : Sort 0) (x : α) => x) True True.intro

#eval Std.format <| dcc_compile' {Expr.infer₂} {Expr.reduce₂} (fun (x : Sort 0) => (fun (x : Sort 0) => x) x)
#eval Std.format <| dcc_infer' {Expr.infer₂} {Expr.reduce₂} (fun (x : Sort 0) => (fun (x : Sort 0) => x) x)
#eval Std.format <| dcc_infer' {Expr.infer₂} {Expr.reduce₂} ((fun (x : Sort 1) => (fun (x : Sort 1) => x) x) (Sort 0))
#eval Std.format <| dcc_compile' {Expr.infer₂} {Expr.reduce₂} ((fun (α : Sort 2) (x : α) => (fun (x : α) => x) x) (Sort 1) (Sort 0))

#eval Std.format <| dcc_compile' {Expr.infer₂} {Expr.reduce₂} ((fun (α : Sort 2) (x : α) => (fun (x : α) => x) x) (Sort 1) (Sort 0))
#eval Std.format <| dcc_infer' {Expr.infer₂} {Expr.reduce₂} ((fun (α : Sort 2) (x : α) => (fun (x : α) => x) x) (Sort 1) (Sort 0))

#eval Std.format <| (dcc_compile' {Expr.infer₂} {Expr.reduce_all₂} ((fun (f : Sort 0 → Sort 0) (x : f True) => x) (fun x => x) True.intro))
#time #eval Std.format <| dcc_infer' {Expr.infer₂} {Expr.reduce_all₂} ((fun (f : Sort 0 → Sort 0) (x : f True) => x) (fun x => x) True.intro)

#eval Std.format <| dcc_infer' {Expr.infer₂} {Expr.reduce_all₂} ((fun (f : Sort 0 → Sort 0) (x : f True) => x))

def K_example : Expr :=
  dcc_compile' {Expr.infer₂} {Expr.reduce_all₂} ((fun (α : Sort 1) (β : α → Sort 1) (x : α) (_y : β x) => x) (Sort 0))

def K_example₂ : Option Expr :=
  dcc_infer' {Expr.infer₂} {Expr.reduce_all₂} ((fun (α : Sort 1) (β : α → Sort 1) (x : α) (_y : β x) => x) (Sort 0))

def K_example₃ : Expr :=
  dcc_compile' {Expr.infer₂} {Expr.reduce_all₂} ((fun (α : Sort 3) (β : α → Sort 2) (x : α) (_y : β x) => x) (Sort 2) (fun x => x))

def K_example₃' : Option Expr :=
  dcc_infer' {Expr.infer₂} {Expr.reduce_all₂} ((fun (α : Sort 3) (β : α → Sort 2) (x : α) (_y : β x) => x) (Sort 2) (fun x => x) (Sort 1) (Sort 0))

#eval Std.format <| K_example₃

#eval Std.format <| K_example₃'

def K_example' : Option Expr :=
  dcc_infer' {Expr.infer₂} {Expr.reduce_all₂} (fun (α : Sort 1) (β : α → Sort 1) (x : α) (_y : β x) => x)

#eval Std.format <| K_example'

#eval Std.format <| K_example

#eval Std.format <| dcc_infer' {Expr.infer₂} {Expr.reduce_all₂} (fun (x : Sort 0) => x)

#eval Std.format <| (DCC (!<Π(Sndc(`(⊤, Sort 1)), Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))> &(⟦`(⊤, Sort 1)⟧(∗, Sort 0)))).reduce_all₂

#eval Std.format <| (DCC (Sndc(`(⊤, Sort 1)) (⟦`(⊤, Sort 1)⟧(∗, Sort 0)))).reduce_all₂

#eval Std.format <| K_example₂

#eval Std.format <| (DCC (Π(Sndc(`(⊤, Sort 1)), Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))) ⟦`(⊤, Sort 1)⟧(∗, Sort 0))).reduce_all₂
#eval (DCC (Sndc(`(⊤, Sort 1)) ⟦`(⊤, Sort 1)⟧(∗, Sort 0))).reduce_all₂

/-
Λ(Coup((Sndc(`(⊤, Sort 1)) ∘'
                             Fstc(Π(Sndc(`(⊤, Sort 1)),
                                    Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))),
                     ((Sndc(`(⊤, Sort 1)) ∘'
                           Fstc(Π(Sndc(`(⊤, Sort 1)),
                                  Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))) ∘'
                        Fstc((Sndc(`(⊤, Sort 1)) ∘'
                                Fstc(Π(Sndc(`(⊤, Sort 1)),
                                       Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                         `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))))),
                     `(Coup(((Sndc(`(⊤, Sort 1)) ∘'
                                  Fstc(Π(Sndc(`(⊤, Sort 1)),
                                         Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                           `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))) ∘'
                               Fstc((Sndc(`(⊤, Sort 1)) ∘'
                                       Fstc(Π(Sndc(`(⊤, Sort 1)),
                                              Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                                `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))))),
                       Sort 1))

add this thingy in eval to arrows?

Eval(Coup((Sndc(`(⊤, Sort 1)) ∘'
                           Fstc(Π(Sndc(`(⊤, Sort 1)),
                                  Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))),
                   ((Sndc(`(⊤, Sort 1)) ∘'
                         Fstc(Π(Sndc(`(⊤, Sort 1)),
                                Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))) ∘'
                      Fstc((Sndc(`(⊤, Sort 1)) ∘'
                              Fstc(Π(Sndc(`(⊤, Sort 1)),
                                     Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                       `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))))),
                   Λ(Coup((Sndc(`(⊤, Sort 1)) ∘'
                             Fstc(Π(Sndc(`(⊤, Sort 1)),
                                    Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))),
                     ((Sndc(`(⊤, Sort 1)) ∘'
                           Fstc(Π(Sndc(`(⊤, Sort 1)),
                                  Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))) ∘'
                        Fstc((Sndc(`(⊤, Sort 1)) ∘'
                                Fstc(Π(Sndc(`(⊤, Sort 1)),
                                       Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                         `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))))),
                     `(Coup(((Sndc(`(⊤, Sort 1)) ∘'
                                  Fstc(Π(Sndc(`(⊤, Sort 1)),
                                         Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                           `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))) ∘'
                               Fstc((Sndc(`(⊤, Sort 1)) ∘'
                                       Fstc(Π(Sndc(`(⊤, Sort 1)),
                                              Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                                `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))))),
                       Sort 1)))
-/

/-dcc_trace' (Λ(⊤, `(⊤, Sort 1),
   !Λ(Coup(`(⊤, Sort 1)),
      Π(Sndc(`(⊤, Sort 1)), Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))),
      !Λ(Coup(Π(Sndc(`(⊤, Sort 1)), Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))),
         (Sndc(`(⊤, Sort 1)) ∘'
            Fstc(Π(Sndc(`(⊤, Sort 1)),
                   Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))),
         Λ(!(Coup((Sndc(`(⊤, Sort 1)) ∘'
                    Fstc(Π(Sndc(`(⊤, Sort 1)),
                           Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))))),
           (Eval(Coup((Sndc(`(⊤, Sort 1)) ∘'
                           Fstc(Π(Sndc(`(⊤, Sort 1)),
                                  Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))),
                   ((Sndc(`(⊤, Sort 1)) ∘'
                         Fstc(Π(Sndc(`(⊤, Sort 1)),
                                Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))) ∘'
                      Fstc((Sndc(`(⊤, Sort 1)) ∘'
                              Fstc(Π(Sndc(`(⊤, Sort 1)),
                                     Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                       `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))))),
                   (Sndc(Π(Sndc(`(⊤, Sort 1)),
                             Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))) ∘'
                      Fstc((Sndc(`(⊤, Sort 1)) ∘'
                              Fstc(Π(Sndc(`(⊤, Sort 1)),
                                     Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                       `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))))) ∘∘
              ⟦Λ(Coup((Sndc(`(⊤, Sort 1)) ∘'
                           Fstc(Π(Sndc(`(⊤, Sort 1)),
                                  Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))),
                   `(Coup((Sndc(`(⊤, Sort 1)) ∘'
                             Fstc(Π(Sndc(`(⊤, Sort 1)),
                                    Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))),
                     Coup((Sndc(`(⊤, Sort 1)) ∘'
                             Fstc(Π(Sndc(`(⊤, Sort 1)),
                                    Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))))),
                   (((Sndc(`(⊤, Sort 1)) ∘'
                            Fstc(Π(Sndc(`(⊤, Sort 1)),
                                   Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))) ∘'
                         Fstc((Sndc(`(⊤, Sort 1)) ∘'
                                 Fstc(Π(Sndc(`(⊤, Sort 1)),
                                        Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                          `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))))) ∘'
                      Fstc(`(Coup((Sndc(`(⊤, Sort 1)) ∘'
                                     Fstc(Π(Sndc(`(⊤, Sort 1)),
                                            Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                              `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))),
                             Coup((Sndc(`(⊤, Sort 1)) ∘'
                                     Fstc(Π(Sndc(`(⊤, Sort 1)),
                                            Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                              `(Coup(Sndc(`(⊤, Sort 1))),
                                                Sort 1))))))))))⟧⟨Id(Coup((Sndc(`(⊤, Sort 1)) ∘'
                                                        Fstc(Π(Sndc(`(⊤, Sort 1)),
                                                               Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                                                 `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))))),
                                             Λ(Coup((Sndc(`(⊤, Sort 1)) ∘'
                                                       Fstc(Π(Sndc(`(⊤, Sort 1)),
                                                              Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                                                `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))),
                                               `(Coup((Sndc(`(⊤, Sort 1)) ∘'
                                                         Fstc(Π(Sndc(`(⊤, Sort 1)),
                                                                Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                                                  `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))),
                                                 Coup((Sndc(`(⊤, Sort 1)) ∘'
                                                         Fstc(Π(Sndc(`(⊤, Sort 1)),
                                                                Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                                                  `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))))),
                                               (Sndc((Sndc(`(⊤, Sort 1)) ∘'
                                                          Fstc(Π(Sndc(`(⊤, Sort 1)),
                                                                 Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                                                   `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))) ∘'
                                                  Fstc(`(Coup((Sndc(`(⊤, Sort 1)) ∘'
                                                                 Fstc(Π(Sndc(`(⊤, Sort 1)),
                                                                        Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                                                          `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))),
                                                         Coup((Sndc(`(⊤, Sort 1)) ∘'
                                                                 Fstc(Π(Sndc(`(⊤, Sort 1)),
                                                                        Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                                                          `(Coup(Sndc(`(⊤, Sort 1))),
                                                                            Sort 1))))))))))⟩),
           ((Sndc((Sndc(`(⊤, Sort 1)) ∘'
                         Fstc(Π(Sndc(`(⊤, Sort 1)),
                                Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))) ∘'
                 *(Coup((Sndc(`(⊤, Sort 1)) ∘'
                          Fstc(Π(Sndc(`(⊤, Sort 1)),
                                 Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))))) ∘'
              Fstc((Eval(Coup((Sndc(`(⊤, Sort 1)) ∘'
                                   Fstc(Π(Sndc(`(⊤, Sort 1)),
                                          Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                            `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))),
                           ((Sndc(`(⊤, Sort 1)) ∘'
                                 Fstc(Π(Sndc(`(⊤, Sort 1)),
                                        Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                          `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))) ∘'
                              Fstc((Sndc(`(⊤, Sort 1)) ∘'
                                      Fstc(Π(Sndc(`(⊤, Sort 1)),
                                             Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                               `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))))),
                           (Sndc(Π(Sndc(`(⊤, Sort 1)),
                                     Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))) ∘'
                              Fstc((Sndc(`(⊤, Sort 1)) ∘'
                                      Fstc(Π(Sndc(`(⊤, Sort 1)),
                                             Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                               `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))))) ∘∘
                      ⟦Λ(Coup((Sndc(`(⊤, Sort 1)) ∘'
                                   Fstc(Π(Sndc(`(⊤, Sort 1)),
                                          Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                            `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))),
                           `(Coup((Sndc(`(⊤, Sort 1)) ∘'
                                     Fstc(Π(Sndc(`(⊤, Sort 1)),
                                            Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                              `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))),
                             Coup((Sndc(`(⊤, Sort 1)) ∘'
                                     Fstc(Π(Sndc(`(⊤, Sort 1)),
                                            Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                              `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))))),
                           (((Sndc(`(⊤, Sort 1)) ∘'
                                    Fstc(Π(Sndc(`(⊤, Sort 1)),
                                           Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                             `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))) ∘'
                                 Fstc((Sndc(`(⊤, Sort 1)) ∘'
                                         Fstc(Π(Sndc(`(⊤, Sort 1)),
                                                Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                                  `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))))) ∘'
                              Fstc(`(Coup((Sndc(`(⊤, Sort 1)) ∘'
                                             Fstc(Π(Sndc(`(⊤, Sort 1)),
                                                    Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                                      `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))),
                                     Coup((Sndc(`(⊤, Sort 1)) ∘'
                                             Fstc(Π(Sndc(`(⊤, Sort 1)),
                                                    Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                                      `(Coup(Sndc(`(⊤, Sort 1))),
                                                        Sort 1))))))))))⟧⟨Id(Coup((Sndc(`(⊤, Sort 1)) ∘'
                                                                Fstc(Π(Sndc(`(⊤, Sort 1)),
                                                                       Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                                                         `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))))),
                                                     Λ(Coup((Sndc(`(⊤, Sort 1)) ∘'
                                                               Fstc(Π(Sndc(`(⊤, Sort 1)),
                                                                      Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                                                        `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))),
                                                       `(Coup((Sndc(`(⊤, Sort 1)) ∘'
                                                                 Fstc(Π(Sndc(`(⊤, Sort 1)),
                                                                        Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                                                          `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))),
                                                         Coup((Sndc(`(⊤, Sort 1)) ∘'
                                                                 Fstc(Π(Sndc(`(⊤, Sort 1)),
                                                                        Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                                                          `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))))),
                                                       (Sndc((Sndc(`(⊤, Sort 1)) ∘'
                                                                  Fstc(Π(Sndc(`(⊤, Sort 1)),
                                                                         Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                                                           `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))) ∘'
                                                          Fstc(`(Coup((Sndc(`(⊤, Sort 1)) ∘'
                                                                         Fstc(Π(Sndc(`(⊤, Sort 1)),
                                                                                Λ(Coup(`(⊤, Sort 1)),
                                                                                  Sndc(`(⊤, Sort 1)),
                                                                                  `(Coup(Sndc(`(⊤, Sort 1))),
                                                                                    Sort 1)))))),
                                                                 Coup((Sndc(`(⊤, Sort 1)) ∘'
                                                                         Fstc(Π(Sndc(`(⊤, Sort 1)),
                                                                                Λ(Coup(`(⊤, Sort 1)),
                                                                                  Sndc(`(⊤, Sort 1)),
                                                                                  `(Coup(Sndc(`(⊤, Sort 1))),
                                                                                    Sort 1))))))))))⟩)))))))
   ∗)
-/

-- Π(Sndc(`(⊤, Sort 1)), Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))

--#eval 
