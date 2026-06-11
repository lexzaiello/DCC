import Dcc.Tactic.Quote

#eval dcc_show (Id(Sort 1) ∘' Id(Sort 1) (Sort 0))
#eval dcc_show `(Sort 1, Sort 1)
#eval dcc_show (Id(Sort 0))
#eval dcc_show (⟦Id(Sort 1)⟧(Sort 0, ⊤))
#check dcc_decompile (⟦Id(Sort 1)⟧(Sort 0, ⊤))

#check dcc_decompile ⟦Id(Sort 2)⟧(Sort 1, Sort 0)
#check dcc_decompile Id(Sort 2)
#check dcc_decompile Id(Sort 2)
#check dcc_decompile Fstc(Id(Sort 2))
#eval dcc_show ⟦Id(Sort 2)⟧(Sort 1, Sort 0)
#check dcc_decompile (Fstc(Id(Sort 2)) ⟦Id(Sort 2)⟧(Sort 1, Sort 0))
#check dcc_decompile (Sndc(Id(Sort 2)) ⟦Id(Sort 2)⟧(Sort 1, Sort 0))
#check dcc_decompile Id(Coup(Id(Sort 1)))
#check Σ (a : Sort 1), ((fun x => x) a)
#check dcc_decompile Coup(Id(Sort 1))
#check dcc_decompile Id(Coup(Id(Sort 1)))
#check dcc_decompile (Λ(Sort 1, Id(Sort 1), Id(Coup(Id(Sort 1)))))
#check dcc_decompile (Λ(Sort 1, Id(Sort 1), Fstc(Id(Sort 1))))
#check dcc_decompile Fstc(Id(Sort 2))
#check dcc_decompile (!(Sort 1))
#check dcc_decompile (!Λ(Sort 1, Id(Sort 1), Id(!(Coup(Id(Sort 1))))))
#eval dcc_show (!Λ(Sort 1, Id(Sort 1), Id(!(Coup(Id(Sort 1))))))
#check dcc_decompile ((Id(Sort 1) ∘' Id(Sort 1)) (Sort 0))
#check dcc_decompile (Λ(Sort 1, `(Sort 1, Sort 1), `(Coup(`(Sort 1, Sort 1)), Sort 2)))
#check dcc_decompile (Σ(`(Sort 1, Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), `(Coup(`(Sort 1, Sort 1)), Sort 2))) (Sort 0))
#check dcc_show (Σ(`(Sort 1, Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), `(Coup(`(Sort 1, Sort 1)), Sort 2))) (Sort 0))
#eval (DCC (Σ(`(Sort 1, Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), `(Coup(`(Sort 1, Sort 1)), Sort 2))) (Sort 0))).reduce_all₂
#check dcc_decompile `(Coup(`(Sort 1, Sort 1)), Sort 2)
#check dcc_decompile (Λ(Sort 1, `(Sort 1, Sort 1), `(Coup(`(Sort 1, Sort 1)), Sort 1)))
#eval dcc_show (Σ(`(Sort 1, Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), `(Coup(`(Sort 1, Sort 1)), Sort 2))))
#check dcc_decompile (Π(Id(Sort 1), Λ(Sort 1, Id(Sort 1), `(Coup(Id(Sort 1)), Sort 0))) (Sort 0))
#check dcc_show (Π(Id(Sort 1), Λ(Sort 1, Id(Sort 1), `(Coup(Id(Sort 1)), Sort 0))) (Sort 0))
#check dcc_decompile (Λ(Sort 1, `(Sort 1, Sort 1), Fstc(`(Sort 1, Sort 1))))

def mk_test_pair : Expr :=
  DCC (⟦`(Sort 1, `(Sort 1, Sort 1))⟧⟨Id(Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), Fstc(`(Sort 1, Sort 1)))⟩
    &(Sort 0))

#eval dcc_decompile #(mk_test_pair)
