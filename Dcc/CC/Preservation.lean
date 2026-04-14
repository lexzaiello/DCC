import Dcc.CC.Ast
import Dcc.CC.Step2
import Dcc.CC.Judge

namespace Expr

namespace JudgeConv

def invert_app : JudgeConv (DCC (f x)) t → (α β : Expr) × (m n : Level) × JudgeConv x α × JudgeConv f (DCC (Π(m, n) α β)) × (Reduces (DCC (β ⟦Sort m, Id(Sort m)⟧(α, x))) t) := fun ⟨h_t, h_red⟩ =>
  match h_t with
  | .app (α := α) (β := β) (m := m) (n := n) h_t_f h_red_pi h_t_x h_red_α =>
    ⟨α, β, m, n, ⟨h_t_x, h_red_α⟩, ⟨h_t_f, h_red_pi⟩, h_red⟩

end JudgeConv

end Expr
