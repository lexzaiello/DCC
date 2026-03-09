import Dcc.Syn.AstPi

def norm (e : Expr) :=
  match e with
  | ⸨(I _m) _α x⸩ => norm x
  | ⸨(K _m _n) _α _β x _y⸩ => norm x
  | ⸨(K' _m _n) _α _β x _y⸩ => norm x
  | ⸨(S _m _n _o) _α _β _γ x y z⸩ => ⸨⸨(norm x) (norm z)⸩ ⸨(norm y) (norm z)⸩⸩
  | ⸨((Π' m) α, β) x⸩ => (Π' m) (norm ⸨α x⸩), (norm ⸨β x⸩)
  | ⸨next f _x⸩ => norm f
  | ⸨read e⸩ => norm e
  | ⸨assert e _x⸩ => norm e
  | ⸨${π} f g x⸩ => ⸨π ⸨(norm f) (norm x)⸩ ⸨(norm g) (norm x)⸩⸩
  | (Π' m) α, β => (Π' m) (norm α), (norm β)
  | ⸨f x⸩ => ⸨(norm f) (norm x)⸩
  | e => e

def defeq (α β : Expr) (gas : ℕ := 100) : Except Format Unit :=
  match gas, α, β with
  | .succ n, ((Π' _m₁) α₁, β₁), ((Π' _m₂) α₂, β₂) => do
    let _ ← (defeq α₁ α₂ n).mapError (fun e => "while checking Π domain: " ++ e)
    (defeq (norm ⸨β₁ _?⸩) (norm ⸨β₂ _?⸩) n).mapError (fun e => "while checking Π codomain: " ++ e)
  | .succ n, ⸨assert e₁⸩, ⸨assert e₂⸩ => defeq e₁ e₂ n
  | .succ n, e₁, e₂ =>
    let e₁' := norm e₁
    let e₂' := norm e₂
    if e₁' == e₂' then
      pure ()
    else
      defeq e₁' e₂' n
  | .zero, e₁, e₂ =>
    let e₁' := norm e₁
    let e₂' := norm e₂
    if e₁' == e₂' then
      pure ()
    else
      .error <| (format α) ++ " ≠ " ++ (format β)

def infer : Expr → Except Format Expr
  | I m => return I.type m
  | K m n => return K.type m n
  | K' m n => return K'.type m n
  | S m n o => return S.type m n o
  | Srt m => return Srt m.succ
  | (Π' m) _α, _β => return Srt m
  | ⸨f x⸩ => do match ← norm <$> infer f, ← norm <$> infer x with
    | ((Π' _m) α₁, β), α₂ => do
      let _ ← (defeq α₁ α₂).mapError
        (fun e => "argument mismatch in app " ++ (format ⸨f x⸩) ++ ":" ++ .line ++ e)
      pure <| norm ⸨β x⸩
    | t₁, _t₂ =>
      .error <| "not a function type: " ++ (.nest 2 <| .line ++ (format t₁))
  | e => .error <| "not well-typed: " ++ (.nest 2 <| .line ++ (format e))

#eval infer ⸨(I 2) (Srt 1) (Srt 0)⸩
#eval infer ⸨(K 3 2) (Srt 2) ⸨(I 3) (Srt 2)⸩ (Srt 1) (Srt 0)⸩

#eval infer <| mk_I (Srt 1) 2
#eval infer <| ⸨(mk_I (Srt 1) 2) (Srt 0)⸩
