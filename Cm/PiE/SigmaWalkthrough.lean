/-
  one annoying thing with combinators and dependent types is you need 
  nondependent special case versions of S and K if you want to make
  a nondependent arrow. just like \alpha -> \beta.
  this is because the dependent type argument, like K (\alpha : Type) (\beta : \alpha -> Type)
  requires a function, but you only have dependent functions, so you
  get stuck in a cycle of type dependency forever.

  Altenkirch also used "special case" nondependent versions of S and K,
  but I've figured out that you can introduce a very weak version of K
  that "breaks the chain" of type dependency in a very clean way
  that fits in really nicely with the sigma-type lists.
-/

nil.{[m]} : \forall (\alpha : Type m), \alpha -> Type m
nil.{[m]} \alpha x = \alpha

/-
  nil basically downgrades a term of some type to its type.
  you can derive nondependent K and S usinng just this thingy,
  at least from the examples I did. I lean on this a lot in the type for `id.{[m]}`
-/

/-
  id.{[m]} : \forall (\alpha : Type m), \alpha -> \alpha

  this ends up being a crazy long list combinator expression normally.
  if we go argument by argument,
  ::[\alpha, id.{[m]}] - we should be able to check that \alpha should have type Type m.
  but we also want to save \alpha for later to make the \alpha -> \alpha part.

  But we also don't care about the (x : \alpha) argument, since we don't depend on the term.
  we only depend on (\alpha : Type m). we just need to check x.

  my convention to check that \alpha is the right type in ::[\alpha, id.{[m]}]
  is to treat ::[\alpha, id.{[m]}] like a sigma type, and "normalize" / isolate
  the Sigma.snd component. Sigma.snd gets us the second component, but without dependency
  on the Sigma.fst component. Standalone. AKA, normalization / function application.

  Sigma.snd could be another sigma, or it could just be a function. But remember,
  in the list calculus, function application is just cons'ing the argument onto
  the function. I haven't like solidified this 100%, but the rule is:
  - if Sigma.snd s is a function, then it should be another sigma. to "apply" \alpha to t_id:
  ::[\alpha, ::[mk_input_type, mk_output_type]], you "substitute" \alpha in as the input type
  ::[\alpha, ::[mk_input_type, mk_output_type]].snd = ::[::[\alpha, mk_input_type], mk_output_type]

  This is like mimicking substitution. The trick here is that we substituted by just making
  a new pair. We didn't normalize anything in id's input type maker.

  If we wanted to type-check (\alpha : Type m) as an argument, we would have to normalize:
  ::[\alpha, t_id_m].snd.fst.snd == (infer_type \alpha). the root .snd gets the "generated type"
  by applying the argument \alpha, then .snd.fst gets the factory for the expected input type,
  then .fst.snd.snd NORMALIZES the expected input type. Let's say mk_input_type
  is ::[Ty m, nil.{[m.succ]}]. As I explained before, nil downgrades a term to a type.
  it's useful for convering dependent types to nondependent types.

  ::[\alpha, t_id_m].snd.fst.snd = ::[::[\alpha, ::[Ty m, nil.{{m.succ]}]], mk_output_type].fst.snd
  = ::[\alpha, ::[Ty m, nil.{{m.succ]}]].snd -- .snd on the expected input type to "normalize" it and break away the Sigma.fst into just a standalong normalized Sigma.snd
  = Ty m -- this is due to the evaluation rule for nil. nil downgrades terms to types.

  continued...
-/


::[\alpha, t_id_m].snd.fst.snd = ::[::[\alpha, ::[Ty m, nil.{{m.succ]}]], mk_output_type].fst.snd
  = ::[\alpha, ::[Ty m, nil.{{m.succ]}]].snd 
  = Ty m = ::[\alpha, t_id_m].snd.fst.snd

/-
  So, the kernel is able to type-check that \alpha should have the type Ty m as an argument to id.{[m]}.
  But what about (x : \alpha), and the return type \alpha? Surely we need to duplicate \alpha?
  Didn't it get downgraded to Ty m? Not so fast.
-/

::[\alpha, t_id_m].snd.fst.snd

/-
  This is the expression the kernel uses to type-check \alpha. it normalizes the expected input type.
  But to get the output type of ::[\alpha, id.{{m]}], it can just remove the .fst.
-/

::[\alpha, t_id_m].snd.snd

/-
  This does not force normalization of the expected input type, but \alpha still gets substitued in.
  So we end up with: ::[::[\alpha, ::[Ty m, nil.{{m.succ]}]], mk_output_type].snd
  Note here, mk_output_type just sees the DATA / pair / sigma form of ::[\alpha, ::[Ty m, nil.{[m.succ]}],
  since the kernel did that extra .fst.snd step to fetch the input type, and normalize it.
  Remember, in a sigma, the Sigma.snd depends on the value of the .fst.
  Just the value. Nothing more. So, .snd just sees the "list" / sigma ::[\alpha, ::[Ty m, nil.{{m.succ]}]].
  And, since it's a sigma / list, it can manipulate it like one.

  So, how do we type-check ::[x, \alpha, id.{[m]}]? We need to:
  - get rid of x for the input type, and spit back out \alpha
  - duplicate \alpha as the output type

  Except, we already know how to do this.
  Let's tall the x-app-type-checker t_check_x

  t_check_x gets as its Sigma.fst that un-normalized "input type" data for the id \alpha app,
  since Sigma.snd (the "return type" of the id \alpha app) depends on the input type.
-/

x_app's_sigma_fst = ::[\alpha, ::[Ty m, nil.{{m.succ]}]] -- this is \alpha substitued into t_id_m.

/-
  But x_app_checker also has its own Sigma.fst.
  So, we apply them.
-/

-- I am a making abuse of notation here. function composition should be easy to implement,
-- or there may be a way around using it here. almost certainly. we'll see.
check_x = ::[nil.{[m]} ∘ Prod.fst, Prod.snd]

-- first element in this list is the \alpha input type data. second element is our x argument checker maker
-- as I described above, the last step in checking ::[x, f] is ::[x, t_f].snd.snd to get the output type.
-- that results in substituting that data into check_x:
::[::[\alpha, ::[Ty m, nil.{{m.succ]}]], check_x].snd =
  ::[::[::[\alpha, ::[Ty m, nil.{{m.succ]}]], nil.{[m]} ∘ Prod.fst], Prod.snd] -- this hanging Prod.snd is for the final return type, which I will explain later
= ::[::[::[\alpha, ::[Ty m, nil.{{m.succ]}]], Prod.fst], nil.{[m]}], Prod.snd] -- Prod.fst composed with nil.{[m.succ]} to fetch \alpha fron the old input type data,
                                                                               -- then make nil.{[m.succ]} \alpha, which will accept as an argument (x : \alpha), returning \alpha
= ::[::[\alpha, nil.{{m]}], Prod.snd]

let norm_out_type_alpha_app_id = ::[::[\alpha, nil.{{m]}], Prod.snd]

/-
  Now, to type-check the x argument, check the expected input type with .snd.fst.snd, and get the return type with .snd.snd:
-/

let sub_x_in = ::[x, norm_out_type_alpha_app_id].snd
  = ::[x, ::[::[\alpha, nil.{{m]}], Prod.snd]].snd
  = ::[::[x, \alpha, nil.{[m]}], Prod.snd]

let x_expected_t = sub_x_in.fst.snd = ::[x, ::[::[\alpha, nil.{{m]}], Prod.snd]].snd.fst.snd
  = ::[::[x, \alpha, nil.{[m]}], Prod.snd].fst.snd
  = ::[x, \alpha, nil.{[m]}].snd
  = \alpha -- due to nil eval rule to downgrade terms to types

-- Sigma.snd needs to be normalized, so it receives Sigma.snd as an argument
let x_out_t = sub_x_in.snd.snd = ::[x, ::[::[\alpha, nil.{{m]}], Prod.snd]].snd.snd
  = ::[::[x, \alpha, nil.{[m]}], Prod.snd].snd
  = \alpha -- due to imaginary Prod.snd, which I haven't written yet. LOL
