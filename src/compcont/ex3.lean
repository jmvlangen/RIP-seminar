import analysis.topology.topological_space
import analysis.topology.continuity
import analysis.topology.topological_structures
import ex2

open tactic expr function has_add
variables {X : Type*} {Y : Type*} {Z : Type*} {W : Type*}
          {f f₁ f₂ : X → Y} {g : Y → Z} {h : Z → W}
variables [topological_space X] [topological_space Y]
          [topological_space Z] [topological_space W]

example [add_monoid X] [topological_add_monoid X]:
  (λ x : X, x + x) = (uncurry add) ∘ (λ x : X, (x, x)) :=
by reflexivity

#check @has_add.add .

-- Some preparation is necessary, has_add.add has 4 (in words four) arguments
-- first count the non-implicit (default) args, then find them

meta def get_app_num_default_args_aux : expr → nat
| (pi _ binder_info.default _ bbody) := 1 + (get_app_num_default_args_aux bbody) 
| (pi _ _ _ bbody) := get_app_num_default_args_aux bbody
| _ :=  0


meta def get_app_num_default_args : expr → tactic nat :=
assume e,
do type ← infer_type e, -- the type of a function is a pi type, we inspect the binder_info recursively
  return $ get_app_num_default_args_aux type

meta def ith_default_arg_index_aux : expr → nat → tactic nat 
| (expr.pi _ binder_info.default _ _) 0 := return 0
| (expr.pi _ binder_info.default _ bbody) (i + 1) := do idx ← ith_default_arg_index_aux bbody i, return $ idx + 1
| (expr.pi _ _ _ bbody) i := do idx ← ith_default_arg_index_aux bbody i, return $ idx + 1
| e i := do fail $ "can't find " ++ to_string i ++ "th default argument index"


meta def ith_default_arg_index (e : expr) (i : nat) : tactic nat :=
do type ← infer_type e,
   index ← ith_default_arg_index_aux type i,
   return index

meta def get_codomain (e : expr) : tactic expr :=
do t ← infer_type e,
match t with
| `(%%domain → %%codomain) := return codomain
| _ := fail $ "Can't determine codomain, '" ++ to_string t ++ "' is not a function type."
end


--now we can 'uncurry' and move λ inside

/- Push a given lambda expression inside in the goal:
 -
 - Takes an expression of the form 'λ x, f _[x]',
 - creates a hypothesis 'λ x, f _[x] = f ∘ (λ x, _[x])',
 - and rewrites the main goal using this hypothesis.
 -
 - Tries to uncurry if there is a curried function with two arguments.
 -
 - Fails if it 'doesn't simplify'.
 -/
meta def push_lam_inside2 (e : expr): tactic unit :=
--do trace $ to_raw_fmt e,
do lam name binfo bdomain bbody ← return e
       <|> (fail "The given expression must be a λ."),
  if ¬ is_app bbody
  then fail $ "The outer most part of the lambda expression '" ++ (to_string e) ++ 
              "' is not a function application."
  else do
    -- we use fancier versions instead of simple pattern matching
    -- because there are many curried arguments now
    fn ← return $ get_app_fn bbody,
    arg ← return $ app_arg bbody,
    num_default_args ← get_app_num_default_args fn,

    -- uncurry if necessary, then push λ inside
    match num_default_args with
    | 2 := do -- there are two default arguments, uncurry and push lambda inside

      -- get first argument and argument type
      arg0_idx ← ith_default_arg_index fn 0,
      arg0 ← return $ ith_arg bbody arg0_idx,
      arg0_type ← get_codomain (expr.lam name binfo bdomain arg0),

      -- get second argument and argument type
      arg1_idx ← ith_default_arg_index fn 1,
      arg1 ← return $ ith_arg bbody arg1_idx,
      arg1_type ← get_codomain (expr.lam name binfo bdomain arg1),

      -- create the inner expression, i.e. λ x, (arg0[x], arg1[x])
      inner_body_app ← to_expr ``(@prod.mk %%arg0_type %%arg1_type),
      inner ← return $ expr.lam name binfo bdomain
                       (expr.app (expr.app inner_body_app arg0) arg1),

      -- create the outer expression, i.e. (uncurry f)
      expr.const fn_name _ ← return fn,
      outer ← return $ @expr.const ff fn_name [],

      -- create term 'original = outer ∘ inner', need to hint types here
      -- i.e. need to use @comp instead of $∘
      can_uncurry ← to_expr ``(%%e = @comp %%bdomain (%%arg0_type × %%arg1_type) _ 
                                           (uncurry %%outer) %%inner),            

      -- create hypothesis and prove it by reflexivity
      h_can_uncurry ← assert "can_uncurry" can_uncurry,
      reflexivity <|> rotate 1,

      -- rewrite target
      rewrite_target h_can_uncurry,
      to_expr ``(function.uncurry_def) >>= rewrite_target,
           
      -- fail if the outer or inner part is the same as the original expression
      `(continuous $ %%outer ∘ %%inner) ← target,
      (success_if_fail $ unify e inner) <|> fail "inner not changed!",
      (success_if_fail $ unify e outer) <|> fail "outer not changed!",

      -- done!
      return ()

    | 1 := do -- same as before
      -- create hypothesis
      can_push_inside ← to_expr ``(%%e = %%fn ∘ %%(expr.lam name binfo bdomain arg)),   
      -- prove hypothesis
      h_can_push_inside ← assert "can_push_λ_inside" can_push_inside,
      reflexivity <|> fail "Can't prove that λ can be pushed inside by reflexivity.",
      -- rewrite target
      rewrite_target h_can_push_inside,
      return ()
    | _ := fail "uncurrying more than two arguements is not implemented"
    end

example [add_monoid X] [topological_add_monoid X] : (continuous (λ x : X, x + x)) := 
begin
  (do `(continuous %%e) ← target,
    push_lam_inside2 e,
    return ()),
  contcomp2,
  exact topological_add_monoid.continuous_add X,
  sorry
end

example [add_monoid X] [topological_add_monoid X] : (continuous (λ x : X, (x, x))) := 
by sorry


-- Same as contcomp2, bu uses push_lam_inside2
meta def contcomp3 : tactic unit :=
do `(continuous %%e) ← target <|> fail "goal has to be of the form 'continuous _'",

  -- if the goal is to show that the expression e is continuous, check if it is an assumption
  assumption <|>
  
  -- if e is not continuous by assumption, check if it is of the form 'f ∘ g' for some f and g
  match e with
  | `(%%outer ∘ %%inner) :=
    do    
    -- assert that the outer function is continuous, if not, rotate the goal away
    outer_continuous ← to_expr ``(continuous %%outer),
    outer_is_continuous ← assert "h_outer_cont" outer_continuous,         
    contcomp <|> rotate 1,

    -- assert that the inner function is continuous, if not, rotate the goal away
    inner_continuous ← to_expr ``(continuous %%inner),
    inner_is_continuous ← assert "h_inner_cont" inner_continuous,
    contcomp <|> rotate 1,

    -- knowing that inner and outer function are continuous, apply the theorem continuous.comp
    -- which shows that the composite is continuous
    cont_comp ← to_expr ``(continuous.comp %%inner_is_continuous %%outer_is_continuous),
    exact cont_comp
  | `(λ _, _) :=
    -- if we can move the lambda inside, to that and apply contcomp2 recursively
    do push_lam_inside2 e <|> fail "can't move lambda inside",
       contcomp3
  | _ := fail "neither composite nor lambda expression"
  end

example [add_monoid X] [topological_add_monoid X] : (continuous (λ x : X, x + x)) := 
begin
  contcomp3,
  exact topological_add_monoid.continuous_add X,
  sorry
end

example [add_monoid X] [topological_add_monoid X] : (continuous (λ x : X, (x, x))) := 
by sorry
