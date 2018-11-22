import analysis.topology.topological_space
import analysis.topology.continuity
import analysis.topology.topological_structures
import ex1

open tactic expr
variables {X : Type*} {Y : Type*} {Z : Type*} {W : Type*} {f f₁ f₂ : X → Y} {g : Y → Z} {h : Z → W}
variables [topological_space X] [topological_space Y] [topological_space Z] [topological_space W]

/- Push a given lambda expression inside in the goal:
 -
 - Takes an expression of the form 'λ x, f _[x]',
 - creates a hypothesis 'λ x, f _[x] = f ∘ (λ x, _[x])',
 - and rewrites the main goal using this hypothesis.
 -/
meta def push_lam_inside (e : expr) : tactic unit :=
do lam name binfo bdomain bbody ← return e
       <|> (fail "The given expression must be a λ."),

   app fn arg ← return bbody <|> fail "The outermost part must be a function application.",

   -- create hypothesis
   can_push_inside ← to_expr ``(%%e = %%fn ∘ %%(expr.lam name binfo bdomain arg)),   
   -- prove hypothesis
   h_can_push_inside ← assert "can_push_λ_inside" can_push_inside,
   reflexivity <|> fail "Can't prove that λ can be pushed inside by reflexivity.",
   -- rewrite target
   rewrite_target h_can_push_inside,
   return ()

example (_ : continuous f) (_ : continuous g) :
  continuous (λ x, g $ f x) :=
begin
(do to_expr ```(λ x, g $ f x) >>= push_lam_inside),
contcomp,
end

-- Same as contcomp, put pushes λ inside if possible.
meta def contcomp2 : tactic unit :=
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
    do push_lam_inside e <|> fail "can't move lambda inside",
       contcomp2
  | _ := fail "neither composite nor lambda expression"
  end

example (_ : continuous f) (_ : continuous g) [add_monoid Y] :
  continuous (λ x, g $ f x) :=
by contcomp2

example (_ : continuous f₁) (_ : continuous f₂) [add_monoid Y] :
  continuous (λ x, f₁ x + f₂ x) :=
by contcomp2

example [add_monoid X] [topological_add_monoid X]:
  continuous (λ x : X, x + x) :=
by do to_expr ```(has_add.add) >>= push_lam_inside; repeat sorry

