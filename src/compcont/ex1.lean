import analysis.topology.topological_space
import analysis.topology.continuity
import analysis.topology.topological_structures

open tactic expr
variables {X : Type*} {Y : Type*} {Z : Type*} {W : Type*}
          {f f₁ f₂ : X → Y} {g : Y → Z} {h : Z → W}
variables [topological_space X] [topological_space Y]
          [topological_space Z] [topological_space W]

-- Finish a goal of the form continuous (f ∘ g ∘ ... ) given all functions are continuous.
meta def contcomp : tactic unit :=
do `(continuous %%e) ← target <|> fail "goal has to be of the form 'continuous _'",
  
  -- if the goal is to show that the expression e is continuous, check if it is an assumption
  assumption <|>
  
  -- if e is not continuous by assumption, check if it is of the form 'f ∘ g' for some f and g
  do `(%%outer ∘ %%inner) ← return e <|> fail "not continuous by assumption, and not a compsition",
    
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

example (_ : continuous f) (_ : continuous g) (_ : continuous h) :
continuous (h ∘ g ∘ f) := 
by contcomp

example (_ : continuous f₁) (_ : continuous f₂) [add_monoid Y] :
  continuous (λ x, f₁ x + f₂ x) :=
sorry

example (_ : continuous f) (_ : continuous g) [add_monoid Y] :
  continuous (λ x, g $ f x) :=
by contcomp
