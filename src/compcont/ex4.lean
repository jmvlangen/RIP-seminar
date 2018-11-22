import analysis.topology.topological_space
import analysis.topology.continuity
import analysis.topology.topological_structures
import ex3

open tactic expr function has_add
variables {X : Type*} {Y : Type*} {Z : Type*} {W : Type*}
          {f f₁ f₂ : X → Y} {g : Y → Z} {h : Z → W}
variables [topological_space X] [topological_space Y]
          [topological_space Z] [topological_space W]


/- A tactic that splits a goal of the form continuous λ x, ⟨f₁ x, f₂ x⟩
 - into two subgoals of the form continuous λ x, f₁ x and continuous λ x, f₂ x.
 -/
meta def contprod : tactic unit :=
do `(continuous %%e) ← target <|>  fail "The goal must be of the form 'continuous _'.",
   `(_ → _ × _) ← infer_type e <|> fail "The function must be to a cartesian product.",

   -- create a goal showing that the first factor is continuous
   fst_continuous ← match e with 
     | `(λ x, prod.mk (%%left) (%%right)) := to_expr ``(continuous (λ x, %%left))
     | _ := to_expr ``(continuous $ prod.fst ∘ %%e)
   end,
   h_fst_continuous ← assert "h_lhs_is_cont" fst_continuous,
   rotate 1,
   
   -- create a goal showing that the second factor is continuous
   snd_continuous ← match e with
     | `(λ x, prod.mk (%%left) (%%right)) := to_expr ``(continuous (λ x, %%right))
     | _ := to_expr ``(continuous $ prod.fst ∘ %%e)
   end,
   h_snd_continuous ← assert "h_rhs_is_cont" snd_continuous,
   rotate 1,
   
   -- the function goes to a product, it suffices to show that each factor is continuous
   cont_prod ← to_expr ``(continuous.prod_mk %%h_fst_continuous %%h_snd_continuous),
   exact cont_prod,
   return ()

example [add_monoid X] [topological_add_monoid X] : (continuous (λ x : X, (x, x))) := 
begin
  contprod,
  exact continuous_id,
  exact continuous_id,
end

example [add_monoid X] [topological_add_monoid X] : (continuous (λ x : X, x + x)) := 
begin
  contcomp3,
  exact topological_add_monoid.continuous_add X,
  contprod,
  exact continuous_id,
  exact continuous_id
end
