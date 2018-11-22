import analysis.topology.topological_space
import analysis.topology.continuity
import analysis.topology.topological_structures
import ex4 analysis.normed_space

open tactic expr function has_add
variables {X : Type*} {Y : Type*} {Z : Type*} {W : Type*}
          {f f₁ f₂ : X → Y} {g : Y → Z} {h : Z → W}
variables [topological_space X] [topological_space Y]
          [topological_space Z] [topological_space W]
          [ring X] [topological_ring X]

declare_trace elementary

lemma continuous_subs {X : Type*} [topological_space X] [add_group X] [topological_add_group X] :
  continuous (λ p : X × X, p.1 - p.2) := sorry

lemma continuous_smul' {E : Type*} {k : Type*} [normed_field k] [normed_space k E] :
  continuous ((λ p , p.fst • p.snd) : (k × E → E)) := sorry


meta def elementary : tactic unit :=
do `(continuous %%e) ← target,

   (when_tracing `elementary (do trace e, trace "  elementary trying statements")),

   (do tgt : expr ← target,
     to_expr ``(continuous_id : %%tgt) >>= exact <|>
     to_expr ``(continuous_const : %%tgt) >>= exact <|>
     to_expr ``(topological_add_monoid.continuous_add _ : %%tgt) >>= exact <|>
     to_expr ``(topological_group.continuous_inv _ : %%tgt) >>= exact <|>
     to_expr ``(topological_add_group.continuous_neg _ : %%tgt) >>= exact <|>
     to_expr ``(topological_monoid.continuous_mul _ : %%tgt) >>= exact <|>
     to_expr ``(continuous_subs : %%tgt) >>= exact <|>
     to_expr ``(continuous_smul' : %%tgt) >>= exact ) <|> 

   ((when_tracing `elementary $ (tactic.trace "  elementary trying assumption"));
     assumption) <|>

   ((when_tracing `elementary $ (tactic.trace "  elementary trying contcomp3"));
     contcomp3; elementary) <|>

   ((when_tracing `elementary $ (tactic.trace "  elementary trying contprod"));
     contprod; elementary) <|>

   skip

example : continuous ( λ x : X, x + 1 + x)  :=
by elementary


example {E : Type*} {k : Type*} [normed_field k] [normed_space ℝ E] 
        (L₁ : E → E) (L₂ : E → E) (ψ₁ : E → E) (ψ₂ : E → E)
        (_ : continuous ψ₁) (_ : continuous ψ₂) (v : E) :
continuous (λ t : ℝ,  L₁ v - L₂ v + ∥v∥ • (ψ₁ (t • v) - ψ₂ (t • v))) :=
by sorry
