import algebra.field algebra.ring
import analysis.normed_space analysis.ennreal
import analysis.topology.infinite_sum
import analysis.complex


/--
 - A formal power series over a ring R is a formal expression of the form
 -
 - ∑ᵢ aᵢ zⁱ
 -
 - where i ∈ ℕ and aᵢ ∈ R. Thus, the data necessary to specify a formal power
 - series is a sequence in R. The point of writing them as series is that this
 - specifies natural operations on them.
 -/
def formal_power_series (R : Type*) [ring R] : Type* := ℕ → R

-- TODO: introduce some notation, figure out how to avoid conflicts with notation for
-- infinite sums and convergent power series.

/--
 - Just like for polynomials, it is easy to define a 'formal derivative' for 
 - formal power series.
 -/
def formal_derivative {R : Type*} [ring R] : formal_power_series R → formal_power_series R := sorry


variable {R : Type*}
variables [normed_ring R]
open lattice topological_space

/--
 - A predicate that indicates if the formal power series s converges at a point x ∈ R.
 -/
def converges_at (x : R) (s : formal_power_series R) : Prop :=
has_sum (λ n : ℕ , s n * x ^ n) -- has_sum means absolute convergence of the series at x

/--
 - The supremum of {r : ℝ | ∀ x, ∥x∥ < r → converges s x}.
 -/
noncomputable def convergence_radius (s : formal_power_series R) (x₀ : R) : ennreal :=
Sup {r : ennreal | ∀ x : R, ↑(nnnorm (x - x₀)) < r → converges_at (x - x₀) s}


/--
 - A power series is the function associated with a formal power series by taking infinite sums. I may or may not converge.
 -/
noncomputable def power_series (s : formal_power_series R) : R → option R :=
begin
  haveI := classical.prop_decidable,
  exact λ x, if h : (converges_at x s) then some (classical.some h) else none
end

/--
 - A function f defined on an open subset of R is analytic if it can
 - locally be written as a convergent power series.
 -
 - This definition is not done yet.
 -/
class is_analytic (U : opens R) (f : U → R) : Prop :=
(prop : ∀ x ∈ U,  ∃ (s : formal_power_series R) (x₀ : R), convergence_radius s x₀ > 0 ∧ ↑(nnnorm (x - x₀)) ≤ convergence_radius s x₀ ∧  some (f ⟨x, ‹x ∈ U›⟩) = power_series s (x - x₀) )

structure analytic_function (U : opens R) :=
(to_fun : U → R)
(is_analytic := is_analytic U to_fun)

/--
 - An analytic function on U can be coerced to a function U → R.
 -/
instance (U : opens R) : has_coe_to_fun $ analytic_function U := ⟨λ _, U → R, λ f, f.to_fun⟩

/--
 - The formal derivative on formal power series restricts and corestricts
 - to convergent power series, hence it is defined for analytic functions.
 -/
def derivative (U : opens ℝ) : analytic_function U → analytic_function U := sorry

instance : normed_field ℂ := sorry

theorem one_div_z_analytic : is_analytic ⟨{z : ℂ | z ≠ 0}, sorry⟩ (λ z, (1:ℂ)/z) := sorry

