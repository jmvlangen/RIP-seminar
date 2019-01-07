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
def formal_power_series (R : Type*) : Type* := ℕ → R

namespace formal_power_series

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
def converges_at_to (s : formal_power_series R) (x : R) (y : R) : Prop :=
is_sum (λ n : ℕ , s n * x ^ n) y -- is_sum means absolute convergence of the series at x

def converges_to_at (s : formal_power_series R) (y : R) (x : R) : Prop :=
is_sum (λ n : ℕ , s n * x ^ n) y -- is_sum means absolute convergence of the series at x

def converges_at (s : formal_power_series R) (x : R) : Prop :=
has_sum (λ n : ℕ , s n * x ^ n) -- has_sum means absolute convergence of the series at x

/--
 - The supremum of {r : ℝ | ∀ x, ∥x∥ < r → converges s x}.
 -/
noncomputable def convergence_radius (s : formal_power_series R) (x₀ : R) : ennreal :=
Sup {r : ennreal | ∀ x : R, ↑(nnnorm (x - x₀)) < r → converges_at (x - x₀) s}


/--
 - A power series is the function associated with a formal power series by taking infinite sums. I may or may not converge.
 -/
noncomputable def at_point (s : formal_power_series R) (x : R) :=
∑ n : ℕ , s n * x ^ n

-- noncomputable instance : has_coe_to_fun (formal_power_series R) :=
-- ⟨λ _, R → R,
--   λ s x, s.at_point x⟩

end formal_power_series

variable {R : Type*}
variables [normed_ring R]
open lattice topological_space

/--
 - A function f defined on an open subset of R is analytic if it can
 - locally be written as a convergent power series.
 -
 - This definition is not done yet.
 -/
def is_analytic_at (x₀ : R) (f : R → R) : Prop :=
∃ (s : formal_power_series R) (r > 0), ∀ x : R, norm(x - x₀) < r → s.converges_at_to (x - x₀) (f x)

#print is_analytic_at.

def is_analytic_on (U : set R) (f : R → R) : Prop :=
∀ x ∈ U, is_analytic_at x f


-- class is_analytic (U : opens R) (f : U → R) : Prop :=
-- (prop : ∀ x ∈ U,  ∃ (s : formal_power_series R) (x₀ : R), convergence_radius s x₀ > 0 ∧ ↑(nnnorm (x - x₀)) < convergence_radius s x₀ ∧  some (f ⟨x, ‹x ∈ U›⟩) = power_series s (x - x₀) )

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

