import analysis.topology.topological_space
import analysis.topology.continuity
import analysis.topology.topological_structures
import data.set.basic
import analysis.real
import tactic.wlog
import connected_space

open set
open function
open tactic

universes u v

section intervals

variables {α : Type*} [partial_order α] {i : set α}

/-- an interval is a convex set -/
def interval (i : set α) : Prop := ∀x y z, x ∈ i → z ∈ i → x ≤ y → y ≤ z → y ∈ i

/-- Left-open right-closed interval -/
def Ioc (a b : α) := {x | a < x ∧ x ≤ b}

/-- Left-infinite right-open interval -/
def Iic (a : α) := {x | x ≤ a}

/-- Left-open right-infinite interval -/
def Ioi (b : α) := {x | b < x}


lemma Iio_inter_Ioi_empty {b : ℝ} : Iio b ∩ Ioi b = ∅ :=
classical.by_contradiction
    (assume h : Iio b ∩ Ioi b ≠ ∅,
    let ⟨x, _⟩ := exists_mem_of_ne_empty h in
    have x < b, from mem_of_mem_inter_left  ‹x ∈ Iio b ∩ Ioi b›,
    have b < x, from mem_of_mem_inter_right ‹x ∈ Iio b ∩ Ioi b›,
    show false, from not_le_of_lt ‹x < b› (le_of_lt ‹b < x›))

lemma neg_Ioi_eq_Iio {b : ℝ} : (λ (x : ℝ), -x)⁻¹' (Iio (-b)) = Ioi b := sorry

lemma is_open_Ioi {b : ℝ} : is_open (Ioi b) :=
let neg := λ (x : ℝ), -x in
have continuous neg, from topological_ring.continuous_neg ℝ,
@neg_Ioi_eq_Iio b ▸ ‹continuous neg› (Iio (-b)) is_open_Iio


--Classification of bounded above intervals
lemma exists_smaller_of_not_bounded_below {i : set ℝ} (_ : ¬bdd_below i) (x : ℝ) : ∃ y ∈ i, y ≤ x :=
have h : ∀ y, ¬∀ z ∈ i, y ≤ z, by rw [←not_exists]; assumption,
have ¬∀ z ∈ i, x ≤ z, from h x,
have ∃ z, ¬(z ∈ i → x ≤ z), by rw [←classical.not_forall]; assumption,
let ⟨z, h1⟩ := this in
have h2 : z ∈ i ∧ ¬x ≤ z, from (@not_imp _ _ (classical.dec (z ∈ i))).mp h1,
⟨z, h2.left, le_of_not_le h2.right⟩ 

lemma exists_real_between {x y : ℝ} (_ : x < y) : ∃z, x < z ∧ z < y :=
suffices Ioo x y ≠ ∅, from exists_mem_of_ne_empty this,
mt Ioo_eq_empty_iff.mp (not_le_of_lt ‹x < y›)

theorem exists_inf (S : set ℝ) : (∃ x, x ∈ S) → (∃ x, ∀ y ∈ S, x ≤ y) →
  ∃ x, ∀ y, y ≤ x ↔ ∀ z ∈ S, y ≤ z := sorry

lemma mem_nbhd_sup_of_right_open {i : set ℝ} {x sup : ℝ} (_ : sup ∉ i) (_ : x < sup)
  (bound_iff_ge_sup : ∀ b, sup ≤ b ↔ ∀ y ∈ i, y ≤ b) : ∃ z ∈ i, x ≤ z :=
have le_sup : ∀ x ∈ i, x ≤ sup, from (bound_iff_ge_sup sup).mp (le_refl sup),
have i ∩ Ioo x sup ≠ ∅, from
  assume _ : i ∩ Ioo x sup = ∅, --show that a smaller supremum exists
  let ⟨sup2, _⟩ := exists_real_between ‹x < sup› in
  have ∀ z ∈ i, z ≤ sup2, from
    assume z,
    assume _ : z ∈ i,
    le_of_not_lt $
      assume _ : z > sup2,
      have z ≠ sup, from assume _ : z = sup, ‹sup ∉ i› $ ‹z = sup› ▸ ‹z ∈ i›,
      have z < sup, from lt_of_le_of_ne (le_sup z ‹z ∈ i›) ‹z ≠ sup›,
      have z ∈ Ioo x sup, from ⟨lt_trans ‹x < sup2 ∧ sup2 < sup›.left ‹sup2 < z›, ‹z < sup›⟩,
      have z ∈ i ∩ Ioo x sup, from mem_inter ‹z ∈ i› ‹z ∈ Ioo x sup›,
      show false, from eq_empty_iff_forall_not_mem.mp ‹i ∩ Ioo x sup = ∅› z ‹z ∈ i ∩ Ioo x sup›,
have sup ≤ sup2, from (bound_iff_ge_sup sup2).mpr this,
show false, from (not_le_of_lt ‹x < sup2 ∧ sup2 < sup›.right) ‹sup ≤ sup2›,
let ⟨z, _⟩ := exists_mem_of_ne_empty ‹i ∩ Ioo x sup ≠ ∅› in
have z ∈ i, from mem_of_mem_inter_left ‹z ∈ i ∩ Ioo x sup›,
have x ≤ z, from le_of_lt (mem_of_mem_inter_right ‹z ∈ i ∩ Ioo x sup›).left,
⟨z, ‹z ∈ i›, ‹x ≤ z›⟩

lemma mem_nbhd_inf_of_left_open {i : set ℝ} {x inf : ℝ} (_ : inf ∉ i) (_ : inf < x)
  (bound_iff_le_inf : ∀ b, b ≤ inf ↔ ∀ y ∈ i, b ≤ y) : ∃ z ∈ i, z ≤ x := sorry


theorem bdd_above_interval_iff {i : set ℝ} (_ : bdd_above i) (_ : i ≠ ∅) : interval i ↔
∃b, i = Iic b ∨ i = Iio b ∨ ∃a, i = Icc a b ∨ i = Ioc a b ∨ i = Ico a b ∨ i = Ioo a b :=
iff.intro
  (assume _ : interval i,
  have ∃ sup, ∀ bound, sup ≤ bound ↔ ∀ x ∈ i, x ≤ bound, from
    real.exists_sup i (set.exists_mem_of_ne_empty ‹i ≠ ∅›) ‹bdd_above i›,
  let ⟨sup, bound_iff_ge_sup⟩ := this in
  have le_sup : ∀ x ∈ i, x ≤ sup, from (bound_iff_ge_sup sup).mp $ le_refl sup,
  ⟨sup, classical.by_cases
    (assume _ : bdd_below i, /-left-bounded cases-/
    have ∃ inf, ∀ bound, bound ≤ inf ↔ ∀ x ∈ i, bound ≤ x, from
      exists_inf i (set.exists_mem_of_ne_empty ‹i ≠ ∅›) ‹bdd_below i›,
    let ⟨inf, bound_iff_le_inf⟩ := this in
    have ge_inf : ∀ x ∈ i, inf ≤ x, from (bound_iff_le_inf inf).mp $ le_refl inf,
    or.intro_right (i = Iic sup) $ or.intro_right (i = Iio sup)
    ⟨inf, classical.by_cases
      (assume _ : sup ∈ i,
      classical.by_cases
        (assume _ : inf ∈ i, --left-closed right-closed case
        have i = Icc inf sup, from ext $
          assume x,
          iff.intro
            (assume _ : x ∈ i, ⟨ge_inf x ‹x ∈ i›, le_sup x ‹x ∈ i›⟩)
            (assume _ : x ∈ Icc inf sup, ‹interval i› inf x sup ‹inf ∈ i› ‹sup ∈ i› ‹x ∈ Icc inf sup›.left ‹x ∈ Icc inf sup›.right),
        by simp [this])
        (assume _ : inf ∉ i, --left-open right-closed case
        have gt_inf : ∀ x ∈ i, inf < x, from assume x, assume _ : x ∈ i, --DUPLICATE
          lt_of_le_of_ne (ge_inf x ‹x ∈ i›) $ ne.symm $ ne_of_mem_of_not_mem ‹x ∈ i› ‹inf ∉ i›,
        have i = Ioc inf sup, from ext $
          assume x,
          iff.intro
            (assume _ : x ∈ i, ⟨gt_inf x ‹x ∈ i›, le_sup x ‹x ∈ i›⟩)
            (assume _ : x ∈ Ioc inf sup,
            let ⟨z, _, _⟩ := mem_nbhd_inf_of_left_open ‹inf ∉ i› ‹inf < x ∧ x ≤ sup›.left bound_iff_le_inf in
            ‹interval i› z x sup ‹z ∈ i› ‹sup ∈ i› ‹z ≤ x› ‹x ∈ Ioc inf sup›.right),
        by simp [this]))
      (assume _ : sup ∉ i,
      have lt_sup : ∀ x ∈ i, x < sup, from assume x, assume _ : x ∈ i, --DUPLICATE
          lt_of_le_of_ne (le_sup x ‹x ∈ i›) $ ne_of_mem_of_not_mem ‹x ∈ i› ‹sup ∉ i›,
      classical.by_cases
        (assume _ : inf ∈ i, --left-closed right-open case
        have i = Ico inf sup, from ext $
          assume x,
          iff.intro
            (assume _ : x ∈ i, ⟨ge_inf x ‹x ∈ i›, lt_sup x ‹x ∈ i›⟩)
            (assume _ : x ∈ Ico inf sup,
            let ⟨z, _, _⟩ := mem_nbhd_sup_of_right_open ‹sup ∉ i› ‹inf ≤ x ∧ x < sup›.right bound_iff_ge_sup in
            ‹interval i› inf x z ‹inf ∈ i› ‹z ∈ i› ‹x ∈ Ico inf sup›.left ‹x ≤ z›),
        by simp [this])
        (assume _ : inf ∉ i, --left-open right-open case
        have gt_inf : ∀ x ∈ i, inf < x, from assume x, assume _ : x ∈ i, --DUPLICATE
          lt_of_le_of_ne (ge_inf x ‹x ∈ i›) $ ne.symm $ ne_of_mem_of_not_mem ‹x ∈ i› ‹inf ∉ i›,
        have i = Ioo inf sup, from ext $
          assume x,
          iff.intro
            (assume _ : x ∈ i, ⟨gt_inf x ‹x ∈ i›, lt_sup x ‹x ∈ i›⟩)
            (assume _ : x ∈ Ioo inf sup,
            let ⟨z1, _, _⟩ := mem_nbhd_inf_of_left_open ‹inf ∉ i› ‹inf < x ∧ x < sup›.left bound_iff_le_inf in
            let ⟨z2, _, _⟩ := mem_nbhd_sup_of_right_open ‹sup ∉ i› ‹inf < x ∧ x < sup›.right bound_iff_ge_sup in
            ‹interval i› z1 x z2 ‹z1 ∈ i› ‹z2 ∈ i› ‹z1 ≤ x› ‹x ≤ z2›),
        by simp [this]))⟩)
    (assume _ : ¬bdd_below i, /-left-infinite cases-/
    classical.by_cases
      --left-infinite right-closed case
      (assume _ : sup ∈ i,
      have i = Iic sup, from ext $
        assume x,
        let ⟨y, _, _⟩ := exists_smaller_of_not_bounded_below ‹¬bdd_below i› x in
        iff.intro
          (assume _ : x ∈ i, le_sup x ‹x ∈ i›)
          (assume _ : x ∈ Iic sup, ‹interval i› y x sup ‹y ∈ i› ‹sup ∈ i› ‹y ≤ x› ‹x ∈ Iic sup›),
      by simp [this]) --add the large disjunction
      --left-infinite right-open cases
      (assume _ : sup ∉ i,
      have i = Iio sup, from ext $
        assume x,
        let ⟨y, _, _⟩ := exists_smaller_of_not_bounded_below ‹¬bdd_below i› x in
        iff.intro
          (assume _ : x ∈ i,
          have x ≠ sup, from ne_of_mem_of_not_mem ‹x ∈ i› ‹sup ∉ i›,
          lt_of_le_of_ne (le_sup x ‹x ∈ i›) ‹x ≠ sup›)
          (assume _ : x ∈ Iio sup,
          let ⟨z, _, _⟩ := mem_nbhd_sup_of_right_open ‹sup ∉ i› ‹x < sup› bound_iff_ge_sup in
          ‹interval i› y x z ‹y ∈ i› ‹z ∈ i› ‹y ≤ x› ‹x ≤ z›),
      by simp [this]))⟩) --add the large disjunction
  --(begin
  --intros h,
  --cases h with b h1,
  --cases h1 with hic h2,
  --show interval i, from (assume x y z _ _ _ _, eq.symm hic ▸ le_trans ‹y ≤ z› (show z ∈ Iic b, from (hic ▸ ‹z ∈ i›)))
  sorry
  --end)


end intervals


section real
variables {i: set ℝ} {s₁ s₂: set ℝ}
variables {t : topological_space ℝ}

def has_max (S : set ℝ) : Prop := ∃ max ∈ S, ∀ x ∈ S, x ≤ max

/- A closed subset of ℝ that is bounded from above has a maximum. -/
lemma has_max_of_closed_bdd_above {S : set ℝ} (_ : is_closed S) (_ : bdd_above S) (_ : S ≠ ∅) : has_max S :=
-- a set that is bounded from above has a supremum
-- if that supremum is contained in the set, it is the maximum
have ∃ sup, ∀ bound, sup ≤ bound ↔ ∀ x ∈ S, x ≤ bound, from
  real.exists_sup S (set.exists_mem_of_ne_empty ‹S ≠ ∅›) ‹bdd_above S›,
let ⟨sup, bound_iff_ge_sup⟩ := this in
suffices sup ∈ S, from exists.intro sup ⟨‹sup ∈ S›, (bound_iff_ge_sup sup).mp (le_refl sup)⟩,
classical.by_contradiction
  -- we now show that the supremum is contained in the set
  -- for that we use that, since -S is open, sup ∈ -S implies that there is a metric ball around it that's not in S
  -- anything left of the supremum will be smaller than the sup, but still bound S
  -- this contradicts the assumptions
  (assume : sup ∉ S, show false, from
    have ∃ ε > 0, ball sup ε ⊆ -S, from is_open_metric.mp ‹is_open (-S)› sup ‹sup ∈ -S›,
    let ⟨ε, _, _⟩ := this in
      suffices ∀ x ∈ S, x ≤ sup - ε, from
        have ¬(sup ≤ sup - ε), from not_le_of_lt (show sup - ε < sup, by linarith),
        have (sup ≤ sup - ε), from ((bound_iff_ge_sup (sup - ε)).mpr ‹∀ x ∈ S, x ≤ sup - ε›),
        absurd this ‹¬(sup ≤ sup - ε)›,
      assume x (_ : x ∈ S),
      classical.by_contradiction
        (assume : ¬ x ≤ sup - ε, 
          have x ≤ sup, from (bound_iff_ge_sup sup).mp (le_refl sup) x ‹x ∈ S›,
          have 0 ≤ sup - x, by linarith,
          have dist x sup < ε, from 
            calc dist x sup = abs (sup - x) : by rw[dist_comm x sup]; refl
                        ... = sup - x : abs_of_nonneg ‹0 ≤ sup - x›
                        ... < ε : by linarith,
          have x ∈ -S, from mem_of_subset_of_mem ‹ball sup ε ⊆ -S› ‹x ∈ ball sup ε›,
          absurd ‹x ∈ S› ‹x ∈ -S›))

lemma sup_in_closed {S : set ℝ} (_ : is_closed S) (_ : bdd_above S) (_ : S ≠ ∅) : real.Sup S ∈ S :=
have has_max S, from has_max_of_closed_bdd_above ‹is_closed S› ‹bdd_above S› ‹S ≠ ∅›,
let ⟨max, (_ : max ∈ S), max_upper_bound⟩ := this in
have max ≤ real.Sup S, from real.le_Sup S ‹bdd_above S› ‹max ∈ S›,
have real.Sup S ≤ max, from (real.Sup_le S (set.exists_mem_of_ne_empty ‹S ≠ ∅›) ‹bdd_above S›).mpr max_upper_bound,
have max = real.Sup S, from le_antisymm ‹max ≤ real.Sup S› ‹real.Sup S ≤ max›,
show real.Sup S ∈ S, from ‹max = real.Sup S› ▸ ‹max ∈ S› 

lemma mem_iff_neg_mem {S : set ℝ} {x : ℝ} : -x ∈ S ↔ x ∈ {y | -y ∈ S} :=
by rw mem_set_of_eq

lemma bdd_above_iff_neg_bdd_below {S : set ℝ} : bdd_below S ↔ bdd_above {x | -x ∈ S} :=
iff.intro
  (assume ⟨y, h⟩, --S is bounded from below by y
    ⟨-y,
    assume x,
    assume _ : x ∈ {x | -x ∈ S},
    have -x ∈ S, by rwa [mem_iff_neg_mem],
    neg_neg x ▸ neg_le_neg (h (-x) ‹-x ∈ S›)⟩)
  (assume ⟨y, h⟩, --{x | -x ∈ S} is bounded from above by y
    ⟨-y,
    assume x,
    assume _ : x ∈ S,
    have -x ∈ {x | -x ∈ S}, by simp [‹x ∈ S›], --how to do this by def?
    neg_neg x ▸ neg_le_neg (h (-x) ‹-x ∈ {x | -x ∈ S}›)⟩)

lemma bdd_above_Icc {a b : ℝ} : bdd_above (Icc a b) :=
⟨b, by intros; exact (mem_def.mp ‹y ∈ Icc a b›).right⟩

lemma bdd_below_Icc {a b : ℝ} : bdd_below (Icc a b) :=
⟨a, by intros; exact (mem_def.mp ‹y ∈ Icc a b›).left⟩

lemma neg_closed {S : set ℝ} (_ : is_closed S) : is_closed {x | -x ∈ S} :=
let neg := λ (x : ℝ), -x in
have continuous neg, from topological_ring.continuous_neg ℝ,
show is_closed (neg ⁻¹' S), from continuous_iff_is_closed.mp ‹continuous neg› S ‹is_closed S›

lemma inf_in_closed {S : set ℝ} (_ : is_closed S) (_ : bdd_below S) (_ : S ≠ ∅) : real.Inf S ∈ S :=
let neg := λ (x : ℝ), -x in
let ⟨x, h⟩ := ne_empty_iff_exists_mem.mp ‹S ≠ ∅› in
have {x | -x ∈ S} ≠ ∅, from ne_empty_iff_exists_mem.mpr ⟨-x, mem_iff_neg_mem.mp (eq.symm (neg_neg x) ▸ h)⟩,
sup_in_closed
  (neg_closed ‹is_closed S›)
  (bdd_above_iff_neg_bdd_below.mp ‹bdd_below S›)
  ‹{x | -x ∈ S} ≠ ∅›

lemma inter_sep_comp_eq {α : Type u} {s s₁ s₂ : set α} (_ : s ∩ s₁ ∩ s₂ = ∅) (_ : s ⊆ s₁ ∪ s₂) : s ∩ s₁ = s ∩ -s₂ :=
have s ∩ s₁ ⊆ s ∩-s₂, by simpa [subset_compl_iff_disjoint],
have s ∩-s₂ ⊆ s ∩ s₁, from
calc s ∩-s₂ ⊆ s ∩ ((s₁ ∪ s₂) ∩ -s₂) : by simp [inter_subset_inter_left, ‹s ⊆ s₁ ∪ s₂›]
        ... ⊆ s ∩ s₁                : by simp [inter_subset_inter_right, inter_distrib_right],
eq_of_subset_of_subset ‹s ∩ s₁ ⊆ s ∩ -s₂› ‹s ∩-s₂ ⊆ s ∩ s₁›


lemma subset_separation_left_inter_closed {α : Type u} {s s₁ s₂ c : set α} [topological_space α]
  (sub_sep : subset_separation s s₁ s₂) (_ : is_closed c) (_ : c ⊆ s) : is_closed (s₁ ∩ c) :=
let ⟨_, _, _, _, _, _⟩ := sub_sep in
let lift := @subtype.val α s in
have sep : @separation s _ (lift⁻¹' s₁) (lift⁻¹' s₂), from sep_of_subset_sep sub_sep,
have h : lift⁻¹' s₁ = lift⁻¹' -s₂, by rw [sep_neg sep, eq.symm preimage_compl],
have is_closed (-s₂), by rw [show is_closed (-s₂) = is_open ( - - s₂), by refl]; rwa [compl_compl s₂],
have s₁ ∩ s = -s₂ ∩ s, from
  calc s₁ ∩ s = lift '' (lift⁻¹' s₁)  : by rw [inter_comm, image_preimage_subtype_val s₁]
          ... = lift '' (lift⁻¹' -s₂) : by rw h
          ... = -s₂ ∩ s               : by rw [image_preimage_subtype_val (-s₂), inter_comm],
have s₁ ∩ c = -s₂ ∩ c, from
  calc s₁ ∩ c =  s₁ ∩ s ∩ c : by rw [inter_assoc, inter_eq_self_of_subset_right ‹c ⊆ s›]
          ... = -s₂ ∩ s ∩ c : by rw [←‹s₁ ∩ s = -s₂ ∩ s›]
          ... = -s₂ ∩ c     : by rw [inter_assoc, inter_eq_self_of_subset_right ‹c ⊆ s›],
eq.symm this ▸ (is_closed_inter ‹is_closed (-s₂)› ‹is_closed c›)


lemma subset_separation_right_inter_closed {α : Type u} {s s₁ s₂ c : set α} [topological_space α]
  (sep : subset_separation s s₁ s₂) (_ : is_closed c) (_ : c ⊆ s) : is_closed (s₂ ∩ c) :=
subset_separation_left_inter_closed (subset_sep_symm sep) ‹is_closed c› ‹c ⊆ s›


set_option eqn_compiler.zeta true

-- An convex subset of ℝ is connected in the subspace topology
instance connected_of_interval {i : set ℝ} (_ : interval i) : connected_space' i :=
subtype_connected_iff_subset_connected.mpr $
-- assume that i is not connected, then there exists a separation
assume _ : disconnected_subset i,
  have ∃ (s₁ : set ℝ) (s₂ : set ℝ) (a ∈ s₁ ∩ i) (b ∈ s₂ ∩ i), a < b ∧ subset_separation i s₁ s₂,
    from (
      let ⟨s₁, s₂, sep⟩ := ‹disconnected_subset i›,
          ⟨_, _, _, _, _, _⟩ := sep,
          ⟨a, _⟩ := exists_mem_of_ne_empty ‹s₁ ∩ i ≠ ∅›,
          ⟨b, _⟩ := exists_mem_of_ne_empty ‹s₂ ∩ i ≠ ∅› in
      have a ≠ b, from (assume _ : a = b,
      have b ∈ s₁ ∩ s₂ ∩ i, from ⟨⟨‹a = b› ▸ (‹a ∈ s₁ ∩ i›.1), (‹b ∈ s₂ ∩ i›).1⟩, (‹b ∈ s₂ ∩ i›.2)⟩,
      show false, from eq_empty_iff_forall_not_mem.1 ‹s₁ ∩ s₂ ∩ i = ∅› b ‹b ∈ s₁ ∩ s₂ ∩ i›),
      or.elim (ne_iff_lt_or_gt.mp ‹a ≠ b›)
        (assume _, ⟨s₁, s₂, a, ‹_›, b, ‹_›, ⟨‹_›, sep⟩⟩)
        (assume _, ⟨s₂, s₁, b, ‹_›, a, ‹_›, ⟨‹_›, subset_sep_symm sep⟩⟩)),
  let ⟨s₁, s₂, a, ⟨_, _⟩, b, ⟨_, _⟩, ⟨(_ : a < b), sep⟩⟩ := this,
      ⟨_, _, _, _, _, _⟩ := sep in
      have Icc a b ⊆ i, from
        (suffices (∀x, x ∈ Icc a b → x ∈ i), by simpa only [subset_def],
        assume x,
        assume _ : x ∈ Icc a b, 
        have hab : a ≤ x ∧ x ≤ b, from mem_set_of_eq.mp ‹x ∈ Icc a b›,
        show x ∈ i, from ‹interval i› a x b ‹a ∈ i› ‹b ∈ i› hab.1 hab.2),
      let s₁' := s₁ ∩ Icc a b, s₂' := s₂ ∩ Icc a b in
      have s₁' ∪ s₂' = Icc a b, from
        (calc  s₁' ∪ s₂' = (s₁ ∪ s₂) ∩ Icc a b : eq.symm (inter_distrib_right s₁ s₂ (Icc a b))
                     ... = Icc a b             : inter_eq_self_of_subset_right (subset.trans ‹Icc a b ⊆ i› ‹i ⊆ s₁ ∪ s₂›)),
      let sup := real.Sup s₁' in
      have is_closed s₁', from subset_separation_left_inter_closed sep is_closed_Icc ‹Icc a b ⊆ i›,
      have is_closed s₂', from subset_separation_right_inter_closed sep is_closed_Icc ‹Icc a b ⊆ i›,

      have bdd_above s₁', from bdd_above_Int2 bdd_above_Icc,
      have s₁' ≠ ∅, from ne_empty_of_mem (⟨‹a ∈ s₁›, mem_set_of_eq.mpr ⟨le_refl a, le_of_lt ‹a < b›⟩⟩),
      have sup ∈ s₁', from sup_in_closed ‹is_closed s₁'› ‹bdd_above s₁'› ‹s₁' ≠ ∅›,
      have sup ∈ Icc a b, from mem_of_mem_inter_right ‹sup ∈ s₁'›,
      have sup ∈ i, from mem_of_subset_of_mem ‹Icc a b ⊆ i› ‹sup ∈ Icc a b›,

      have sup ≤ b, from (mem_def.mp ‹sup ∈ Icc a b›).2,
      let s₂'' := s₂' ∩ Icc sup b in
      let inf := real.Inf s₂'' in

      have is_closed s₂'', from is_closed_inter ‹is_closed s₂'› is_closed_Icc,
      have bdd_below s₂', from bdd_below_Int2 bdd_below_Icc,
      have bdd_below s₂'', from bdd_below_Int1 ‹bdd_below s₂'›,
      have b ∈ s₂', from ⟨‹b ∈ s₂›, mem_set_of_eq.mpr ⟨le_of_lt ‹a < b›, le_refl b⟩⟩,
      have s₂'' ≠ ∅, from ne_empty_of_mem ⟨‹b ∈ s₂'›, mem_set_of_eq.mpr ⟨‹sup ≤ b›, le_refl b⟩⟩,
      have inf ∈ s₂'', from inf_in_closed ‹is_closed s₂''› ‹bdd_below s₂''› ‹s₂'' ≠ ∅›,
      have inf ∈ Icc a b, from mem_of_mem_inter_right $ mem_of_mem_inter_left ‹inf ∈ s₂''›,
      have inf ∈ i, from mem_of_subset_of_mem ‹Icc a b ⊆ i› ‹inf ∈ Icc a b›,

      have sup ≤ inf, from (mem_def.mp (mem_of_mem_inter_right ‹inf ∈ s₂''›)).left,
      have sup < inf, from lt_of_le_of_ne ‹sup ≤ inf› $ ne.intro
        (assume _ : sup = inf,
        have inf ∈ s₁', from ‹sup = inf› ▸ ‹sup ∈ s₁'›,
        have inf ∈ s₁ ∩ s₂ ∩ i, from ⟨⟨mem_of_mem_inter_left ‹inf ∈ s₁'›, mem_of_mem_inter_left $ mem_of_mem_inter_left ‹inf ∈ s₂''›⟩, ‹inf ∈ i›⟩,
        show false, from mem_empty_eq inf ▸ ‹s₁ ∩ s₂ ∩ i = ∅› ▸ ‹inf ∈ s₁ ∩ s₂ ∩ i›),
      
      let ⟨z, ⟨(_ : sup < z), (_ : z < inf)⟩⟩ := exists_real_between ‹sup < inf› in
      have z ∈ Ioo sup inf, from mem_set_of_eq.mp (and.intro ‹sup < z› ‹z < inf›),
      have z ∈ i, from ‹interval i› sup z inf ‹sup ∈ i› ‹inf ∈ i› (le_of_lt ‹sup < z›) (le_of_lt ‹z < inf›),
      have z ∈ s₁ ∪ s₂, from mem_of_subset_of_mem ‹i ⊆ s₁ ∪ s₂› ‹z ∈ i›,
      have a ≤ z, from le_trans ‹sup ∈ Icc a b›.left (le_of_lt ‹sup < z›),
      have z ≤ b, from le_trans (le_of_lt ‹z < inf›) ‹inf ∈ Icc a b›.right,
      show false, from mem_union.elim ‹z ∈ s₁ ∪ s₂›
        (assume _ : z ∈ s₁,
        have z ∈ s₁', from mem_inter ‹z ∈ s₁› $ and.intro ‹a ≤ z› ‹z ≤ b›,
        have z ≤ sup, from real.le_Sup s₁' ‹bdd_above s₁'› ‹z ∈ s₁'›,
        not_lt_of_le ‹z ≤ sup› ‹sup < z›)
        (assume _ : z ∈ s₂,
        have z ∈ s₂', from mem_inter ‹z ∈ s₂› $ and.intro ‹a ≤ z› ‹z ≤ b›,
        have z ∈ s₂'', from mem_inter ‹z ∈ s₂'› $ and.intro (le_of_lt ‹sup < z›) ‹z ≤ b›,
        have z ≥ inf, from real.Inf_le s₂'' ‹bdd_below s₂''› ‹z ∈ s₂''›,
        not_le_of_gt ‹inf > z› ‹inf ≤ z›)




theorem interval_of_connected {i : set ℝ} [connected_space' i] : interval i :=
by intros x y z _ _ _ _;
exact
  classical.by_cases
    (assume h : x = y ∨ y = z,
    or.elim h
      (assume _ : x = y, ‹x = y› ▸ ‹x ∈ i›)
      (assume _ : y = z, eq.symm ‹y = z› ▸ ‹z ∈ i›))
    (assume _ : ¬(x = y ∨ y = z),
    have x ≠ y ∧ y ≠ z, from not_or_distrib.mp ‹¬(x = y ∨ y = z)›,
    have x < y, from lt_of_le_of_ne ‹x ≤ y› ‹x ≠ y ∧ y ≠ z›.left,
    have y < z, from lt_of_le_of_ne ‹y ≤ z› ‹x ≠ y ∧ y ≠ z›.right,
    classical.by_contradiction
    (assume _ : y ∉ i,
    have Iio y ∩ Ioi y ∩ i = ∅, from
      calc Iio y ∩ Ioi y ∩ i = ∅ ∩ i : by rw [Iio_inter_Ioi_empty]
                         ... = ∅     : empty_inter i,
    have i ⊆ Iio y ∪ Ioi y, from subset_def.mpr
      (assume a,
      assume _ : a ∈ i,
      have a ≠ y, from ne_of_mem_of_not_mem ‹a ∈ i› ‹y ∉ i›,
      or.elim (ne_iff_lt_or_gt.mp ‹a ≠ y›)
        (assume _ : a < y, mem_union_left  (Ioi y) ‹a < y›)
        (assume _ : a > y, mem_union_right (Iio y) ‹y < a›)),
    have Iio y ∩ i ≠ ∅, from ne_empty_of_mem (mem_inter ‹x < y› ‹x ∈ i›),
    have Ioi y ∩ i ≠ ∅, from ne_empty_of_mem (mem_inter ‹y < z› ‹z ∈ i›),
    have disconnected_subset i, from ⟨Iio y, Ioi y, is_open_Iio, is_open_Ioi, ‹Iio y ∩ i ≠ ∅›, ‹Ioi y ∩ i ≠ ∅›, ‹Iio y ∩ Ioi y ∩ i = ∅›, ‹i ⊆ Iio y ∪ Ioi y›⟩,
    have ¬connected_space' i, by simpa [subtype_connected_iff_subset_connected],
    this ‹connected_space' i›))


end real
