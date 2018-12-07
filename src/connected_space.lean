import analysis.topology.topological_space
import analysis.topology.continuity
import analysis.topology.topological_structures
import data.set.basic
import analysis.real

open set
open function
open tactic

universes u v

variables {α: Type u} {β : Type v}
variables [topological_space α]
variables [topological_space β]
variables {a : α} {b : β}
variables {s s₁ s₂ : set α} {r r₁ r₂ : set β}
variables {f : α → β}

--- Usefull lemma's about the inclusion map
lemma image_preimage_subtype_val {s : set α} (t : set α) :
  subtype.val '' (@subtype.val α s ⁻¹' t) = s ∩ t :=
begin
  rw [image_preimage_eq_inter_range, inter_comm, subtype_val_range],
  exact set_of_mem,
end

lemma subtype_val_univ_eq (s : set α) : (subtype.val) '' (@univ s) = s :=
calc
  subtype.val '' (@univ s) = range subtype.val : image_univ
                       ... = s                 : subtype_val_range

lemma preimage_subtype_val_eq_univ (s : set α) : @univ s = (@subtype.val _ s) ⁻¹' s :=
let lift := @subtype.val α s in
calc
  @univ s = lift ⁻¹' univ                      : by rw set.preimage_univ
      ... = lift ⁻¹' (lift '' (lift ⁻¹' univ)) : by rw set.preimage_image_preimage
      ... = lift ⁻¹' (s ∩ univ)                : by rw image_preimage_subtype_val
      ... = lift ⁻¹' s                         : by rw inter_univ s

lemma preimage_subtype_val_empty_iff {s : set α} (t : set α) :
  @subtype.val α s ⁻¹' t = ∅ ↔ s ∩ t = ∅ :=
by rw [←image_preimage_subtype_val, image_eq_empty]

lemma preimage_subtype_val_ne_empty_iff {s : set α} (t : set α) :
  @subtype.val α s ⁻¹' t ≠ ∅ ↔ s ∩ t ≠ ∅ :=
not_iff_not_of_iff (preimage_subtype_val_empty_iff t)

lemma mem_image_inter_iff {f : α → β} : (∃ x : α, x ∈ s ∩ (f ⁻¹' r)) ↔ ∃ y : β, y ∈ (f '' s) ∩ r :=
iff.intro
  (assume h : ∃ x, x ∈ s ∩ (f ⁻¹' r),
   let ⟨x, _, _⟩ := h in
   show ∃ y, y ∈ (f '' s) ∩ r, from ⟨f x, ⟨x, ‹x ∈ s›, rfl⟩, ‹x ∈ f ⁻¹' r›⟩)
  (assume h : ∃ y, y ∈ (f '' s) ∩ r,
   let ⟨y, _, _⟩ := h in
   have ∃ x, x ∈ s ∧ f x = y, from ‹y ∈ f '' s›,
   let ⟨x, _, _⟩ := this in
   have x ∈ f ⁻¹' r, by rw [mem_preimage_eq, ‹f x = y›]; assumption,
   show ∃ x, x ∈ s ∩ (f ⁻¹' r), from ⟨x, ‹x ∈ s›, ‹x ∈ f ⁻¹' r›⟩)

lemma image_connected [continuous f] [is_connected s] : is_connected (f '' s) :=
-- We take arbitrary sets U and V of β
assume U : set β,
assume V : set β,
-- Assuming U is open we get that f ⁻¹' U is open
assume _ : is_open U,
have h₁ : is_open (f ⁻¹' U), from ‹continuous f› U ‹is_open U›,
-- Assuming V is open we get that f ⁻¹' V is open
assume _ : is_open V,
have h₂ : is_open (f ⁻¹' V), from ‹continuous f› V ‹is_open V›,
-- Assuming that (f '' s) ⊆ U ∪ V we get that s ⊆ (f ⁻¹' U) ∪ (f ⁻¹' V)
assume _ : f '' s ⊆ U ∪ V,
have h₃ : s ⊆ (f ⁻¹' U) ∪ (f ⁻¹' V),
  by rw [←preimage_union, ←image_subset_iff]; assumption,
-- Assuming (f '' s) ∩ U is non-empty we get that s ∩ (f ⁻¹' U) is non-empty
assume h₄' : ∃ y : β, y ∈ (f '' s) ∩ U,
have h₄ : ∃ x : α, x ∈ s ∩ (f ⁻¹' U), by rw mem_image_inter_iff; assumption,
-- Assuming (f '' s) ∩ V is non-empty we get that s ∩ (f ⁻¹' V) is non-empty
assume _ : ∃ y : β, y ∈ (f '' s) ∩ V,
have h₅ : ∃ x : α, x ∈ s ∩ (f ⁻¹' V), by rw mem_image_inter_iff; assumption,
-- Applying connectedness of s to f ⁻¹' U and f ⁻¹' V with our assumptions
-- tells us that s ∩ (f ⁻¹' U) ∩ (f ⁻¹' V) is non-empty
have ∃ x : α, x ∈ s ∩ ((f ⁻¹' U) ∩ (f ⁻¹' V)),
  from ‹is_connected s› (f ⁻¹' U) (f ⁻¹' V) h₁ h₂ h₃ h₄ h₅,
show ∃ y : β, y ∈ (f '' s) ∩ (U ∩ V),
  begin
    rw ←mem_image_inter_iff,
    fapply exists_imp_exists,
    exact λ x, x ∈ s ∩ ((f ⁻¹' U) ∩ (f ⁻¹' V)),
    intros,
    rw preimage_inter,
    assumption,
    assumption,
  end
-- This proves that f '' s is connected.

set_option eqn_compiler.zeta true

instance connected_subset [is_connected s] : connected_space s :=
⟨let lift := @subtype.val _ s in
 -- Start with arbitrary subsets of s
 assume U : set s,
 assume V : set s,
 -- We have an open set U' containing U if U is open in s
 assume _ : is_open U,
 have ∃ U' : set α, is_open U' ∧ U = lift ⁻¹' U', from ‹is_open U›,
 let ⟨U', h₁, _⟩ := this in
 -- We have an open set V' containing V if V is open in s
 assume _ : is_open V,
 have ∃ V' : set α, is_open V' ∧ V = lift ⁻¹' V', from ‹is_open V›,
 let ⟨V', h₂, _⟩ := this in
 -- Assuming the universe of s is contained in the union of U and V,
 -- s will be contained in the union of U' and V'
 assume _ : univ ⊆ U ∪ V,
 have h₃ : s ⊆ U' ∪ V',
   by rw [←(subtype_val_univ_eq s), image_subset_iff, preimage_union,
          ←‹U = lift ⁻¹' U'›, ←‹V = lift ⁻¹' V'›]; assumption,
 -- Assuming that U is non-empty we get that U' intersected s is non-empty
 assume _ :∃ x, x ∈ univ ∩ U,
 have h₄ : ∃ y, y ∈ s ∩ U',
   by rw [←(subtype_val_univ_eq s), ←mem_image_inter_iff, ←‹U = lift ⁻¹' U'›]; assumption,
 -- Assuming that V is non-empty we get that V' intersected s is non-empty
 assume _ : ∃ x, x ∈ univ ∩ V,
 have h₅ : ∃ y, y ∈ s ∩ V',
   by rw [←(subtype_val_univ_eq s), ←mem_image_inter_iff, ←‹V = lift ⁻¹' V'›]; assumption,
 -- We can now deduce that there is an element in s ∩ (U' ∩ V')
 -- which in turn gives an element of univ ∩ (U ∩ V)
 have ∃ y, y ∈ s ∩ (U' ∩ V'), from ‹is_connected s› U' V' h₁ h₂ h₃ h₄ h₅,
 show ∃ x, x ∈ univ ∩ (U ∩ V),
   by rw [‹U = lift ⁻¹' U'›, ‹V = lift ⁻¹' V'›, ←preimage_inter,
          mem_image_inter_iff, subtype_val_univ_eq]; assumption⟩

lemma connected_subspace_iff : connected_space s ↔ is_connected s :=
let lift := @subtype.val _ s in
iff.intro
  (assume h : connected_space s,
   have is_connected (@univ s), from h.is_connected_univ,
   have is_connected (lift '' univ),
     from @image_connected _ _ _ _ (@univ s) lift continuous_subtype_val ‹is_connected (@univ s)›,
   show is_connected s, by rw ←(subtype_val_univ_eq s); assumption)
  (@connected_subset _ _ s)

section old_connected

lemma preimage_empty_of_empty {f : α → β} {r : set β} (hf : surjective f): f⁻¹' r = ∅ → r = ∅ :=
suffices (∀a, a ∉ f ⁻¹' r) → ∀b, b ∉ r,
  by simpa only [eq_empty_iff_forall_not_mem],
assume h b,
let ⟨a, eq⟩ := hf b in
eq ▸ h a

lemma preimage_ne_empty_of_ne_empty {f : α → β } (_ : surjective f) {s : set β} (_ : s ≠ ∅ ) : f ⁻¹' s ≠ ∅ :=
let ⟨y, _⟩ := exists_mem_of_ne_empty ‹s ≠ ∅›,
    ⟨x, _⟩ := ‹surjective f›  y in
have f x ∈ s, from (eq.symm ‹f x = y›) ▸ ‹y ∈ s›,
show f⁻¹' s ≠ ∅, from ne_empty_of_mem ‹x ∈ f⁻¹' s›


-- Separations of a topological space: write α as the disjoint union of non empty, open subsets
def separation (s₁ s₂ : set α) : Prop :=
is_open s₁ ∧ is_open s₂ ∧ s₁ ≠ ∅ ∧ s₂ ≠ ∅ ∧ s₁ ∩ s₂ = ∅ ∧ s₁ ∪ s₂ = univ

-- Separations are symmetric: if s₁ s₂ is a separation of α, then so is s₂ s₁.
lemma sep_symm  (h : separation s₁ s₂) : separation s₂ s₁ :=
let ⟨ho1, ho2, hne1, hne2, hce, huu⟩ := h in ⟨ho2, ho1, hne2, hne1, (inter_comm s₁ s₂) ▸ hce, (union_comm s₁ s₂) ▸ huu⟩

lemma sep_neg (sep : separation s₁ s₂) : s₁ = -s₂ :=
let ⟨_, _, _, _, _, _⟩ := sep in
have s₁ ⊆ -s₂, by rw [subset_compl_iff_disjoint]; assumption,
have -s₂ ⊆ s₁, by rw [compl_subset_iff_union, union_comm]; assumption,
antisymm ‹s₁ ⊆ -s₂› ‹-s₂ ⊆ s₁›

lemma sep_sets_closed (h : separation s₁ s₂) : is_closed s₁ ∧ is_closed s₂ :=
let ⟨ho1, ho2, _, _, hce, huu⟩ := h in
have he1 : -s₂ = s₁, from eq.symm (sep_neg h),
have he2 : -s₁ = s₂, from eq.symm (sep_neg (sep_symm h)),
⟨he1 ▸ is_closed_compl_iff.mpr ho2, he2 ▸ is_closed_compl_iff.mpr ho1⟩


--Connected topological spaces
--class connected_space (α) [topological_space α] : Prop :=
--(connected : ¬∃ s₁ s₂ : set α, separation s₁ s₂)

theorem is_connected_image {f : α → β} [connected_space α] (_ : continuous f) : is_connected (f '' univ) :=
assume u v hu hv hcsuv ⟨y, hycs, hyu⟩ ⟨z, hzcs, hzv⟩,
sorry


/-- The image of a connected space under a surjective map is connected. -/
/-theorem im_connected {f : α → β} [connected_space α]
  (_ : continuous f) (_ : surjective f) : connected_space β :=
connected_space.mk $
-- a space is connected if there exists no separation, so we assume there is one and derive false
-- we do this by constructing a 'preimage separation'
assume _ : ∃ r₁ r₂ : set β, separation r₁ r₂,
  -- supose we have a separation r₁ ∪ r₂ = β
  let ⟨r₁, r₂, _, _, _, _, _, _⟩ := ‹∃ r₁ r₂ : set β, separation r₁ r₂› in
  -- we claim that then (s₁=f⁻¹r₁) ∪ (s₂=f⁻¹r₂) is a separation of α
  let s₁ := f⁻¹' r₁, s₂ := f⁻¹' r₂ in
  -- we now need to show that s_i are open, disjoint, nonempty, and span α
  have is_open s₁, from ‹continuous f› r₁ ‹is_open r₁›,
  have is_open s₂, from ‹continuous f› r₂ ‹is_open r₂›,
  have s₁ ≠ ∅, from preimage_ne_empty_of_ne_empty ‹surjective f› ‹r₁ ≠ ∅›,
  have s₂ ≠ ∅, from preimage_ne_empty_of_ne_empty ‹surjective f› ‹r₂ ≠ ∅›,
  have s₁ ∩ s₂ = ∅, by rw ←(@preimage_empty α β f); rw ←‹r₁ ∩ r₂ = ∅›; simp,
  have s₁ ∪ s₂ = univ, by rw ←(@preimage_univ α β f); rw ←‹r₁ ∪ r₂ = univ›; simp,
  -- with this preparation at hand, we construct a separation
  have separation s₁ s₂, from ⟨‹is_open s₁›, ‹is_open s₂›, ‹s₁ ≠ ∅›, ‹s₂ ≠ ∅›, ‹s₁ ∩ s₂ = ∅›, ‹s₁ ∪ s₂ = univ›⟩,
  -- which contradicts the fact that α is connected
  show false, from connected_space'.connected α
    ⟨s₁, s₂, ‹separation s₁ s₂›⟩

--Separations of a subset of a topological space
def subset_separation [topological_space α] (s s₁ s₂ : set α) : Prop :=
is_open s₁ ∧ is_open s₂ ∧ s₁ ∩ s ≠ ∅ ∧ s₂ ∩ s ≠ ∅ ∧ s₁ ∩ s₂ ∩ s = ∅ ∧ s ⊆ s₁ ∪ s₂

lemma subset_sep_symm {t : topological_space α} {s s₁ s₂ : set α} (h : subset_separation s s₁ s₂) : subset_separation s s₂ s₁ :=
let ⟨ho1, ho2, hne1, hne2, hce, huu⟩ := h in
⟨ho2, ho1, hne2, hne1, (inter_comm s₁ s₂) ▸ hce, (union_comm s₁ s₂) ▸ huu⟩

lemma sep_of_subset_sep {s s₁ s₂ : set α} :
  subset_separation s s₁ s₂ → @separation s _ (subtype.val⁻¹' s₁) (subtype.val⁻¹' s₂) := 
let lift := @subtype.val _ s in
assume h : subset_separation s s₁ s₂,
let ⟨_, _, _, _, _, _⟩ := h in
let s₁' := lift ⁻¹' s₁ in
let s₂' := lift ⁻¹' s₂ in
have is_open s₁', from ⟨s₁, ‹is_open s₁›, eq.refl s₁'⟩,
have is_open s₂', from ⟨s₂, ‹is_open s₂›, eq.refl s₂'⟩,
have s₁' ≠ ∅, by rw [preimage_subtype_val_ne_empty_iff, inter_comm]; assumption,
have s₂' ≠ ∅, by rw [preimage_subtype_val_ne_empty_iff, inter_comm]; assumption,
have s₁' ∩ s₂' = ∅, by rw [←preimage_inter, preimage_subtype_val_empty_iff, inter_comm]; assumption,
have s₁' ∪ s₂' = univ, from
  (have s₁' ∪ s₂' ⊆ univ, from subset_univ (s₁' ∪ s₂'),
   have univ ⊆ s₁' ∪ s₂', from
     calc
      univ = lift ⁻¹' s : by rw preimage_subtype_val_eq_univ
       ... ⊆ lift ⁻¹' (s₁ ∪ s₂) : preimage_mono ‹s ⊆ s₁ ∪ s₂›
       ... = (lift ⁻¹' s₁) ∪ (lift ⁻¹' s₂) : by rw preimage_union
       ... = s₁' ∪ s₂' : rfl,
   show s₁' ∪ s₂' = univ, from eq_of_subset_of_subset ‹s₁' ∪ s₂' ⊆ univ› ‹univ ⊆ s₁' ∪ s₂'›
  ),
show separation s₁' s₂',
   from ⟨‹is_open s₁'›, ‹is_open s₂'›, ‹s₁' ≠ ∅›, ‹s₂' ≠ ∅›, ‹s₁' ∩ s₂' = ∅›, ‹s₁' ∪ s₂' = univ›⟩

lemma exists_subset_sep_of_sep {s : set α} {s₁ s₂ : set s} :
  separation s₁ s₂ → ∃ s₁' s₂' : set α, subset_separation s s₁' s₂' :=
let lift := @subtype.val _ s in
assume h : separation s₁ s₂,
let ⟨_, _, _, _, _, _⟩ := h in
have ∃ s₁' : set α, is_open s₁' ∧ s₁ = (lift) ⁻¹' s₁', from ‹is_open s₁›,
let ⟨s₁', _, _⟩ := this in
have ∃ s₂' : set α, is_open s₂' ∧ s₂ = (lift) ⁻¹' s₂', from ‹is_open s₂›,
let ⟨s₂', _, _⟩ := this in
have s₁' ∩ s ≠ ∅,
  by rw [←inter_comm, ←preimage_subtype_val_ne_empty_iff, ←‹s₁ = lift ⁻¹' s₁'›]; assumption,
have s₂' ∩ s ≠ ∅,
  by rw [←inter_comm, ←preimage_subtype_val_ne_empty_iff, ←‹s₂ = lift ⁻¹' s₂'›]; assumption,
have s₁' ∩ s₂' ∩ s = ∅,
  by rw [←inter_comm, ←preimage_subtype_val_empty_iff, preimage_inter, ←‹s₁ = lift ⁻¹' s₁'›, ←‹s₂ = lift ⁻¹' s₂'›]; assumption,
have s ⊆ s₁' ∪ s₂', from
  (calc
       s = lift '' (univ) : by rw (subtype_val_univ_eq s)
     ... = lift '' (s₁ ∪ s₂) : by rw ‹s₁ ∪ s₂ = univ›
     ... = lift '' s₁ ∪ lift '' s₂ : by rw image_union
     ... = (lift '' (lift ⁻¹' s₁')) ∪ (lift '' (lift ⁻¹' s₂')) : by rw [‹s₁ = lift ⁻¹' s₁'›, ‹s₂ = lift ⁻¹' s₂'›]
     ... ⊆ s₁' ∪ s₂' : union_subset_union (image_preimage_subset lift s₁') (image_preimage_subset lift s₂')
  ),
show ∃s₁' s₂' : set α, subset_separation s s₁' s₂',
  from ⟨s₁', s₂', ‹is_open s₁'›, ‹is_open s₂'›, ‹s₁' ∩ s ≠ ∅›, ‹s₂' ∩ s ≠ ∅›, ‹s₁' ∩ s₂' ∩ s = ∅›, ‹s ⊆ s₁' ∪ s₂'›⟩

--Connected subsets of a topological space
def disconnected_subset (s : set α) : Prop :=
∃s₁ s₂ : set α, subset_separation s s₁ s₂

def connected_subset' (s : set α) : Prop :=
¬(disconnected_subset s)

lemma connected_space_iff : connected_space' α ↔ ¬∃ s₁ s₂ : set α, separation s₁ s₂ :=
begin
  constructor,
  apply connected_space'.connected,
  apply connected_space'.mk
end

theorem subtype_connected_iff_subset_connected {s : set α} : connected_space' s ↔ connected_subset' s :=
suffices h₀ : (∃ s₁ s₂ : set s, separation s₁ s₂) ↔ disconnected_subset s,
  by rw connected_space_iff; apply not_iff_not_of_iff; assumption,
let lift := @subtype.val α s in
iff.intro
  (assume h : ∃ s₁ s₂ : set s, separation s₁ s₂,
   let ⟨s₁, s₂, h₁⟩ := h in
   show ∃ s₁' s₂' : set α, subset_separation s s₁' s₂', from exists_subset_sep_of_sep h₁
  )
  (assume h : disconnected_subset s,
   let ⟨s₁, s₂, h₁⟩ := h in
   show ∃ s₁ s₂ : set s, separation s₁ s₂,
     from ⟨lift ⁻¹' s₁, lift ⁻¹' s₂, sep_of_subset_sep h₁⟩
  )-/

end old_connected

