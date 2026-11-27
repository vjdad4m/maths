import PrivatePairs33

namespace Graffiti384b.RootCut
open Finset SimpleGraph HighEar OneEar EarAnchor CliquePivot33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- If one exterior misses the entire clique, every edge in the other
exterior must contain the whole safe set. -/
private theorem no_contact_bound {M C A B : Finset V} (mc : M⊆C) (ms : 2≤M.card)
    (an : (pairs H A).Nonempty) (bn : (pairs H B).Nonempty)
    (cover : ∀ E∈pairs H A,∀ F∈pairs H B,M⊆E∪F)
    (none : ¬∃ z∈B,z∈C) : M.card=2 ∧ (pairs H A).card≤1 := by
  obtain ⟨F,fm⟩ := bn
  have contain {E : Finset V} (em : E∈pairs H A) : M⊆E := by
    intro x xm
    exact (mem_union.mp (cover E em F fm xm)).resolve_right (fun h =>
      none ⟨x,(mem_powersetCard.mp (mem_filter.mp fm).1).1 h,mc xm⟩)
  have size {E : Finset V} (em : E∈pairs H A) : E.card=2 :=
    (mem_powersetCard.mp (mem_filter.mp em).1).2
  obtain ⟨E,em⟩ := an
  have m2 := (card_le_card (contain em)).trans (size em).le
  refine ⟨Nat.le_antisymm m2 ms,?_⟩
  have sub : pairs H A⊆{M} := by
    intro K km
    exact mem_singleton.mpr (eq_of_subset_of_card_le (contain km) ((size km).le.trans ms)).symm
  simpa using card_le_card sub

/-- A safe palette has exactly two vertices. Either both are the ear
endpoints' respective clique contacts, or one endpoint has just two triangles. -/
theorem palette {e a c : V} (de : H.degree e=2) (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (thin : additional H e a c=∅) (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    {R C M : Finset V} (tight : Tight H R) (cl : H.IsNClique 5 C) (apart : ¬(a∈C ∧ c∈C))
    (mc : M⊆C) (safe : ∀ x∈M,Safe H R x) (ms : 2≤M.card) :
    a∉C ∧ c∉C ∧ M.card=2 ∧
    (trianglesAt H a=2 ∨ trianglesAt H c=2 ∨ ∃ p∈M,∃ q∈M,p≠q ∧ H.Adj a p ∧ H.Adj c q) := by
  classical
  have flip : additional H e c a=∅ := by simpa only [additional,inter_comm] using thin
  have an := off_clique H de ea ec ac thin pos inj tight cl apart mc safe ms
  have cn := off_clique H de ec ea ac.symm flip pos inj tight cl (fun h => apart ⟨h.2,h.1⟩) mc safe ms
  refine ⟨an,cn,?_⟩
  let A := exterior H e a c
  let B := exterior H e c a
  have aedge := has_edge H de ea ec ac thin pos inj
  have bedge := has_edge H de ec ea ac.symm flip pos inj
  have cov : ∀ E∈pairs H A,∀ F∈pairs H B,M⊆E∪F := by
    intro E em F fm x xm
    exact edge_cover H de ea ec ac pos inj tight cl apart (mc xm) (safe x xm)
      (fun eq => an (eq ▸ mc xm)) (fun eq => cn (eq ▸ mc xm)) em fm
  by_cases bc : ∃ q∈B,q∈C
  · by_cases ax : ∃ p∈A,p∈C
    · obtain ⟨p,pa,pc⟩ := ax
      obtain ⟨q,qb,qc⟩ := bc
      have ap := (H.mem_neighborFinset _ _).mp (mem_sdiff.mp pa).1
      have cq := (H.mem_neighborFinset _ _).mp (mem_sdiff.mp qb).1
      have pq : p≠q := by
        rintro rfl
        have pe : p≠e := fun eq => (mem_sdiff.mp pa).2 (eq ▸ mem_insert_self ..)
        have m := (additional_mem H).mpr ⟨pe,ap,cq⟩
        rw [thin] at m; exact not_mem_empty _ m
      have sub : M⊆{p,q} := fun x xm =>
        contact_cover H de ea ec ac pos inj tight cl an cn pc qc pq ap cq (mc xm) (safe x xm)
      have equal := eq_of_subset_of_card_le sub (by simpa [pq] using ms)
      have pp : p∈M := equal ▸ mem_insert_self ..
      have qq : q∈M := equal ▸ mem_insert_of_mem (mem_singleton_self _)
      exact ⟨by rw [equal,card_pair pq],Or.inr (Or.inr ⟨p,pp,q,qq,pq,ap,cq⟩)⟩
    · have ⟨sz,le⟩ := no_contact_bound H mc ms bedge aedge
        (fun F fm E em => by simpa only [union_comm] using cov E em F fm) ax
      have val := exterior_count H de ec ea ac.symm flip
      have po := card_pos.mpr bedge
      exact ⟨sz,Or.inr (Or.inl (by omega))⟩
  · have ⟨sz,le⟩ := no_contact_bound H mc ms aedge bedge cov bc
    have val := exterior_count H de ea ec ac thin
    have po := card_pos.mpr aedge
    exact ⟨sz,Or.inl (by omega)⟩

end Graffiti384b.RootCut
#print axioms Graffiti384b.RootCut.palette
