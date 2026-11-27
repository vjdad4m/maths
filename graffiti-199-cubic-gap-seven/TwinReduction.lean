import CoreTransfer
import OmissionSplice

open private traceable_of_omission_permutation from OmissionSplice

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Adjacent vertices with the same neighbors at every third vertex. -/
structure AdjacentTwins (G : SimpleGraph V) (x y : V) : Prop where
  edge : G.Adj x y
  same : ∀ w, w ≠ x → w ≠ y → (G.Adj x w ↔ G.Adj y w)

theorem AdjacentTwins.symm {x y : V} (tw : AdjacentTwins G x y) :
    AdjacentTwins G y x :=
  ⟨tw.edge.symm,fun w hy hx => (tw.same w hx hy).symm⟩

theorem PathOn.induce_restrict {S T : Set V} (p : PathOn G S) (sub : S ⊆ T) :
    ∃ q : PathOn (G.induce T) {x : T | x.val ∈ S}, q.vertices.map Subtype.val = p.vertices := by
  have h (v : V) (hv : v ∈ p.vertices) : v ∈ T := sub ((p.covers _).mp hv)
  let l : List T := p.vertices.attachWith (· ∈ T) h
  have mapped : l.map Subtype.val = p.vertices := List.attachWith_map_subtype_val h
  refine ⟨⟨l,?_,?_,?_,?_⟩,mapped⟩
  · intro e
    exact p.nonempty (by simpa only [e,List.map_nil] using mapped.symm)
  · exact (List.chain'_map Subtype.val).mp (mapped.symm ▸ p.chain)
  · exact List.Nodup.of_map Subtype.val (mapped.symm ▸ p.nodup)
  · intro x
    constructor
    · intro h
      exact (p.covers _).mp (mapped ▸ List.mem_map.mpr ⟨x,h,rfl⟩)
    · intro h
      have hm : x.val ∈ l.map Subtype.val := mapped.symm ▸ (p.covers _).mpr h
      obtain ⟨y,hy,eq⟩ := List.mem_map.mp hm
      exact (Subtype.ext eq) ▸ hy

/-- Removing the first of two consecutive twins from a simple path
preserves its order on the remaining vertices. -/
theorem PathOn.delete_before_twin {S : Set V} {u v : V} (p : PathOn G S)
    (tw : AdjacentTwins G u v) {L R : List V} (split : p.vertices = L ++ u :: v :: R) :
    ∃ q : PathOn G {x | x ∈ S ∧ x ≠ u}, q.vertices = L ++ v :: R := by
  have old : (L ++ u :: v :: R).Chain' G.Adj := split ▸ p.chain
  have nd : (L ++ u :: v :: R).Nodup := split ▸ p.nodup
  obtain ⟨lnd,rnd,disj⟩ := List.nodup_append.mp nd
  have off : u ∉ L ++ v :: R := by
    intro h
    rcases List.mem_append.mp h with hl|hr
    · exact disj hl (List.mem_cons_self)
    · exact (List.nodup_cons.mp rnd).1 hr
  refine ⟨⟨_,by simp,?_,?_,?_⟩,rfl⟩
  · apply old.left_of_append.append old.right_of_append.tail
    intro x hx y hy
    have eq : v = y := by simpa using hy
    have xl := List.mem_of_getLast? (Option.mem_def.mp hx)
    have xu : x ≠ u := fun e => off (List.mem_append_left _ (e ▸ xl))
    have xv : x ≠ v := fun e => disj (e ▸ xl) (by simp)
    have xuE := (List.chain'_append.mp old).2.2 x hx u rfl
    exact eq ▸ ((tw.same _ xu xv).mp xuE.symm).symm
  · exact List.nodup_append.mpr ⟨lnd,(List.nodup_cons.mp rnd).2,
      fun x hx hy => disj hx (List.mem_cons_of_mem _ hy)⟩
  · intro x
    constructor
    · intro hx
      refine ⟨(p.covers _).mp ?_,fun e => off (e ▸ hx)⟩
      rw [split]
      rcases List.mem_append.mp hx with hx|hx
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)
    · rintro ⟨xs,xu⟩
      have hm := (p.covers _).mpr xs
      rw [split] at hm
      exact List.mem_append.mpr ((List.mem_append.mp hm).imp id
        (fun h => (List.mem_cons.mp h).resolve_left xu))

/-- Reinserting an adjacent twin preserves the existence of a spanning path. -/
theorem AdjacentTwins.traceable_of_delete [DecidableEq V] {u v : V}
    (tw : AdjacentTwins G u v)
    (h : Catalogue.Traceable (G.induce {x | x ≠ u})) : Catalogue.Traceable G := by
  obtain ⟨q⟩ := pathOn_univ_iff_hamiltonian_walk.mpr
    (Catalogue.traceable_iff_hamiltonian_walk.mp h)
  let l := q.vertices.map Subtype.val
  have chain : l.Chain' G.Adj := (List.chain'_map _).mpr q.chain
  have nodup : l.Nodup := q.nodup.map Subtype.val_injective
  have cov (x : V) : x ∈ l ↔ x ≠ u := by
    constructor
    · intro hx
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
      exact y.property
    · intro hx
      exact List.mem_map.mpr ⟨⟨x,hx⟩,(q.covers _).mpr (Set.mem_univ _),rfl⟩
  let p : PathOn G {x | x ≠ u} :=
    ⟨l,fun e => q.nonempty (List.map_eq_nil_iff.mp e),chain,nodup,cov⟩
  obtain ⟨L,R,split⟩ := List.append_of_mem ((cov v).mpr tw.edge.ne.symm)
  have ch : (L ++ v :: R).Chain' G.Adj := split ▸ chain
  have nd : (L ++ v :: R).Nodup := split ▸ nodup
  have tail : (v :: u :: R).Chain' G.Adj := by
    apply List.Chain'.cons
    · exact tw.edge.symm
    · apply ch.right_of_append.tail.cons'
      intro w hw
      have wu : w ≠ u := (cov _).mp (split.symm ▸ List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_of_mem_head? hw)))
      have wv : w ≠ v := fun eq => (List.nodup_cons.mp (List.nodup_append.mp nd).2.1).1
        (eq ▸ List.mem_of_mem_head? hw)
      exact (tw.same _ wu wv).mpr (ch.right_of_append.rel_head? hw)
  have all : (L ++ v :: u :: R).Chain' G.Adj := by
    apply ch.left_of_append.append tail
    intro x hx y hy
    have eq : v = y := by simpa using hy
    exact eq ▸ (List.chain'_append.mp ch).2.2 x hx v rfl
  have perm : (L ++ v :: u :: R).Perm (u :: p.vertices) := by
    change (L ++ v :: u :: R).Perm (u :: l)
    rw [split]
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using
      (List.perm_middle (a := u) (l₁ := L ++ [v]) (l₂ := R))
  exact traceable_of_omission_permutation p perm all

#print axioms AdjacentTwins.traceable_of_delete
#print axioms PathOn.delete_before_twin

end Graffiti199Depleted
