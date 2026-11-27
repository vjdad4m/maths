import CubicDeletion

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Distinct internal vertices of a simple path require strictly more
distinct neighboring vertices if all of their flanks are drawn from one set. -/
theorem card_lt_of_path_flanks {L : List V} {U T : Finset V}
    (nd : L.Nodup) (all : ∀ v ∈ U, v ∈ L) (nonempty : U.Nonempty)
    (before : ∀ i : Fin L.length, L.get i ∈ U →
      ∃ j : Fin L.length, j.val + 1 = i.val ∧ L.get j ∈ T)
    (after : ∀ i : Fin L.length, L.get i ∈ U →
      ∃ j : Fin L.length, i.val + 1 = j.val ∧ L.get j ∈ T) : U.card < T.card := by
  classical
  let getEmb : Fin L.length ↪ V := ⟨L.get,List.nodup_iff_injective_get.mp nd⟩
  let I := Finset.univ.filter (fun i => L.get i ∈ U)
  have memI (i : Fin L.length) : i ∈ I ↔ L.get i ∈ U := by simp [I]
  have mapI : I.map getEmb = U := by
    ext x
    constructor
    · rintro hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
      exact (memI i).mp hi
    · intro hx
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp (all _ hx)
      exact Finset.mem_map.mpr ⟨i,(memI i).mpr hx,rfl⟩
  have size : I.card = U.card := by rw [← mapI,Finset.card_map]
  have iNonempty : I.Nonempty := Finset.card_pos.mp (size ▸ Finset.card_pos.mpr nonempty)
  let m := I.max' iNonempty
  have hm := (memI m).mp (I.max'_mem iNonempty)
  obtain ⟨last,hlast,hT⟩ := after m hm
  choose prev hprev hprevT using before
  let f : ↥I → ↥T := fun i => ⟨L.get (prev i ((memI i).mp i.property)),hprevT _ _⟩
  have inj : Function.Injective f := by
    intro a b eq
    have e : prev a ((memI a).mp a.property) = prev b ((memI b).mp b.property) :=
      getEmb.injective (congrArg Subtype.val eq)
    apply Subtype.ext
    exact Fin.ext ((hprev a ((memI a).mp a.property)).symm.trans
      ((congrArg (fun i : Fin L.length => i.val + 1) e).trans (hprev b ((memI b).mp b.property))))
  have notOnto : ¬ Function.Surjective f := by
    intro onto
    obtain ⟨i,eq⟩ := onto ⟨L.get last,hT⟩
    have e : prev i ((memI i).mp i.property) = last :=
      getEmb.injective (congrArg Subtype.val eq)
    have hi := hprev i ((memI i).mp i.property)
    rw [e] at hi
    have le : i.val.val ≤ m.val := I.le_max' i.val i.property
    omega
  have strict := Fintype.card_lt_of_injective_not_surjective f inj notOnto
  simpa only [Fintype.card_coe,size] using strict

variable {r : V}

/-- View a Hamiltonian path of the induced deletion as an unfilled
one-omission path on the original vertex type. -/
theorem pathOn_of_traceable_delete (tr : Traceable (G.induce {x | x ≠ r})) :
    Nonempty (PathOn G {x | x ≠ r}) := by
  obtain ⟨a,b,w,hp,all⟩ := tr
  let f : {x : V // x ≠ r} ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let L := w.support.map f
  have chain : L.Chain' G.Adj := by
    apply (List.chain'_map _).mpr
    exact w.chain'_adj_support
  refine ⟨⟨L,by simp [L],chain,hp.support_nodup.map f.injective,?_⟩⟩
  intro v
  constructor
  · intro mem
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp mem
    exact x.property
  · intro off
    exact List.mem_map.mpr ⟨⟨v,off⟩,all _,rfl⟩

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Every neighbor of the omitted vertex is internal, with both flanks
outside its neighborhood, in a spanning path of a nontraceable graph's deletion. -/
theorem path_flanks_of_nontraceable (p : PathOn G {x | x ≠ r}) (no : ¬ Traceable G)
    (i : Fin p.vertices.length) (adj : G.Adj r (p.vertices.get i)) :
    (∃ j : Fin p.vertices.length, j.val + 1 = i.val ∧ G.Adj (p.vertices.get i) (p.vertices.get j) ∧
      ¬ G.Adj r (p.vertices.get j)) ∧
    (∃ j : Fin p.vertices.length, i.val + 1 = j.val ∧ G.Adj (p.vertices.get i) (p.vertices.get j) ∧
      ¬ G.Adj r (p.vertices.get j)) := by
  classical
  let fill : FilledPath G (G.neighborFinset r) r :=
    ⟨p.vertices,p.nonempty,p.nodup,p.covers,p.chain.imp (fun _ _ h => Or.inl h)⟩
  have notFirst : i.val ≠ 0 := by
    intro zero
    have edge : G.Adj r (p.vertices.head p.nonempty) := by
      rw [List.head_eq_getElem]
      have eq : (⟨0,List.length_pos_iff.mpr p.nonempty⟩ : Fin p.vertices.length) = i :=
        Fin.ext zero.symm
      change G.Adj r (p.vertices.get ⟨0,_⟩)
      rw [eq]
      exact adj
    have chain : (r :: p.vertices).Chain' G.Adj := p.chain.cons' (by
      intro x hx
      have eq : p.vertices.head p.nonempty = x :=
        (List.head_eq_iff_head?_eq_some p.nonempty).mpr hx
      exact eq ▸ edge)
    exact no (traceable_from_augmented_fill fill (List.Perm.refl _) chain)
  have notLast : i.val + 1 < p.vertices.length := by
    by_contra h
    have eq : i.val = p.vertices.length - 1 := by have hi := i.isLt; omega
    have edge : G.Adj (p.vertices.getLast p.nonempty) r := by
      rw [List.getLast_eq_getElem]
      have indEq : (⟨p.vertices.length-1,by have hi := i.isLt; omega⟩ :
        Fin p.vertices.length) = i := Fin.ext eq.symm
      change G.Adj (p.vertices.get ⟨_,_⟩) r
      rw [indEq]
      exact adj.symm
    have chain : (p.vertices ++ [r]).Chain' G.Adj := p.chain.append (by simp) (by
      intro x hx y hy
      obtain ⟨_,ex⟩ := List.mem_getLast?_eq_getLast hx
      have ey : r = y := by simpa using hy
      rw [ex,← ey]
      exact edge)
    have perm : (p.vertices ++ [r]).Perm (r :: p.vertices) := by
      simpa only [List.cons_append,List.nil_append,List.append_nil] using
        (List.perm_middle (a := r) (l₁ := p.vertices) (l₂ := []))
    exact no (traceable_from_augmented_fill fill perm chain)
  have consecutive (k : ℕ) (hk : k+1 < p.vertices.length) :
      G.Adj (p.vertices.get ⟨k,by omega⟩) (p.vertices.get ⟨k+1,hk⟩) ∧
      ¬ (G.Adj r (p.vertices.get ⟨k,by omega⟩) ∧
        G.Adj r (p.vertices.get ⟨k+1,hk⟩)) := by
    let L := p.vertices.take k
    let R := p.vertices.drop (k+2)
    let a := p.vertices.get ⟨k,by omega⟩
    let b := p.vertices.get ⟨k+1,hk⟩
    have form : p.vertices = L ++ a :: b :: R := by
      have eq := List.take_append_drop k p.vertices
      rw [List.drop_eq_getElem_cons (by omega : k < p.vertices.length),
        List.drop_eq_getElem_cons hk] at eq
      exact eq.symm
    have chain := p.chain
    rw [form] at chain
    obtain ⟨left,real,right⟩ := List.chain'_append_cons_cons.mp chain
    refine ⟨real,?_⟩
    rintro ⟨ra,rb⟩
    exact no (traceable_of_single_fill fill form ((G.mem_neighborFinset _ _).mpr ra)
      ((G.mem_neighborFinset _ _).mpr rb) left right)
  let j : Fin p.vertices.length := ⟨i.val-1,by have hi := i.isLt; omega⟩
  have ji : j.val+1 = i.val := by dsimp [j]; omega
  have before := consecutive j.val (by rw [ji]; exact i.isLt)
  have ej : (⟨j.val+1,by rw [ji]; exact i.isLt⟩ : Fin p.vertices.length) = i := Fin.ext ji
  rw [ej] at before
  let k : Fin p.vertices.length := ⟨i.val+1,notLast⟩
  have after := consecutive i.val notLast
  exact ⟨⟨j,ji,before.1.symm,fun h => before.2 ⟨h,adj⟩⟩,
    ⟨k,rfl,after.1,fun h => after.2 ⟨adj,h⟩⟩⟩

#print axioms card_lt_of_path_flanks
#print axioms pathOn_of_traceable_delete
#print axioms path_flanks_of_nontraceable

end Graffiti199Depleted.Catalogue
