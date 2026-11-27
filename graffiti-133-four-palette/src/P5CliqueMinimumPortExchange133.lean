import CambyDomBase133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Two middle ports cannot be replaced by one exterior vertex that covers
all their previous one-port clients and attaches to the surviving core. -/
theorem minimum_core_forbids_two_port_single_vertex_exchange
    (D E : Finset V) (dm : MinimalSize G D) (sub : E⊆D)
    (ec : (G.induce (E : Set V)).Connected)
    (ed : ∀ v∈D,v∈E ∨ ∃ e∈E,G.Adj v e)
    (tag : V→V) (route : ∀ v∉D,tag v∈D ∧ G.Adj v (tag v))
    (p r x : V) (pd : p∈D) (rd : r∈D) (pE : p∉E) (rE : r∉E) (pr : p≠r)
    (xD : x∉D) (xp : tag x≠p) (xr : tag x≠r)
    (coverage : ∀ v∉D,tag v=p ∨ tag v=r→G.Adj x v) : False := by
  let S := (D.erase p).erase r
  let T := insert x S
  have sD : S⊆D := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have xm : x∉S := fun m=>xD (sD m)
  have eSub : E⊆S := by
    intro e em
    exact Finset.mem_erase.mpr ⟨fun q=>rE (q ▸ em),
      Finset.mem_erase.mpr ⟨fun q=>pE (q ▸ em),sub em⟩⟩
  have tS : S⊆T := Finset.subset_insert _ _
  have xe : tag x∈S := Finset.mem_erase.mpr ⟨xr,Finset.mem_erase.mpr ⟨xp,(route x xD).1⟩⟩
  let f : G.induce (E : Set V) →g G.induce (T : Set V) :=
    ⟨fun e=>⟨e.val,tS (eSub e.property)⟩,fun h=>h⟩
  obtain ⟨a⟩ := ec.nonempty
  have old (v : V) (vm : v∈S) : (G.induce (T : Set V)).Reachable (f a) ⟨v,tS vm⟩ := by
    rcases ed v (sD vm) with ve|⟨e,ee,ev⟩
    · exact (ec a ⟨v,ve⟩).map f
    · exact ((ec a ⟨e,ee⟩).map f).trans
        (show (G.induce (T : Set V)).Adj (f ⟨e,ee⟩) ⟨v,tS vm⟩ from ev.symm).reachable
  have tc : (G.induce (T : Set V)).Connected := by
    rw [connected_iff_exists_forall_reachable]
    refine ⟨f a,fun v=>?_⟩
    rcases Finset.mem_insert.mp v.property with vx|vm
    · have ev : G.Adj (tag x) v.val := by rw [vx]; exact (route x xD).2.symm
      exact (old (tag x) xe).trans
        (show (G.induce (T : Set V)).Adj ⟨tag x,tS xe⟩ v from ev).reachable
    · exact old v.val vm
  have td : CD G T := by
    refine ⟨tc,fun v=>?_⟩
    by_cases vd : v∈D
    · rcases ed v vd with e|⟨u,um,vu⟩
      · exact Or.inl (tS (eSub e))
      · exact Or.inr ⟨u,tS (eSub um),vu⟩
    by_cases tagP : tag v=p ∨ tag v=r
    · exact Or.inr ⟨x,Finset.mem_insert_self _ _,(coverage v vd tagP).symm⟩
    push_neg at tagP
    have mem : tag v∈S := Finset.mem_erase.mpr ⟨tagP.2,Finset.mem_erase.mpr ⟨tagP.1,(route v vd).1⟩⟩
    exact Or.inr ⟨tag v,tS mem,(route v vd).2⟩
  have lower := dm.2 T td
  have pEq := Finset.card_erase_add_one pd
  have rEq : S.card+1=(D.erase p).card :=
    Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨pr.symm,rd⟩)
  have tEq : T.card=S.card+1 := Finset.card_insert_of_not_mem xm
  omega

#print axioms minimum_core_forbids_two_port_single_vertex_exchange

/-- In the genuine minimum-CDS setting, a one-port outer vertex cannot see
two distinct singleton middle-port fibers. -/
theorem minimum_core_at_most_one_visible_singleton_middle_port
    (D E : Finset V) (dm : MinimalSize G D) (sub : E⊆D)
    (ec : (G.induce (E : Set V)).Connected)
    (ed : ∀ v∈D,v∈E ∨ ∃ e∈E,G.Adj v e)
    (tag : V→V) (route : ∀ v∉D,tag v∈D ∧ G.Adj v (tag v))
    (x q r : V) (xo : x∉D) (qo : q∉D) (ro : r∉D)
    (qE : tag q∉E) (rE : tag r∉E)
    (xq : G.Adj x q) (xr : G.Adj x r)
    (uniqQ : ∀ v∉D,tag v=tag q→v=q)
    (uniqR : ∀ v∉D,tag v=tag r→v=r) :
    tag q=tag r := by
  by_contra ne
  have nxq : tag x≠tag q := fun e=>xq.ne (uniqQ x xo e)
  have nxr : tag x≠tag r := fun e=>xr.ne (uniqR x xo e)
  apply minimum_core_forbids_two_port_single_vertex_exchange D E dm sub ec ed tag route
    (tag q) (tag r) x (route q qo).1 (route r ro).1 qE rE ne xo nxq nxr
  intro v vo h
  rcases h with e|e
  · exact (uniqQ v vo e).symm ▸ xq
  · exact (uniqR v vo e).symm ▸ xr

#print axioms minimum_core_at_most_one_visible_singleton_middle_port
end Graffiti133P5CliqueArms
