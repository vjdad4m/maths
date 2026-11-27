import RoutedFourRingCubic

open Finset SimpleGraph
namespace KelmansCactus.FourRingReplica.Layout
open FourRingBudget FourRingCutAux FourRingCutChoices
noncomputable section
variable {U J : Type*} [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J]
variable {A : SimpleGraph U} {r : Bool→U}
variable (L : Layout A r) (next : Equiv.Perm J) (rev : J→Bool) (fixed : ∀i,next i≠i)
variable (c : Host J r→Bool)

def routedActiveSeams : Finset (J×Bool) :=
  univ.filter (fun s=>c (L.routedStart rev s)≠c (L.routedEnd next rev s))

omit [Fintype U] [DecidableEq U] [DecidableEq J] in
theorem routedMemActive {s : J×Bool} :
    s∈L.routedActiveSeams next rev c ↔ c (L.routedStart rev s)≠c (L.routedEnd next rev s) := by
  simp [routedActiveSeams]

omit [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J] in
theorem routedStart_ne_end (s t : J×Bool) : L.routedStart rev s≠L.routedEnd next rev t := by
  rintro h
  obtain ⟨i,k⟩ := s
  obtain ⟨j,l⟩ := t
  have e : (i,swapSlot (rev i) (true,k))=(next j,swapSlot (rev (next j)) (false,l)) :=
    L.port_inj_on_host h
  have iEq := congrArg Prod.fst e
  have sides := congrArg Prod.snd e
  change swapSlot (rev i) (true,k)=swapSlot (rev (next j)) (false,l) at sides
  change i=next j at iEq
  rw [←iEq] at sides
  exact Bool.false_ne_true (congrArg Prod.fst (swapSlot_inj _ sides)).symm

def routedRepresentedSeam (s : J×Bool) : Host J r×Host J r :=
  orientation c (L.routedStart rev s) (L.routedEnd next rev s)

omit [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J] in
private theorem represented_injective :
    Function.Injective (L.routedRepresentedSeam next rev c) := by
  intro i j same
  have e : L.routedStart rev i=L.routedStart rev j := by
    rcases orientation_cases (x:=L.routedStart rev i) (y:=L.routedEnd next rev i) (c:=c) with ai|ai <;>
      rcases orientation_cases (x:=L.routedStart rev j) (y:=L.routedEnd next rev j) (c:=c) with aj|aj
    · exact congrArg Prod.fst (ai.symm.trans (same.trans aj))
    · exact (L.routedStart_ne_end next rev i j (congrArg Prod.fst (ai.symm.trans (same.trans aj)))).elim
    · exact (L.routedStart_ne_end next rev i j (congrArg Prod.snd (ai.symm.trans (same.trans aj)))).elim
    · exact congrArg Prod.snd (ai.symm.trans (same.trans aj))
  have q : (i.1,swapSlot (rev i.1) (true,i.2))=(j.1,swapSlot (rev j.1) (true,j.2)) :=
    L.port_inj_on_host e
  exact Prod.ext (congrArg (fun x : J×Slot=>x.1) q) (congrArg (fun x : J×Slot=>x.2.2) q)

private def cellPairEmbed (i : J) : (Piece r×Piece r)↪(Host J r×Host J r) :=
  ⟨fun x=>((i,x.1),(i,x.2)),fun _ _ e=>Prod.ext
    (congrArg (fun v : Host J r×Host J r=>v.1.2) e)
    (congrArg (fun v : Host J r×Host J r=>v.2.2) e)⟩

private def mappedInside (i : J) : Finset (Host J r×Host J r) :=
  (boundary (minor A r) (cellColour c i)).map (cellPairEmbed i)

omit [Fintype J] [DecidableEq J] in
private theorem mappedIndex {i : J} {e : Host J r×Host J r} (m : e∈mappedInside (A:=A) c i) :
    e.1.1=i ∧ e.2.1=i := by
  obtain ⟨z,_,rfl⟩ := mem_map.mp m
  exact ⟨rfl,rfl⟩

omit [DecidableEq J] in
private theorem mappedInside_mem (i : J) :
    mappedInside (A:=A) c i⊆boundary (L.routedGraph next rev fixed) c := by
  intro z hz
  obtain ⟨e,em,rfl⟩ := mem_map.mp hz
  obtain ⟨xf,yt,a⟩ := mem_boundary.mp em
  exact mem_boundary.mpr ⟨xf,yt,Or.inl ⟨rfl,a⟩⟩

private theorem activeIncluded :
    (L.routedActiveSeams next rev c).image (L.routedRepresentedSeam next rev c)⊆boundary (L.routedGraph next rev fixed) c := by
  intro e m
  obtain ⟨s,sm,rfl⟩ := mem_image.mp m
  have adj : (L.routedGraph next rev fixed).Adj (L.routedStart rev s) (L.routedEnd next rev s) :=
    L.routedSeam_edge next rev s.1 s.2
  exact active_edge ((L.routedMemActive next rev c).mp sm) adj

/-- The host cut contains disjoint contributions from all internal
cuts and all active paired seams. Cardinalities may be added. -/
theorem routedHostCutLower :
    (∑ i : J, insideCount (A:=A) c i)+(L.routedActiveSeams next rev c).card ≤
      (boundary (L.routedGraph next rev fixed) c).card := by
  classical
  let I := univ.biUnion (mappedInside (A:=A) c)
  let E := (L.routedActiveSeams next rev c).image (L.routedRepresentedSeam next rev c)
  have sep : Disjoint I E := by
    apply disjoint_left.mpr
    intro e hi he
    obtain ⟨i,_,inz⟩ := mem_biUnion.mp hi
    have coord := mappedIndex c inz
    obtain ⟨s,_,rfl⟩ := mem_image.mp he
    rcases orientation_cases (x:=L.routedStart rev s) (y:=L.routedEnd next rev s) (c:=c) with x|x
    · change L.routedRepresentedSeam next rev c s = _ at x
      rw [x] at coord
      exact fixed s.1 (coord.2.trans coord.1.symm)
    · change L.routedRepresentedSeam next rev c s = _ at x
      rw [x] at coord
      exact fixed s.1 (coord.1.trans coord.2.symm)
  have sub : I∪E⊆boundary (L.routedGraph next rev fixed) c := by
    intro v m
    rcases mem_union.mp m with ii|ee
    · obtain ⟨i,_,mi⟩ := mem_biUnion.mp ii
      exact L.mappedInside_mem next rev fixed c i mi
    · exact L.activeIncluded next rev fixed c ee
  have disj : (↑(univ : Finset J) : Set J).PairwiseDisjoint (mappedInside (A:=A) c) := by
    intro i _ j _ ne
    exact disjoint_left.mpr (fun x hi hj=>ne ((mappedIndex c hi).1.symm.trans (mappedIndex c hj).1))
  have bound := card_le_card sub
  rw [card_union_of_disjoint sep] at bound
  have ci : I.card=∑ i:J,insideCount (A:=A) c i := by
    change (univ.biUnion (mappedInside (A:=A) c)).card=_
    rw [card_biUnion disj]
    exact sum_congr rfl (fun i _=>card_map _)
  have ce : E.card=(L.routedActiveSeams next rev c).card :=
    card_image_of_injective _ (L.represented_injective next rev c)
  rwa [ci,ce] at bound

#print axioms routedHostCutLower
end
end KelmansCactus.FourRingReplica.Layout
