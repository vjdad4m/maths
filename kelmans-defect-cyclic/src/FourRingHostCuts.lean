import FourRingCapCuts

open Finset SimpleGraph
namespace KelmansCactus.FourRingReplica.Layout
open FourRingBudget FourRingCutAux FourRingCutChoices
noncomputable section
variable {U J : Type*} [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J]
variable {A : SimpleGraph U} {r : Bool→U}
variable (L : Layout A r) (next : Equiv.Perm J) (fixed : ∀i,next i≠i)
variable (c : Host J r→Bool)

def cellColour (c : Host J r→Bool) (i : J) : Piece r→Bool := fun x=>c (i,x)

def startSeam (s : J×Bool) : Host J r := L.p s.1 (true,s.2)
def endSeam (s : J×Bool) : Host J r := L.p (next s.1) (false,s.2)

def activeSeams : Finset (J×Bool) :=
  univ.filter (fun s=>c (L.startSeam s)≠c (L.endSeam next s))

omit [Fintype U] [DecidableEq U] [DecidableEq J] in
theorem mem_active {s : J×Bool} :
    s∈L.activeSeams next c ↔ c (L.startSeam s)≠c (L.endSeam next s) := by
  simp [activeSeams]

omit [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J] in
theorem seamStart_ne_end (s t : J×Bool) : L.startSeam s≠L.endSeam next t := by
  intro eq
  have color := L.port.injective (congrArg (fun x : Host J r=>x.2) eq)
  exact Bool.false_ne_true (congrArg Prod.fst color).symm

def representedSeam (s : J×Bool) : Host J r×Host J r :=
  orientation c (L.startSeam s) (L.endSeam next s)

omit [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J] in
private theorem represented_injective :
    Function.Injective (L.representedSeam next c) := by
  intro i j same
  have e : L.startSeam i=L.startSeam j := by
    rcases orientation_cases (x:=L.startSeam i) (y:=L.endSeam next i) (c:=c) with ai|ai <;>
      rcases orientation_cases (x:=L.startSeam j) (y:=L.endSeam next j) (c:=c) with aj|aj
    · exact congrArg Prod.fst (ai.symm.trans (same.trans aj))
    · exact (L.seamStart_ne_end next i j (congrArg Prod.fst (ai.symm.trans (same.trans aj)))).elim
    · exact (L.seamStart_ne_end next i j (congrArg Prod.snd (ai.symm.trans (same.trans aj)))).elim
    · exact congrArg Prod.snd (ai.symm.trans (same.trans aj))
  have q : (i.1,(true,i.2))=(j.1,(true,j.2)) := L.port_inj_on_host e
  exact Prod.ext (congrArg (fun x : J×Slot=>x.1) q) (congrArg (fun x : J×Slot=>x.2.2) q)

def insideCount (i : J) : ℕ := (boundary (minor A r) (cellColour c i)).card

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
    mappedInside (A:=A) c i⊆boundary (L.graph next fixed) c := by
  intro z hz
  obtain ⟨e,em,rfl⟩ := mem_map.mp hz
  obtain ⟨xf,yt,a⟩ := mem_boundary.mp em
  exact mem_boundary.mpr ⟨xf,yt,Or.inl ⟨rfl,a⟩⟩

private theorem activeIncluded :
    (L.activeSeams next c).image (L.representedSeam next c)⊆boundary (L.graph next fixed) c := by
  intro e m
  obtain ⟨s,sm,rfl⟩ := mem_image.mp m
  have adj : (L.graph next fixed).Adj (L.startSeam s) (L.endSeam next s) :=
    Or.inr ⟨(s.1,true,s.2),rfl,(L.reverse_seam next s.1 s.2).1.symm⟩
  exact active_edge ((L.mem_active next c).mp sm) adj

/-- The host cut contains disjoint contributions from all internal
cuts and all active paired seams. Cardinalities may be added. -/
theorem host_cut_lower :
    (∑ i : J, insideCount (A:=A) c i)+(L.activeSeams next c).card ≤
      (boundary (L.graph next fixed) c).card := by
  classical
  let I := univ.biUnion (mappedInside (A:=A) c)
  let E := (L.activeSeams next c).image (L.representedSeam next c)
  have sep : Disjoint I E := by
    apply disjoint_left.mpr
    intro e hi he
    obtain ⟨i,_,inz⟩ := mem_biUnion.mp hi
    have coord := mappedIndex c inz
    obtain ⟨s,_,rfl⟩ := mem_image.mp he
    rcases orientation_cases (x:=L.startSeam s) (y:=L.endSeam next s) (c:=c) with x|x
    · change L.representedSeam next c s = _ at x
      rw [x] at coord
      exact fixed s.1 (coord.2.trans coord.1.symm)
    · change L.representedSeam next c s = _ at x
      rw [x] at coord
      exact fixed s.1 (coord.1.trans coord.2.symm)
  have sub : I∪E⊆boundary (L.graph next fixed) c := by
    intro v m
    rcases mem_union.mp m with ii|ee
    · obtain ⟨i,_,mi⟩ := mem_biUnion.mp ii
      exact L.mappedInside_mem next fixed c i mi
    · exact L.activeIncluded next fixed c ee
  have disj : (↑(univ : Finset J) : Set J).PairwiseDisjoint (mappedInside (A:=A) c) := by
    intro i _ j _ ne
    exact disjoint_left.mpr (fun x hi hj=>ne ((mappedIndex c hi).1.symm.trans (mappedIndex c hj).1))
  have bound := card_le_card sub
  rw [card_union_of_disjoint sep] at bound
  have ci : I.card=∑ i:J,insideCount (A:=A) c i := by
    change (univ.biUnion (mappedInside (A:=A) c)).card=_
    rw [card_biUnion disj]
    exact sum_congr rfl (fun i _=>card_map _)
  have ce : E.card=(L.activeSeams next c).card :=
    card_image_of_injective _ (L.represented_injective next c)
  rwa [ci,ce] at bound

#print axioms host_cut_lower
end
end KelmansCactus.FourRingReplica.Layout
