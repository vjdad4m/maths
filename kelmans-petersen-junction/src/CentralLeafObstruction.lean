import Substitute

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.CentralLeafObstruction
open Substitute
set_option maxRecDepth 2000
set_option maxHeartbeats 6000000

/-- Label the Petersen graph by its outer pentagon 0--4, the five
matching edges, and inner step-two pentagon 5--9. -/
def edge (v w : Fin 10) : Bool :=
  if v.val < 5 then
    if w.val < 5 then (w.val = (v.val+1)%5 || v.val = (w.val+1)%5)
    else w.val == v.val + 5
  else if w.val < 5 then v.val == w.val + 5
  else (w.val-5 = (v.val-5+2)%5 || v.val-5 = (w.val-5+2)%5)

def pet : SimpleGraph (Fin 10) where
  Adj v w := edge v w = true
  symm := by
    have sym : ∀ v w, edge v w = edge w v := by decide
    intro v w e
    exact (sym v w).symm.trans e
  loopless := by
    have noDiag : ∀ v, edge v v = false := by decide
    intro v e
    exact Bool.noConfusion ((noDiag v).symm.trans e)

instance : DecidableRel pet.Adj := fun v w => inferInstanceAs (Decidable (edge v w = true))

theorem pet_cubic : ∀ v, pet.degree v = 3 := by decide

private def remaining (v : Fin 10) : Finset (Fin 10) := univ \ {0,2,8,v}

/-- An anchor tile leaves an isolated vertex in the residual graph. This
predicate only checks tiles in a six-vertex residual region. -/
private def anchorObstruction (R : Finset (Fin 10)) (a : Fin 10) : Prop :=
  ∀ T ∈ R.powerset, a ∈ T → KelmansStarter.IsTile pet T →
    ∃ w ∈ R, w ∉ T ∧ ∀ z ∈ R, z ∉ T → ¬ pet.Adj w z

private theorem obstructs (R : Finset (Fin 10)) (a : Fin 10) (ha : a∈R)
    (bad : anchorObstruction R a) : ¬ Closed pet R := by
  rintro ⟨P,hP⟩
  obtain ⟨T,hT,aT⟩ := mem_biUnion.mp (hP.cover.symm ▸ ha)
  obtain ⟨w,wR,wT,bad'⟩ := bad T (mem_powerset.mpr (hP.tile_sub pet hT)) aT (hP.tile T hT)
  obtain ⟨S,hS,wS⟩ := mem_biUnion.mp (hP.cover.symm ▸ wR)
  have n : S ≠ T := fun e=>wT (e ▸ wS)
  have iso (z : Fin 10) (zS : z∈S) : ¬ pet.Adj w z :=
    bad' z (hP.tile_sub pet hS zS) (fun h=> disjoint_left.mp (hP.disj S hS T hT n) zS h)
  have hs := hP.tile S hS
  obtain ⟨i,j,k,_,_,_,ij,jk,eq⟩ := (Kelmans.tile_iff_path pet S hs.1).mp hs.2
  have iS : i∈S := eq.symm ▸ mem_insert_self _ _
  have jS : j∈S := eq.symm ▸ mem_insert_of_mem (mem_insert_self _ _)
  change w ∈ S at wS
  rw [eq] at wS
  simp only [mem_insert,mem_singleton] at wS
  rcases wS with rfl|rfl|rfl
  · exact iso j jS ij
  · exact iso i iS ij.symm
  · exact iso j jS jk.symm

private theorem anchor_with_one_neighbor (R : Finset (Fin 10)) {a b u v : Fin 10}
    (ab : a≠b) (au : a≠u) (av : a≠v) (bu : b≠u) (bv : b≠v)
    (first : ∀ x ∈ R, pet.Adj a x → x=b)
    (second : ∀ x ∈ R, pet.Adj b x → x=a ∨ x=u ∨ x=v)
    (T : Finset (Fin 10)) (inc : T⊆R) (atA : a∈T) (tile : KelmansStarter.IsTile pet T) :
    T={a,b,u} ∨ T={a,b,v} := by
  obtain ⟨n,c,ct,adj⟩ := tile
  have cb : c=b := by
    by_cases ec : c=a
    · subst c
      have ss : T⊆({a,b}:Finset (Fin 10)) := by
        intro x xT
        by_cases xa : x=a
        · simp [xa]
        · simp [first x (inc xT) (adj x xT xa)]
      have wrong := card_le_card ss
      rw [n] at wrong
      simp [ab] at wrong
    · exact first c (inc ct) (adj a atA (fun e=>ec e.symm)).symm
  subst c
  have other : u∈T ∨ v∈T := by
    by_contra no
    have ss : T⊆({a,b}:Finset (Fin 10)) := by
      intro x xT
      by_cases xb : x=b
      · simp [xb]
      · rcases second x (inc xT) (adj x xT xb) with ea|eu|ev
        · simp [ea]
        · exact (no (Or.inl (eu ▸ xT))).elim
        · exact (no (Or.inr (ev ▸ xT))).elim
    have wrong := card_le_card ss
    rw [n] at wrong
    simp [ab] at wrong
  rcases other with h|h
  · left
    symm
    apply eq_of_subset_of_card_le (insert_subset_iff.mpr ⟨atA,insert_subset_iff.mpr
      ⟨ct,singleton_subset_iff.mpr h⟩⟩)
    simp [n,ab,au,bu]
  · right
    symm
    apply eq_of_subset_of_card_le (insert_subset_iff.mpr ⟨atA,insert_subset_iff.mpr
      ⟨ct,singleton_subset_iff.mpr h⟩⟩)
    simp [n,ab,av,bv]

private theorem isolate_directly (R : Finset (Fin 10)) (a : Fin 10)
    (h : ∀ x∈R, ¬ pet.Adj a x) : anchorObstruction R a := by
  intro T TR aT f
  have sub := mem_powerset.mp TR
  obtain ⟨n,c,cT,adj⟩ := f
  by_cases ac : a=c
  · subst c
    have ss : T⊆({a}:Finset (Fin 10)) := by
      intro x xT
      by_cases xa : x=a
      · simp [xa]
      · exact (h x (sub xT) (adj x xT xa)).elim
    have impossible := card_le_card ss
    simp [n] at impossible
  · exact (h c (sub cT) (adj a aT ac).symm).elim

private theorem rem3 : anchorObstruction (remaining 3) 4 := by
  intro T TR aT t
  have c := anchor_with_one_neighbor (remaining 3) (a:=4) (b:=9) (u:=6) (v:=7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) T (mem_powerset.mp TR) aT t
  rcases c with rfl | rfl
  · exact ⟨1,by decide,by decide,by decide⟩
  · exact ⟨5,by decide,by decide,by decide⟩

private theorem rem5 : anchorObstruction (remaining 5) 7 := by
  intro T TR aT t
  have c := anchor_with_one_neighbor (remaining 5) (a:=7) (b:=9) (u:=4) (v:=6)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) T (mem_powerset.mp TR) aT t
  rcases c with rfl | rfl
  · exact ⟨3,by decide,by decide,by decide⟩
  · exact ⟨1,by decide,by decide,by decide⟩

private theorem only_partners : ∀ v, pet.Adj 8 v → v = 3 ∨ v = 5 ∨ v = 6 := by decide

/-- A central Petersen graph with closed markers 0 and 2 and a
single-width-two marker 8 has no central stitching of this limited kind:
whichever neighbor of 8 is supplied to the third atom, the ordinary
remainder has no three-vertex path factor. -/
theorem no_single_leaf_stitch : ¬ ∃ v, pet.Adj 8 v ∧ Closed pet (remaining v) := by
  rintro ⟨v,e,f⟩
  rcases only_partners v e with rfl|rfl|rfl
  · exact obstructs (remaining 3) 4 (by decide) rem3 f
  · exact obstructs (remaining 5) 7 (by decide) rem5 f
  · exact obstructs (remaining 6) 1 (by decide) (isolate_directly _ _ (by decide)) f

#print axioms no_single_leaf_stitch
end KelmansCactus.AtomicBridge.CentralLeafObstruction
