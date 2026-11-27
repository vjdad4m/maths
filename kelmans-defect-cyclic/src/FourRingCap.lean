import FourRingBudget

open Finset SimpleGraph
namespace KelmansCactus.FourRingCap
open ThreePort Substitute PathSlides ContactSlides NearPerfectCells FourRingBudget
noncomputable section
variable {V : Type*} [DecidableEq V] {G K : SimpleGraph V}

/-- Two distinct adjacent cap roots, each attached to two ports.
Additional edges are allowed in the cap. -/
structure Cap (K : SimpleGraph V) (A : Finset V) (p : Slot→V) (r : Bool→V) : Prop where
  outside : ∀ s,r s∉A
  rootEdge : K.Adj (r false) (r true)
  portEdge : ∀ s, K.Adj (r s.1) (p s)
  keep : ∀ x∈A, ∀ y∈A, G.Adj x y → K.Adj x y

private theorem bool_sum (f : Bool→ℕ) : (∑ b : Bool,f b)= f false+f true := by
  have eq : (univ : Finset Bool)={false,true} := by decide
  rw [eq,sum_insert (by decide : false∉({true} : Finset Bool)),sum_singleton]

theorem profile_sum (w : Slot→ℕ) : (∑ s : Slot,w s)=left w+right w := by
  rw [Fintype.sum_prod_type,bool_sum,bool_sum (fun b=>w (false,b)),bool_sum (fun b=>w (true,b))]
  rfl

private def portUnion (F : Slot→Finset V) : Finset V := univ.biUnion F
private def halfUnion (F : Slot→Finset V) (b : Bool) : Finset V :=
  univ.biUnion (fun c=>F (b,c))

private theorem half_subset (F : Slot→Finset V) (b : Bool) :
    halfUnion F b⊆portUnion F := by
  intro v h
  obtain ⟨c,_,hc⟩ := mem_biUnion.mp h
  exact mem_biUnion.mpr ⟨(b,c),mem_univ _,hc⟩

private theorem union_halves (F : Slot→Finset V) :
    halfUnion F false ∪ halfUnion F true = portUnion F := by
  apply le_antisymm (union_subset (half_subset F false) (half_subset F true))
  intro v h
  obtain ⟨⟨a,b⟩,_,hv⟩ := mem_biUnion.mp h
  cases a
  · exact mem_union_left _ (mem_biUnion.mpr ⟨b,mem_univ _,hv⟩)
  · exact mem_union_right _ (mem_biUnion.mpr ⟨b,mem_univ _,hv⟩)

private theorem fragments_inside {A : Finset V} {F : Slot→Finset V} {p : Slot→V}
    (hs : ∀ i,AtPort (G:=G) A (p i) (F i)) : portUnion F ⊆ A := by
  intro v vu
  obtain ⟨i,_,h⟩ := mem_biUnion.mp vu
  exact (hs i).inside h

private theorem half_partition {A : Finset V} {F : Slot→Finset V} {p : Slot→V} {w : Slot→ℕ}
    (hs : ∀ i,(F i).card=w i ∧ AtPort (G:=G) A (p i) (F i))
    (sep : ∀ i j,i≠j→Disjoint (F i) (F j)) (b : Bool) :
    Signature (G:=G) (halfUnion F b) (fun c=>p (b,c)) (fun c=>w (b,c)) := by
  refine ⟨fun c=>F (b,c),?_,?_,∅,?_⟩
  · intro c
    obtain ⟨size,port⟩ := hs (b,c)
    exact ⟨size,⟨fun x hx=>mem_biUnion.mpr ⟨c,mem_univ _,hx⟩,
      port.includes,port.star⟩⟩
  · intro c d ne
    exact sep (b,c) (b,d) (fun e=>ne (congrArg Prod.snd e))
  · refine ⟨by simp,by simp,?_⟩
    simp [halfUnion]

private theorem inside_closed {A : Finset V} {F : Slot→Finset V} {p : Slot→V}
    {r : Bool→V} {P : Parts V}
    (cp : Cap (G:=G) K A p r) (h : Assemble.LocalPart G P (A\portUnion F)) :
    Closed K (A\portUnion F) :=
  ⟨P,change_edges h (fun a ha b hb=>cp.keep a (mem_sdiff.mp ha).1 b (mem_sdiff.mp hb).1)⟩

/-- Any width-one signature caps: both roots and the unique exported
port make the last path. -/
theorem export_one_caps {A : Finset V} {p : Slot→V} {w : Slot→ℕ}
    {r : Bool→V} (cp : Cap (G:=G) K A p r)
    (sig : Signature (G:=G) A p w) (one : (∑ i : Slot,w i)=1) :
    Closed K (insert (r false) (insert (r true) A)) := by
  classical
  obtain ⟨F,hs,sep,P,hP⟩ := sig
  have ua : portUnion F⊆A := fragments_inside (fun i=>(hs i).2)
  have uCard : (portUnion F).card=1 := by
    unfold portUnion
    rw [card_biUnion (fun i _ j _ ne=>sep i j ne),←one]
    exact sum_congr rfl (fun i _=>(hs i).1)
  obtain ⟨v,eq⟩ := card_eq_one.mp uCard
  have vu : v∈portUnion F := eq.symm ▸ mem_singleton_self v
  have va : v∈A := ua vu
  obtain ⟨i,_,vi⟩ := mem_biUnion.mp vu
  have pp := (hs i).2.includes ⟨v,vi⟩
  have pu : p i∈portUnion F := mem_biUnion.mpr ⟨i,mem_univ _,pp⟩
  have pv : p i=v := mem_singleton.mp (eq ▸ pu)
  have vaEdge : K.Adj (r i.1) v := pv ▸ cp.portEdge i
  have rf : v≠r false := fun e=>cp.outside false (e ▸ va)
  have rt : v≠r true := fun e=>cp.outside true (e ▸ va)
  let W : Finset V := {r false,r true,v}
  have tile : KelmansStarter.IsTile K W := by
    have order : ({r true,r false,v} : Finset V)=W := by
      ext x
      simp only [W,mem_insert,mem_singleton]
      tauto
    cases h : i.1
    · rw [h] at vaEdge
      exact order ▸ path_tile K cp.rootEdge.symm vaEdge rt.symm
    · rw [h] at vaEdge
      exact path_tile K cp.rootEdge vaEdge rf.symm
  have apart : Disjoint (A\portUnion F) W := by
    apply disjoint_left.mpr
    intro x hx wx
    simp only [W,mem_insert,mem_singleton] at wx
    rcases wx with rfl|rfl|rfl
    · exact cp.outside false (mem_sdiff.mp hx).1
    · exact cp.outside true (mem_sdiff.mp hx).1
    · exact (mem_sdiff.mp hx).2 vu
  have glued := add_closed (inside_closed cp hP) (tile_closed tile) apart
  have cov : (A\portUnion F)∪W = insert (r false) (insert (r true) A) := by
    ext x
    constructor
    · intro q
      rcases mem_union.mp q with q|q
      · exact mem_insert_of_mem (mem_insert_of_mem (mem_sdiff.mp q).1)
      · simp only [W,mem_insert,mem_singleton] at q
        rcases q with rfl|rfl|rfl
        · exact mem_insert_self _ _
        · exact mem_insert_of_mem (mem_insert_self _ _)
        · exact mem_insert_of_mem (mem_insert_of_mem va)
    · intro hx
      simp only [mem_insert] at hx
      rcases hx with rfl|rfl|xa
      · exact mem_union_right _ (mem_insert_self _ _)
      · exact mem_union_right _ (mem_insert_of_mem (mem_insert_self _ _))
      · by_cases xu : x∈portUnion F
        · obtain rfl := mem_singleton.mp (eq ▸ xu)
          exact mem_union_right _ (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _)))
        · exact mem_union_left _ (mem_sdiff.mpr ⟨xa,xu⟩)
  rwa [cov] at glued

/-- A width-four signature caps when precisely two vertices
are exported by each pair of ports. Each root caps its own
two-vertex half independently. -/
theorem export_balanced_caps {A : Finset V} {p : Slot→V} {w : Slot→ℕ}
    {r : Bool→V} (cp : Cap (G:=G) K A p r)
    (sig : Signature (G:=G) A p w) (l : left w=2) (rr : right w=2) :
    Closed K (insert (r false) (insert (r true) A)) := by
  classical
  obtain ⟨F,hs,sep,P,hP⟩ := sig
  have ua : portUnion F⊆A := fragments_inside (fun i=>(hs i).2)
  have hh (b : Bool) : Closed K (insert (r b) (halfUnion F b)) := by
    have ends : (∑ c : Bool,w (b,c))=2 := by
      rw [bool_sum]
      cases b
      · exact l
      · exact rr
    exact export_two_caps (half_partition hs sep b) ends
      (fun h=>cp.outside b (ua (half_subset F b h)))
      (fun x hx y hy=>cp.keep x (ua (half_subset F b hx)) y (ua (half_subset F b hy)))
      (fun c=>cp.portEdge (b,c))
  have halvesDisj : Disjoint (insert (r false) (halfUnion F false))
      (insert (r true) (halfUnion F true)) := by
    apply disjoint_left.mpr
    intro x x0 x1
    rcases mem_insert.mp x0 with rfl | h0
    · rcases mem_insert.mp x1 with eq|fr
      · exact cp.rootEdge.ne eq
      · exact cp.outside false (ua (half_subset F true fr))
    rcases mem_insert.mp x1 with rfl | h1
    · exact cp.outside true (ua (half_subset F false h0))
    · obtain ⟨i,_,hi⟩ := mem_biUnion.mp h0
      obtain ⟨j,_,hj⟩ := mem_biUnion.mp h1
      exact disjoint_left.mp (sep (false,i) (true,j) (fun e=>Bool.false_ne_true (congrArg Prod.fst e))) hi hj
  let S := insert (r false) (halfUnion F false) ∪ insert (r true) (halfUnion F true)
  have sc : Closed K S := add_closed (hh false) (hh true) halvesDisj
  have sm : S = insert (r false) (insert (r true) (portUnion F)) := by
    rw [←union_halves F]
    ext x
    simp only [S,mem_union,mem_insert]
    tauto
  have sep' : Disjoint (A\portUnion F) S := by
    rw [sm]
    apply disjoint_left.mpr
    intro x xr xs
    rcases mem_insert.mp xs with rfl | xs
    · exact cp.outside false (mem_sdiff.mp xr).1
    rcases mem_insert.mp xs with rfl | xs
    · exact cp.outside true (mem_sdiff.mp xr).1
    · exact (mem_sdiff.mp xr).2 xs
  have yes := add_closed (inside_closed cp hP) sc sep'
  have eq : (A\portUnion F)∪S=insert (r false) (insert (r true) A) := by
    rw [sm]
    ext x
    have sub : x∈portUnion F → x∈A := fun h=>ua h
    simp only [mem_union,mem_sdiff,mem_insert]
    tauto
  rwa [eq] at yes

#print axioms export_one_caps
#print axioms export_balanced_caps
end
end KelmansCactus.FourRingCap
