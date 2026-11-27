import FourRingCap

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ActiveCaps
open ThreePort Substitute PathSlides ContactSlides NearPerfectCells FourRingBudget
noncomputable section
variable {V : Type*} [DecidableEq V] {G K : SimpleGraph V}

structure ActiveCap (K : SimpleGraph V) (A : Finset V) (p : Slot→V)
    (r : Bool→V) (w : Slot→ℕ) : Prop where
  outside : ∀ s,r s∉A
  root_ne : r false≠r true
  portEdge : ∀ s,0<w s→K.Adj (r s.1) (p s)
  keep : ∀ x∈A,∀ y∈A,G.Adj x y→K.Adj x y

variable {I : Type*} [Fintype I]
/-- Export of exactly two vertices always lifts to a factor of the
one-vertex cap. They lie together in one fragment, or in two
different singleton fragments whose vertices are both cap neighbors. -/
theorem export_two_active_caps {A : Finset V} {p : I→V} {w : I→ℕ} {r : V} {K : SimpleGraph V}
    (sig : Signature (G:=G) A p w) (two : (∑ i:I,w i)=2) (out : r∉A)
    (edges : ∀ x∈A, ∀ y∈A, G.Adj x y → K.Adj x y)
    (cap : ∀ i,0<w i→K.Adj r (p i)) : Closed K (insert r A) := by
  classical
  obtain ⟨F,frag,sep,P,pack⟩ := sig
  let U := univ.biUnion F
  have UA : U⊆A := by
    intro v vu
    obtain ⟨i,_,vi⟩ := mem_biUnion.mp vu
    exact (frag i).2.inside vi
  have count : U.card=2 := by
    rw [show U=univ.biUnion F from rfl,card_biUnion (fun i _ j _ ne => sep i j ne),←two]
    exact sum_congr rfl (fun i _ => (frag i).1)
  obtain ⟨x,y,xy,eqU⟩ := card_eq_two.mp count
  have xU : x∈U := eqU.symm ▸ mem_insert_self _ _
  have yU : y∈U := eqU.symm ▸ mem_insert_of_mem (mem_singleton_self _)
  have xA := UA xU
  have yA := UA yU
  have rx : r≠x := fun e => out (e.symm ▸ xA)
  have ry : r≠y := fun e => out (e.symm ▸ yA)
  obtain ⟨i,_,xi⟩ := mem_biUnion.mp xU
  obtain ⟨j,_,yj⟩ := mem_biUnion.mp yU
  have wi : 0<w i := by
    rw [←(frag i).1]
    exact card_pos.mpr ⟨x,xi⟩
  have wj : 0<w j := by
    rw [←(frag j).1]
    exact card_pos.mpr ⟨y,yj⟩
  have pi := (frag i).2.includes ⟨x,xi⟩
  have pj := (frag j).2.includes ⟨y,yj⟩
  have pU (k) {v} (f : v∈F k) : v=x ∨ v=y := by
    have aa : v∈U := mem_biUnion.mpr ⟨k,mem_univ _,f⟩
    simpa [eqU] using aa
  have piece : KelmansStarter.IsTile K ({r,x,y}:Finset V) := by
    by_cases same : i=j
    · subst j
      rcases pU i pi with ex|ey
      · have py : p i≠y := fun e => xy (ex.symm.trans e)
        have g := (frag i).2.star y yj (Ne.symm py)
        exact path_tile K (ex ▸ cap i wi) (edges x xA y yA (ex ▸ g)) ry
      · have px : p i≠x := fun e => xy (e.symm.trans ey)
        have g := (frag i).2.star x xi (Ne.symm px)
        obtain h := path_tile K (ey ▸ cap i wi) (edges y yA x xA (ey ▸ g)) rx
        have reorder : ({r,y,x}:Finset V)={r,x,y} := by
          ext z; simp only [mem_insert,mem_singleton]; tauto
        exact reorder ▸ h
    · have ex : p i=x := (pU i pi).resolve_right (fun eq =>
        disjoint_left.mp (sep i j same) (eq ▸ pi) yj)
      have ey : p j=y := (pU j pj).resolve_left (fun eq =>
        disjoint_left.mp (sep i j same) xi (eq ▸ pj))
      have h := path_tile K (ex ▸ (cap i wi).symm) (ey ▸ cap j wj) xy
      have reorder : ({x,r,y}:Finset V)={r,x,y} := by
        ext z; simp only [mem_insert,mem_singleton]; tauto
      exact reorder ▸ h
  have rest : Closed K (A\U) :=
    ⟨P,change_edges pack (fun a ha b hb => edges a (mem_sdiff.mp ha).1 b (mem_sdiff.mp hb).1)⟩
  have apart : Disjoint (A\U) ({r,x,y}:Finset V) := by
    apply disjoint_left.mpr
    intro v av pv
    simp only [mem_insert,mem_singleton] at pv
    rcases pv with rfl|rfl|rfl
    · exact out (mem_sdiff.mp av).1
    · exact (mem_sdiff.mp av).2 xU
    · exact (mem_sdiff.mp av).2 yU
  have outEq : A\U ∪ {r,x,y}=insert r A := by
    ext z
    simp only [mem_union, mem_sdiff,mem_insert,mem_singleton]
    constructor
    · rintro (⟨za,_⟩|rfl|rfl|rfl)
      · exact Or.inr za
      · exact Or.inl rfl
      · exact Or.inr xA
      · exact Or.inr yA
    · rintro (rfl|za)
      · exact Or.inr (Or.inl rfl)
      · by_cases uz : z∈U
        · have p : z=x ∨ z=y := by simpa [eqU] using uz
          exact Or.inr (Or.inr p)
        · exact Or.inl ⟨za,uz⟩
  exact outEq ▸ add_closed rest (tile_closed piece) apart

private theorem bool_sum (f : Bool→ℕ) : (∑ b : Bool,f b)= f false+f true := by
  have eq : (univ : Finset Bool)={false,true} := by decide
  rw [eq,sum_insert (by decide : false∉({true} : Finset Bool)),sum_singleton]

private theorem profile_sum (w : Slot→ℕ) : (∑ s : Slot,w s)=left w+right w := by
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
    {r : Bool→V} {P : Parts V} {w : Slot→ℕ}
    (cp : ActiveCap (G:=G) K A p r w) (h : Assemble.LocalPart G P (A\portUnion F)) :
    Closed K (A\portUnion F) :=
  ⟨P,change_edges h (fun a ha b hb=>cp.keep a (mem_sdiff.mp ha).1 b (mem_sdiff.mp hb).1)⟩

/-- A width-four signature caps when precisely two vertices
are exported by each pair of ports. Each root caps its own
two-vertex half independently. -/
theorem export_balanced_active_caps {A : Finset V} {p : Slot→V} {w : Slot→ℕ}
    {r : Bool→V} (cp : ActiveCap (G:=G) K A p r w)
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
    exact export_two_active_caps (half_partition hs sep b) ends
      (fun h=>cp.outside b (ua (half_subset F b h)))
      (fun x hx y hy=>cp.keep x (ua (half_subset F b hx)) y (ua (half_subset F b hy)))
      (fun c pos=>cp.portEdge (b,c) pos)
  have halvesDisj : Disjoint (insert (r false) (halfUnion F false))
      (insert (r true) (halfUnion F true)) := by
    apply disjoint_left.mpr
    intro x x0 x1
    rcases mem_insert.mp x0 with rfl | h0
    · rcases mem_insert.mp x1 with eq|fr
      · exact cp.root_ne eq
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

#print axioms export_balanced_active_caps
end
end KelmansCactus.AtomicBridge.ActiveCaps
