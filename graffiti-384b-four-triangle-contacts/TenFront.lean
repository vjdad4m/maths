import FourFront
import TenProtected
import Mathlib.Tactic.FinCases

namespace Graffiti384b.Four29
open Finset SimpleGraph Donor LowSample Ten
open private Repair.support_sub from Repair384b
open private Prune.links Prune.link_in_core from Prune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Four vertices outside the four anchors suffice to carry all anchor triangles. -/
theorem four_contacts (t : (types G).card=29) (h : (high G).card=27)
    (q : (nonleaves G).card=29) {e f : V} (de : G.degree e=2) (df : G.degree f=2) (ne : e≠f)
    (few : (triangleContacts G e f).card≤4) : gamma G≤bound G := by
  classical
  apply Nat.le_of_not_gt
  intro bad
  have D := data_of_failure G t h q bad de df ne
  let W := roots G e f
  let X := pool G e f
  let E : Finset V := {e,f}
  have highE : Disjoint (high G) E := disjoint_left.mpr (fun _ hi em =>
    (mem_sdiff.mp (D.earSet.symm ▸ em : _∈twos G)).2 hi)
  have ecard : E.card=2 := card_pair ne
  have xw : Disjoint X W := disjoint_left.mpr (fun _ ix => (mem_sdiff.mp ix).2)
  obtain ⟨T,ct,tx,tc⟩ := exists_subsuperset_card_eq (show triangleContacts G e f⊆X from filter_subset ..)
    few (show 4 ≤ X.card by have := D.poolSize; change X.card=23 at this; omega)
  obtain ⟨a,b,ab,en⟩ := card_eq_two.mp ((card_neighborFinset_eq_degree G e).trans de)
  obtain ⟨c,d,cd,fn'⟩ := card_eq_two.mp ((card_neighborFinset_eq_degree G f).trans df)
  obtain ⟨w,U,_,wu,uc⟩ := (Finset.card_eq_succ (n:=3)).mp tc
  obtain ⟨x,y,z,_,_,_,Uxyz⟩ := card_eq_three.mp uc
  have Twxyz : T={w,x,y,z} := by rw [←wu,Uxyz]
  have Wabcd : W={a,b}∪{c,d} := by change G.neighborFinset e ∪ G.neighborFinset f=_; rw [en,fn']
  let lab : Label→V := ![a,b,c,d,w,x,y,z,e,f]
  let S := W∪T∪E
  have inc : S⊆univ.image lab := by
    intro v vm
    simp only [S,Wabcd,Twxyz,E,mem_union,mem_insert,mem_singleton] at vm
    rcases vm with (((rfl|rfl)|(rfl|rfl))|(rfl|rfl|rfl|rfl))|(rfl|rfl)
    · exact mem_image.mpr ⟨0,mem_univ _,rfl⟩
    · exact mem_image.mpr ⟨1,mem_univ _,rfl⟩
    · exact mem_image.mpr ⟨2,mem_univ _,rfl⟩
    · exact mem_image.mpr ⟨3,mem_univ _,rfl⟩
    · exact mem_image.mpr ⟨4,mem_univ _,rfl⟩
    · exact mem_image.mpr ⟨5,mem_univ _,rfl⟩
    · exact mem_image.mpr ⟨6,mem_univ _,rfl⟩
    · exact mem_image.mpr ⟨7,mem_univ _,rfl⟩
    · exact mem_image.mpr ⟨8,mem_univ _,rfl⟩
    · exact mem_image.mpr ⟨9,mem_univ _,rfl⟩
  have highT := tx.trans (show X⊆high G from sdiff_subset)
  have sz : S.card=10 := by
    have dis := highE.mono_left (union_subset D.highRoots highT)
    rw [show S=W∪T∪E from rfl,card_union_of_disjoint dis,
      card_union_of_disjoint (xw.symm.mono_right tx),D.rootsSize,tc,ecard]
  have inject : Function.Injective lab := by
    have inj := (card_image_iff (s:=univ) (f:=lab)).mp (Nat.le_antisymm card_image_le (by
      have ct' := card_le_card inc; rw [sz] at ct'; simpa using ct'))
    exact fun i j eq => inj (mem_univ i) (mem_univ j) eq
  let idx : Label ↪ V := ⟨lab,inject⟩
  have rangeS {v : V} (vs : v∈S) : v∈Set.range idx := by
    obtain ⟨i,_,rfl⟩ := mem_image.mp (inc vs)
    exact ⟨i,rfl⟩
  have Wmem (i : Label) (ia : i∈anchors) : idx i∈W := by
    simp only [anchors,List.mem_cons,List.not_mem_nil,or_false] at ia
    rcases ia with rfl|rfl|rfl|rfl <;> rw [Wabcd] <;> simp [idx,lab]
  have star8 (j : Label) : G.Adj (idx 8) (idx j) ↔ j=0 ∨ j=1 := by
    change G.Adj e (idx j) ↔ _
    rw [←G.mem_neighborFinset,en,mem_insert,mem_singleton]
    change idx j=idx 0 ∨ idx j=idx 1 ↔ _
    simp only [idx.injective.eq_iff]
  have star9 (j : Label) : G.Adj (idx 9) (idx j) ↔ j=2 ∨ j=3 := by
    change G.Adj f (idx j) ↔ _
    rw [←G.mem_neighborFinset,fn',mem_insert,mem_singleton]
    change idx j=idx 2 ∨ idx j=idx 3 ↔ _
    simp only [idx.injective.eq_iff]
  have shape (i j : Label) (old : 8 ≤ i.val ∨ 8 ≤ j.val) : preset i j=true ↔ G.Adj (idx i) (idx j) := by
    have pred : (∀s:Label,preset 8 s=true ↔ s=0 ∨ s=1) ∧
        (∀s:Label,preset 9 s=true ↔ s=2 ∨ s=3) ∧ (∀r s:Label,preset r s=preset s r) := by decide
    have choices (a : Label) (ha : 8 ≤ a.val) : a=8 ∨ a=9 := by
      have tab : ∀b:Label,8 ≤ b.val → b=8 ∨ b=9 := by decide
      exact tab a ha
    rcases old with hi|hj
    · rcases choices i hi with rfl|rfl
      · exact (pred.1 j).trans (star8 j).symm
      · exact (pred.2.1 j).trans (star9 j).symm
    · rw [pred.2.2 i j,G.adj_comm]
      rcases choices j hj with rfl|rfl
      · exact (pred.1 i).trans (star8 i).symm
      · exact (pred.2.1 i).trans (star9 i).symm
  have win := ten_labels G idx (by omega) (fun v vm => by
    rw [D.earSet,mem_insert,mem_singleton] at vm; exact vm) shape (by
    intro i ia v vm
    obtain ⟨p,pm,vp⟩ := mem_biUnion.mp vm
    have vn : v∈nonleaves G := Prune.link_in_core G (show p∈Prune.links G (idx i) from pm) vp
    apply rangeS
    by_cases vh : v∈high G
    · by_cases vw : v∈W
      · exact mem_union_left _ (mem_union_left _ vw)
      · exact mem_union_left _ (mem_union_right _ (ct (mem_filter.mpr
          ⟨mem_sdiff.mpr ⟨vh,vw⟩,idx i,Wmem i ia,vm⟩)))
    · have ve : v∈twos G := mem_sdiff.mpr ⟨vn,vh⟩
      exact mem_union_right _ (show v∈E by change v∈({e,f}:Finset V); rwa [←D.earSet])) (fun i ia => D.rich _ (D.highRoots (Wmem i ia)))
      (fun a am b bm neq eq => neq (idx.injective (D.scoreInj (D.highRoots (Wmem a am)) (D.highRoots (Wmem b bm)) eq)))
  exact (not_lt_of_ge win) bad

/-- Necessary conditions for any surviving failure at the prescribed profile. -/
theorem four_contact_residual (t : (types G).card=29) (h : (high G).card=27)
    (q : (nonleaves G).card=29) (bad : bound G<gamma G) {e f : V}
    (de : G.degree e=2) (df : G.degree f=2) (ne : e≠f) :
    5≤(triangleContacts G e f).card ∧ (triangleContacts G e f).card≤(exposed G (pool G e f)).card ∧
    (exposed G (pool G e f)).card≤14 ∧
    ((exposed G (pool G e f)).card=14 → (twice G (pool G e f)).card≤6) ∧
    ((exposed G (pool G e f)).card=13 → (twice G (pool G e f)).card≤10) := by
  refine ⟨?_,(residual G t h q bad de df ne).2⟩
  by_contra! small
  exact (not_lt_of_ge (four_contacts G t h q de df ne (by omega))) bad

end Graffiti384b.Four29
#print axioms Graffiti384b.Four29.four_contacts
#print axioms Graffiti384b.Four29.four_contact_residual
