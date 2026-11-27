import NearPerfectBudget
import Substitute
import PathSlides
import ContactSlides

open Finset
namespace KelmansCactus.NearPerfectCells
open ThreePort SpareChord Substitute PathSlides ContactSlides

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {I : Type*} [Fintype I]

/-- Select the old tile using a seam only if it contains both
matched endpoints. Packing disjointness makes this choice unique. -/
noncomputable def tileAt (P : Parts V) (x y : V) : Finset V := by
  classical
  exact if h : ∃ t∈P, x∈t ∧ y∈t then Classical.choose h else ∅

noncomputable def width (P : Parts V) (A : Finset V) (x y : V) : ℕ :=
  (tileAt P x y ∩ A).card

omit [Fintype V] in
theorem tileAt_of_use {P : Parts V} {x y : V} (h : ∃ t∈P,x∈t ∧ y∈t) :
    tileAt P x y∈P ∧ x∈tileAt P x y ∧ y∈tileAt P x y := by
  classical
  unfold tileAt
  rw [dif_pos h]
  exact Classical.choose_spec h

omit [Fintype V] in
theorem tileAt_of_no_use {P : Parts V} {x y : V} (h : ¬∃ t∈P,x∈t ∧ y∈t) :
    tileAt P x y=∅ := by
  classical
  simp [tileAt,h]

omit [Fintype V] in
theorem unique_tileAt {D : Finset V} {P : Parts V} (ok : PackIn G D P)
    {x y : V} {T : Finset V} (tt : T∈P) (xt : x∈T) (yt : y∈T) :
    tileAt P x y=T := by
  classical
  obtain ⟨tp,vx,_⟩ := tileAt_of_use (P:=P) ⟨T,tt,xt,yt⟩
  by_contra ne
  exact disjoint_left.mp (ok.part.disj _ tp _ tt ne) vx xt

omit [Fintype V] in
theorem width_le_two {D A : Finset V} {P : Parts V}
    (ok : PackIn G D P) {x y : V} (outside : y∉A) :
    width P A x y≤2 := by
  classical
  by_cases use : ∃ t∈P,x∈t ∧ y∈t
  · obtain ⟨tp,_,yt⟩ := tileAt_of_use use
    have cap : tileAt P x y ∩ A ⊆ (tileAt P x y).erase y := by
      intro v hv
      obtain ⟨vt,va⟩ := mem_inter.mp hv
      exact mem_erase.mpr ⟨fun eq => outside (eq ▸ va),vt⟩
    have n := card_le_card cap
    rw [card_erase_of_mem yt,(ok.part.tile _ tp).1] at n
    exact n
  · simp only [width,tileAt_of_no_use use,empty_inter,card_empty,zero_le]

omit [Fintype V] [DecidableEq V] [Fintype I] in
private theorem unique_exit {A : Finset V} {p q : I→V}
    (H : Seam (G:=G) A p q) (i : I) {v : V}
    (outside : v∉A) (e : G.Adj (p i) v) : v=q i := by
  obtain ⟨j,jp,jq⟩ := (H.edge (p i) (H.left i) v outside).mp e
  have eq : j=i := H.left_inj jp
  exact eq ▸ jq.symm

omit [Fintype V] [Fintype I] in
/-- Each matched seam is unused or carries a pair of complementary widths.
Even if a third vertex is outside both cells, a tile spanning it and both
ports would violate one of the two ports' unique outside exits. -/
theorem opposite_at_shared_seam {D A B : Finset V} {P : Parts V} (ok : PackIn G D P)
    {p q p' q' : I→V} (HA : Seam (G:=G) A p q) (HB : Seam (G:=G) B p' q')
    (separate : Disjoint A B) (i j : I) (flip1 : p' j=q i) (flip2 : q' j=p i) :
    Opposite (width P A (p i) (q i)) (width P B (p' j) (q' j)) := by
  classical
  by_cases use : ∃ t∈P,p i∈t ∧ q i∈t
  · let T := tileAt P (p i) (q i)
    obtain ⟨tp,pt,qt⟩ := tileAt_of_use use
    have same : tileAt P (p' j) (q' j)=T :=
      unique_tileAt ok tp (flip1.symm ▸ qt) (flip2.symm ▸ pt)
    have whole : T ⊆ A∪B := by
      intro v vt
      by_contra vv
      have va : v∉A := fun h=>vv (mem_union_left _ h)
      have vb : v∉B := fun h=>vv (mem_union_right _ h)
      have vp : v≠p i := fun e=>va (e.symm ▸ HA.left i)
      have vq : v≠q i := fun e=>vb (e.symm ▸ flip1 ▸ HB.left j)
      obtain ⟨_,c,ct,cAdj⟩ := ok.part.tile _ tp
      by_cases pc : c=p i
      · exact vq (unique_exit HA i va (pc ▸ cAdj v vt (pc.symm ▸ vp)))
      by_cases qc : c=q i
      · have c' : c=p' j := qc.trans flip1.symm
        exact vp (unique_exit HB j vb (c' ▸ cAdj v vt (c'.symm ▸ flip1 ▸ vq)) |>.trans flip2)
      have cA : c∈A := by
        by_contra ca
        exact qc (unique_exit HA i ca (cAdj (p i) pt (Ne.symm pc)).symm)
      have cB : c∈B := by
        by_contra cb
        have e : G.Adj (p' j) c := flip1.symm ▸ (cAdj (q i) qt (Ne.symm qc)).symm
        exact pc ((unique_exit HB j cb e).trans flip2)
      exact disjoint_left.mp separate cA cB
    have inters : (T∩A)∪(T∩B)=T := by
      rw [← inter_union_distrib_left]
      exact inter_eq_left.mpr whole
    have sum := card_union_of_disjoint (separate.mono inter_subset_right inter_subset_right :
      Disjoint (T∩A) (T∩B))
    rw [inters,(ok.part.tile _ tp).1] at sum
    have pa : 0<(T∩A).card := card_pos.mpr ⟨p i,mem_inter.mpr ⟨pt,HA.left i⟩⟩
    have qb : 0<(T∩B).card := card_pos.mpr ⟨q i,mem_inter.mpr ⟨qt,flip1 ▸ HB.left j⟩⟩
    right
    unfold width
    rw [same]
    change 1≤(T∩A).card ∧ (T∩A).card≤2 ∧ 1≤(T∩B).card ∧
      (T∩B).card≤2 ∧ (T∩A).card+(T∩B).card=3
    omega
  · have none : ¬∃ t∈P,p' j∈t ∧ q' j∈t := by
      rintro ⟨t,tp,bp,bq⟩
      exact use ⟨t,tp,flip2 ▸ bq,flip1 ▸ bp⟩
    exact Or.inl (by simp [width,tileAt_of_no_use use,tileAt_of_no_use none])

/-- Extract the rooted cell's signature even from an ambient partial
packing, on the covered vertices of a cell; the seam is unchanged. -/
theorem signature_of_partially_covered_cell {D A : Finset V} {P : Parts V} {p q : I→V}
    (ok : PackIn G D P) (H : Seam (G:=G) A p q) :
    Signature (G:=G) (A∩P.biUnion id) p (fun i => width P A (p i) (q i)) := by
  classical
  let T := fun i => tileAt P (p i) (q i)
  let F := fun i => T i∩A
  have Huse (i : I) (h : ∃ t∈P,p i∈t ∧ q i∈t) :
      T i∈P ∧ p i∈T i ∧ q i∈T i := tileAt_of_use h
  have mixed (i : I) (h : ∃ t∈P,p i∈t ∧ q i∈t) :
      Mixed A (T i) := by
    obtain ⟨_,l,r⟩ := Huse i h
    exact ⟨⟨p i,l,H.left i⟩,⟨q i,r,H.right i⟩⟩
  have atP (i : I) (h : ∃ t∈P,p i∈t ∧ q i∈t) :
      AtPort (G:=G) A (p i) (F i) ∧ ((T i∩A).card=1 ∨ (T i\A).card=1) := by
    obtain ⟨hr,ip,iq⟩ := Huse i h
    obtain ⟨j,jp,jq,ap,_,sm⟩ := describe_mixed_tile H (ok.part.tile _ hr) (mixed i h)
    have eq := mixed_uses_only_one_slot H ip iq jp jq sm
    exact ⟨eq.symm ▸ ap,sm⟩
  have falseT (i) (no : ¬∃ t∈P,p i∈t ∧ q i∈t) : T i=∅ := tileAt_of_no_use no
  let Q := P.filter (fun t => t⊆A)
  refine ⟨F,?_,?_,Q,⟨?_,?_,?_⟩⟩
  · intro i
    refine ⟨rfl,?_⟩
    by_cases use : ∃ t∈P,p i∈t ∧ q i∈t
    · obtain ⟨ins,hit,star⟩ := (atP i use).1
      exact ⟨fun v hv=>mem_inter.mpr ⟨ins hv,
        mem_biUnion.mpr ⟨T i,(Huse i use).1,(mem_inter.mp hv).1⟩⟩,hit,star⟩
    · change AtPort (G:=G) (A∩P.biUnion id) (p i) (T i∩A)
      rw [falseT i use,empty_inter]
      exact ⟨empty_subset _,fun e => (not_nonempty_empty e).elim,by simp⟩
  · intro i j ne
    by_cases a : ∃ t∈P,p i∈t ∧ q i∈t
    · by_cases b : ∃ t∈P,p j∈t ∧ q j∈t
      · obtain ⟨iP,ip,iq⟩ := Huse i a
        obtain ⟨jP,jp,jq⟩ := Huse j b
        have diff : T i≠T j := fun e => ne
          (mixed_uses_only_one_slot H ip iq (e.symm ▸ jp) (e.symm ▸ jq) (atP i a).2)
        exact (ok.part.disj _ iP _ jP diff).mono inter_subset_left inter_subset_left
      · change Disjoint (T i∩A) (T j∩A)
        simp [falseT j b]
    · change Disjoint (T i∩A) (T j∩A)
      simp [falseT i a]
  · intro t tp
    exact ok.part.tile _ (mem_filter.mp tp).1
  · intro t tQ u uQ ne
    exact ok.part.disj _ (mem_filter.mp tQ).1 _ (mem_filter.mp uQ).1 ne
  · ext x
    change x∈Q.biUnion id ↔ x∈(A∩P.biUnion id)\univ.biUnion F
    constructor
    · intro hx
      obtain ⟨t,tt,xt⟩ := mem_biUnion.mp hx
      obtain ⟨tp,tA⟩ := mem_filter.mp tt
      refine mem_sdiff.mpr ⟨mem_inter.mpr ⟨tA xt,mem_biUnion.mpr ⟨t,tp,xt⟩⟩,?_⟩
      intro vx
      obtain ⟨i,_,xi⟩ := mem_biUnion.mp vx
      have Ti : x∈T i := (mem_inter.mp xi).1
      have use : ∃ t∈P,p i∈t ∧ q i∈t := by
        by_cases yes : ∃ t∈P,p i∈t ∧ q i∈t
        · exact yes
        · exact (not_mem_empty x (falseT i yes ▸ Ti)).elim
      obtain ⟨ip,_,ri⟩ := Huse i use
      have ne : t≠T i := fun e => H.right i (tA (e.symm ▸ ri))
      exact disjoint_left.mp (ok.part.disj _ tp _ ip ne) xt Ti
    · intro hx
      obtain ⟨xA,none⟩ := mem_sdiff.mp hx
      obtain ⟨t,tp,xt⟩ := mem_biUnion.mp ((mem_inter.mp xA).2)
      have tA : t⊆A := by
        intro v vt
        by_contra vn
        have mix : Mixed A t := ⟨⟨x,xt,(mem_inter.mp xA).1⟩,⟨v,vt,vn⟩⟩
        obtain ⟨i,ip,iq,_⟩ := describe_mixed_tile H (ok.part.tile _ tp) mix
        have eq : T i=t := unique_tileAt ok tp ip iq
        exact none (mem_biUnion.mpr ⟨i,mem_univ _,mem_inter.mpr ⟨eq.symm ▸ xt,(mem_inter.mp xA).1⟩⟩)
      exact mem_biUnion.mpr ⟨t,mem_filter.mpr ⟨tp,tA⟩,xt⟩

/-- In a cell with no vacancies, the signature covers the entire cell. -/
theorem signature_of_covered_cell {D A : Finset V} {P : Parts V} {p q : I→V}
    (ok : PackIn G D P) (cell : A⊆P.biUnion id) (H : Seam (G:=G) A p q) :
    Signature (G:=G) A p (fun i => width P A (p i) (q i)) := by
  simpa only [inter_eq_left.mpr cell] using signature_of_partially_covered_cell ok H

omit [Fintype V] in
/-- Export of exactly two vertices always lifts to a factor of the
one-vertex cap. They lie together in one fragment, or in two
different singleton fragments whose vertices are both cap neighbors. -/
theorem export_two_caps {A : Finset V} {p : I→V} {w : I→ℕ} {r : V} {K : SimpleGraph V}
    (sig : Signature (G:=G) A p w) (two : (∑ i:I,w i)=2) (out : r∉A)
    (edges : ∀ x∈A, ∀ y∈A, G.Adj x y → K.Adj x y)
    (cap : ∀ i,K.Adj r (p i)) : Closed K (insert r A) := by
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
        exact path_tile K (ex ▸ cap i) (edges x xA y yA (ex ▸ g)) ry
      · have px : p i≠x := fun e => xy (e.symm.trans ey)
        have g := (frag i).2.star x xi (Ne.symm px)
        obtain h := path_tile K (ey ▸ cap i) (edges y yA x xA (ey ▸ g)) rx
        have reorder : ({r,y,x}:Finset V)={r,x,y} := by
          ext z; simp only [mem_insert,mem_singleton]; tauto
        exact reorder ▸ h
    · have ex : p i=x := (pU i pi).resolve_right (fun eq =>
        disjoint_left.mp (sep i j same) (eq ▸ pi) yj)
      have ey : p j=y := (pU j pj).resolve_left (fun eq =>
        disjoint_left.mp (sep i j same) xi (eq ▸ pj))
      have h := path_tile K (ex ▸ (cap i).symm) (ey ▸ cap j) xy
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

#print axioms width_le_two
#print axioms opposite_at_shared_seam
#print axioms signature_of_partially_covered_cell
#print axioms signature_of_covered_cell
#print axioms export_two_caps
end KelmansCactus.NearPerfectCells
