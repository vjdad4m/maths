import PortSwitch

open Finset
namespace KelmansCactus.SpareChord

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

omit [Fintype V] in
/-- Any tile crossing an interior region contains an exterior boundary port. -/
theorem mixed_has_port {D W t : Finset V}
    (ex : ∀ u ∈ D, ∀ v ∉ D, G.Adj u v → v ∈ W)
    (tile : KelmansStarter.IsTile G t) (mix : Mixed D t) :
    ∃ w ∈ t, w ∈ W := by
  obtain ⟨⟨u,ut,ud⟩,⟨v,vt,vd⟩⟩ := mix
  obtain ⟨c,ct,center⟩ := tile.2
  by_cases cd : c ∈ D
  · exact ⟨v,vt,ex c cd v vd (center v vt (by rintro rfl; contradiction))⟩
  · exact ⟨c,ct,ex u ud c cd (center u ut (by rintro rfl; contradiction)).symm⟩

/-- Each gap's residue is paid for by exceptional tiles that already touch
the reserved ports. This inequality works for any number of ports or gap
shapes. Internal whole tiles cannot contribute to the residue. -/
theorem residue_le_exception {P E : Finset (Finset V)} {D W : Finset V}
    (hf : Factor G P) (hE : E ⊆ P)
    (ports : ∀ w ∈ W, ∃ t ∈ E, w ∈ t)
    (ex : ∀ u ∈ D, ∀ v ∉ D, G.Adj u v → v ∈ W) :
    D.card % 3 ≤ ∑ t ∈ E, (t ∩ D).card := by
  have hdvd : 3 ∣ ∑ t ∈ P \ E, (t ∩ D).card := by
    apply Finset.dvd_sum
    intro t ht
    obtain ⟨hp,hn⟩ := mem_sdiff.mp ht
    apply pure_dvd _ (hf.tile t hp).1
    intro mix
    obtain ⟨w,wt,ww⟩ := mixed_has_port G ex (hf.tile t hp) mix
    obtain ⟨s,se,ws⟩ := ports w ww
    have he : t = s := by
      by_contra ne
      exact disjoint_left.mp (hf.disj t hp s (hE se) ne) wt ws
    exact hn (he.symm ▸ se)
  have hs : (∑ t ∈ P \ E, (t ∩ D).card) + (∑ t ∈ E, (t ∩ D).card) = D.card := by
    rw [Finset.sum_sdiff hE,sum_inter hf D]
  omega

/-- Simultaneous gap budget. Across any disjoint family of cells whose
exits are protected by chosen boundary tiles, the sum of individual
remainders cannot exceed the total remaining capacity of those tiles.
The set R can contain original ports and any vertices already committed
outside the cells. No assumption that the cells lie in one cycle. -/
theorem all_gap_residue_budget {I : Type*} {J : Finset I} {D : I → Finset V}
    {P E : Finset (Finset V)} {W R : Finset V}
    (hf : Factor G P) (hE : E ⊆ P)
    (ports : ∀ w ∈ W, ∃ t ∈ E, w ∈ t)
    (cells : (J : Set I).PairwiseDisjoint D)
    (reserved : ∀ i ∈ J, Disjoint (D i) R)
    (ex : ∀ i ∈ J, ∀ u ∈ D i, ∀ v ∉ D i, G.Adj u v → v ∈ W) :
    (∑ i ∈ J, (D i).card % 3) ≤ ∑ t ∈ E, (t \ R).card := by
  classical
  calc
    _ ≤ ∑ i ∈ J, ∑ t ∈ E, (t ∩ D i).card := Finset.sum_le_sum (fun i hi =>
      residue_le_exception G hf hE ports (ex i hi))
    _ = ∑ t ∈ E, ∑ i ∈ J, (t ∩ D i).card := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro t _
      have dis : (J : Set I).PairwiseDisjoint (fun i => t ∩ D i) := by
        intro i hi j hj ne
        exact (cells hi hj ne).mono inter_subset_right inter_subset_right
      rw [← card_biUnion dis]
      apply card_le_card
      intro v hv
      obtain ⟨i,hi,hm⟩ := mem_biUnion.mp hv
      obtain ⟨ht,hd⟩ := mem_inter.mp hm
      exact mem_sdiff.mpr ⟨ht,fun h => disjoint_left.mp (reserved i hi) hd h⟩

#print axioms all_gap_residue_budget

/-- One arbitrary port tile + one protected residue-two port service all
gaps that have no other outside neighbors. At most one vertex can spill
into the gap system if the first tile also meets one disjoint outer set. -/
theorem paired_gap_budget {P : Finset (Finset V)} {D₁ D₂ B t₁ t₂ : Finset V} {a x y : V}
    (hf : Factor G P) (ht₁ : t₁ ∈ P) (ht₂ : t₂ ∈ P)
    (ha : a ∈ t₁) (hx : x ∈ t₁) (hy : y ∈ t₂) (ne : a ≠ x)
    (t₂sub : t₂ ⊆ insert y B)
    (nonxa : x ∉ D₁ ∧ x ∉ D₂) (nonya : y ∉ D₁ ∧ y ∉ D₂)
    (nona : a ∉ D₁ ∧ a ∉ D₂)
    (dis₁ : Disjoint D₁ B) (dis₂ : Disjoint D₂ B) (dis : Disjoint D₁ D₂)
    (ex₁ : ∀ u ∈ D₁, ∀ v ∉ D₁, G.Adj u v → v = x ∨ v = y)
    (ex₂ : ∀ u ∈ D₂, ∀ v ∉ D₂, G.Adj u v → v = x ∨ v = y) :
    D₁.card % 3 + D₂.card % 3 ≤ 1 := by
  let E : Finset (Finset V) := {t₁,t₂}
  have hE : E ⊆ P := by
    intro t ht
    simp only [E,mem_insert,mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact ht₁
    · exact ht₂
  have ports : ∀ w ∈ ({x,y} : Finset V), ∃ t ∈ E, w ∈ t := by
    intro w hw
    simp only [mem_insert,mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact ⟨t₁,by simp [E],hx⟩
    · exact ⟨t₂,by simp [E],hy⟩
  have go {D : Finset V}
      (dh : Disjoint D B) (yn : y ∉ D)
      (ex : ∀ u ∈ D, ∀ v ∉ D, G.Adj u v → v = x ∨ v = y) :
      D.card % 3 ≤ (t₁ ∩ D).card := by
    have empty : t₂ ∩ D = ∅ := by
      apply eq_empty_iff_forall_not_mem.mpr
      intro v hv
      obtain ⟨vt,vd⟩ := mem_inter.mp hv
      rcases mem_insert.mp (t₂sub vt) with rfl | vb
      · exact yn vd
      · exact disjoint_left.mp dh vd vb
    have hres := residue_le_exception G hf hE ports
      (fun u hu v hv hadj => mem_insert.mpr
        ((ex u hu v hv hadj).imp_right mem_singleton.mpr))
    by_cases eq : t₁ = t₂
    · simpa [E,eq,empty] using hres
    · simpa [E,Finset.sum_insert,eq,empty] using hres
  have h₁ := go dis₁ nonya.1 ex₁
  have h₂ := go dis₂ nonya.2 ex₂
  let U := t₁ ∩ (D₁ ∪ D₂)
  have hUd : Disjoint U ({a,x} : Finset V) := by
    apply disjoint_left.mpr
    intro u hu hor
    have hd := mem_union.mp (mem_inter.mp hu).2
    simp only [mem_insert,mem_singleton] at hor
    rcases hor with rfl | rfl
    · exact hd.elim nona.1 nona.2
    · exact hd.elim nonxa.1 nonxa.2
  have sub : U ∪ ({a,x} : Finset V) ⊆ t₁ := by
    intro v hv
    rcases mem_union.mp hv with hu | he
    · exact (mem_inter.mp hu).1
    · simp only [mem_insert,mem_singleton] at he
      rcases he with rfl | rfl
      · exact ha
      · exact hx
  have hh := card_le_card sub
  rw [card_union_of_disjoint hUd] at hh
  simp [ne,(hf.tile _ ht₁).1] at hh
  have UU : U = (t₁ ∩ D₁) ∪ (t₁ ∩ D₂) := by
    ext v
    simp [U,and_or_left]
  have DD : Disjoint (t₁ ∩ D₁) (t₁ ∩ D₂) := dis.mono inter_subset_right inter_subset_right
  rw [UU,card_union_of_disjoint DD] at hh
  omega

private theorem protected_second {P : Finset (Finset V)} {B : Finset V} {b y : V}
    (hf : Factor G P) (hb : OnlyExit (G:=G) B b y) (ny : y ∉ B) (rb : B.card % 3 = 2) :
    ∃ t ∈ P, y ∈ t ∧ t ⊆ insert y B := by
  obtain ⟨t,ht,hm⟩ := (bridge_crossing_iff hb hf).mpr (by omega : B.card % 3 ≠ 0)
  have m := bridge_residue hb hf ht hm
  have d := (hf.tile t ht).1
  have h := card_sdiff_add_card_inter t B
  have hcount : (t \ B).card = 1 := by omega
  have hy := (ports_mem hb (hf.tile t ht) hm).2
  have sub : ({y} : Finset V) ⊆ t \ B := by
    intro v hv
    obtain rfl := mem_singleton.mp hv
    exact mem_sdiff.mpr ⟨hy,ny⟩
  have eq := eq_of_subset_of_card_le sub (by rw [hcount,card_singleton] : (t \ B).card ≤ ({y} : Finset V).card)
  refine ⟨t,ht,hy,?_⟩
  intro v hv
  by_cases vb : v ∈ B
  · exact mem_insert_of_mem vb
  · have hu : v ∈ t \ B := mem_sdiff.mpr ⟨hv,vb⟩
    rw [← eq] at hu
    obtain rfl := mem_singleton.mp hu
    exact mem_insert_self _ _

omit [Fintype V] in
private theorem fin_disj {A B : List V} (h : A.Disjoint B) :
    Disjoint A.toFinset B.toFinset :=
  disjoint_left.mpr fun _ ha hb => h (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb)

/-- The width-two port borrows the first vertex of A, leaving two divisible
paths on the interior of the middle cycle. -/
theorem mixed_borrow {a b x y : V} {L R A B : List V}
    (hl : (L++[a]).Chain' G.Adj) (hr : (b::R).Chain' G.Adj)
    (hA : (x::A).Chain' G.Adj) (hB : B.Chain' G.Adj)
    (ha : G.Adj a x) (hb : G.Adj y b)
    (rL : L.length % 3 = 0) (rR : R.length % 3 = 1)
    (rA : A.length % 3 = 1) (rB : B.length % 3 = 0)
    (len : L.length + R.length + A.length + B.length + 4 = Fintype.card V)
    (cov : ∀ v : V, v ∈ L ∨ v = a ∨ v ∈ R ∨ v = b ∨ v = x ∨ v = y ∨ v ∈ A ∨ v ∈ B) :
    KelmansStarter.HasP3Factor G := by
  cases A with
  | nil => simp at rA
  | cons u A =>
    have left : (L ++ [a,x,u]).Chain' G.Adj :=
      List.chain'_append_cons_cons.mpr ⟨hl,ha,(List.chain'_singleton u).cons hA.rel_head⟩
    have right : (y::b::R).Chain' G.Adj := hr.cons hb
    apply PortSwitch.factor_chains G [L++[a,x,u],y::b::R,A,B]
    · simp only [List.flatten_cons,List.flatten_nil,List.append_nil,List.length_append,
        List.length_cons,List.length_nil]
      simp only [List.length_cons] at len
      omega
    · intro v
      have hv := cov v
      simp only [List.flatten_cons,List.flatten_nil,List.append_nil,List.mem_append,List.mem_cons,
        List.not_mem_nil,or_false] at hv ⊢
      tauto
    · intro C hC
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hC
      rcases hC with rfl | rfl | rfl | rfl
      exacts [left,right,hA.tail.tail,hB]
    · intro C hC
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hC
      rcases hC with rfl | rfl | rfl | rfl
      · simp; omega
      · simp; omega
      · simp only [List.length_cons] at rA
        omega
      · exact rB

/-- Exact 1--0--2 chain criterion. L++[a] is the width-1 outer block,
b::R is the width-2 outer block, X and Y are the two open arcs of the
central cycle, each oriented away from x. For the three-cycle subgraph
with only these two bridges, the port residues decide factorability. -/
theorem factor_mixed_iff {a b x y : V} {L R X Y : List V}
    (hl : (L++[a]).Chain' G.Adj) (hr : (b::R).Chain' G.Adj)
    (hX : (x::X).Chain' G.Adj) (hY : (x::Y).Chain' G.Adj)
    (ha : G.Adj a x) (hb : G.Adj y b)
    (rL : L.length % 3 = 0) (rR : R.length % 3 = 1)
    (rM : (X.length+Y.length+2)%3 = 0)
    (len : L.length + R.length + X.length + Y.length + 4 = Fintype.card V)
    (cov : ∀ v : V, v ∈ L ∨ v = a ∨ v ∈ R ∨ v = b ∨ v = x ∨ v = y ∨ v ∈ X ∨ v ∈ Y)
    (exL : OnlyExit (G:=G) (L++[a]).toFinset a x)
    (exR : OnlyExit (G:=G) (b::R).toFinset b y)
    (exX : ∀ u ∈ X.toFinset, ∀ v ∉ X.toFinset, G.Adj u v → v = x ∨ v = y)
    (exY : ∀ u ∈ Y.toFinset, ∀ v ∉ Y.toFinset, G.Adj u v → v = x ∨ v = y) :
    KelmansStarter.HasP3Factor G ↔ X.length % 3 ≠ 2 := by
  constructor
  · rintro ⟨P,hP,hPd,hPc⟩
    let Ps : List (List V) := [L++[a],b::R,[x,y],X,Y]
    have full : Ps.flatten.toFinset = univ := by
      ext v
      have hv := cov v
      simp only [Ps,List.flatten_cons,List.flatten_nil,List.append_nil,
        List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,mem_univ,iff_true]
      tauto
    have plen : Ps.flatten.length = Fintype.card V := by
      simp only [Ps,List.flatten_cons,List.flatten_nil,List.append_nil,
        List.length_append,List.length_cons,List.length_nil]
      omega
    have cardeq : Ps.flatten.toFinset.card = Ps.flatten.length := by rw [full,card_univ,plen]
    have hnd : Ps.flatten.Nodup :=
      (Multiset.toFinset_card_eq_card_iff_nodup (m := (↑Ps.flatten : Multiset V))).mp cardeq
    obtain ⟨hnd,hdis⟩ := List.nodup_flatten.mp hnd
    change List.Pairwise List.Disjoint [L++[a],b::R,[x,y],X,Y] at hdis
    obtain ⟨dL,hD⟩ := List.pairwise_cons.mp hdis
    obtain ⟨dR,hD⟩ := List.pairwise_cons.mp hD
    obtain ⟨dp,hD⟩ := List.pairwise_cons.mp hD
    obtain ⟨dx,_⟩ := List.pairwise_cons.mp hD
    have nx : x ∉ X.toFinset ∧ x ∉ Y.toFinset :=
      ⟨fun h => dp X (by simp) (by simp) (List.mem_toFinset.mp h),
       fun h => dp Y (by simp) (by simp) (List.mem_toFinset.mp h)⟩
    have ny : y ∉ X.toFinset ∧ y ∉ Y.toFinset :=
      ⟨fun h => dp X (by simp) (by simp) (List.mem_toFinset.mp h),
       fun h => dp Y (by simp) (by simp) (List.mem_toFinset.mp h)⟩
    have na : a ∉ X.toFinset ∧ a ∉ Y.toFinset :=
      ⟨fun h => dL X (by simp) (by simp) (List.mem_toFinset.mp h),
       fun h => dL Y (by simp) (by simp) (List.mem_toFinset.mp h)⟩
    have yy : y ∉ (b::R).toFinset :=
      fun h => dR [x,y] (by simp) (List.mem_toFinset.mp h) (by simp)
    have LL : (L++[a]).toFinset.card % 3 = 1 := by
      rw [List.toFinset_card_of_nodup (hnd _ (by simp [Ps]))]
      simpa using (show (L.length+1)%3 = 1 by omega)
    have RR : (b::R).toFinset.card % 3 = 2 := by
      rw [List.toFinset_card_of_nodup (hnd _ (by simp [Ps]))]
      change (R.length+1)%3 = 2
      omega
    have hf : Factor G P := ⟨hP,hPd,hPc⟩
    obtain ⟨t,ht,mt⟩ := (bridge_crossing_iff exL hf).mpr (by omega : (L++[a]).toFinset.card%3 ≠ 0)
    obtain ⟨hat,xt⟩ := ports_mem exL (hf.tile t ht) mt
    obtain ⟨s,hs,ys,sub⟩ := protected_second G hf exR yy RR
    have gap := paired_gap_budget G hf ht hs hat xt ys ha.ne sub nx ny na
      (fin_disj (dR X (by simp))).symm (fin_disj (dR Y (by simp))).symm
      (fin_disj (dx Y (by simp))) exX exY
    rw [List.toFinset_card_of_nodup (hnd X (by simp [Ps])),
      List.toFinset_card_of_nodup (hnd Y (by simp [Ps]))] at gap
    omega
  · intro modX
    by_cases zeroX : X.length % 3 = 0
    · exact mixed_borrow G (A:=Y) (B:=X) hl hr hY hX.tail ha hb rL rR (by omega) zeroX (by omega) (by
        intro v
        have hv := cov v
        tauto)
    · exact mixed_borrow G (A:=X) (B:=Y) hl hr hX hY.tail ha hb rL rR (by omega) (by omega) len cov

/-- Mixed residue chain with either nonzero cycle at its center. Only
the link between the residue-one and residue-two cycles is needed; the
residue-zero block tiles on its own, wherever it is attached. -/
theorem pair_one_two_and_zero {a b : V} {L R C : List V}
    (hl : (L++[a]).Chain' G.Adj) (hr : (b::R).Chain' G.Adj)
    (hc : C.Chain' G.Adj) (link : G.Adj a b)
    (rL : L.length % 3 = 0) (rR : R.length % 3 = 1) (rC : C.length % 3 = 0)
    (len : L.length + R.length + C.length + 2 = Fintype.card V)
    (cov : ∀ v : V, v ∈ L ∨ v = a ∨ v = b ∨ v ∈ R ∨ v ∈ C) :
    KelmansStarter.HasP3Factor G := by
  have first : (L++a::b::R).Chain' G.Adj :=
    List.chain'_append_cons_cons.mpr ⟨hl,link,hr⟩
  apply PortSwitch.factor_chains G [L++a::b::R,C]
  · simp only [List.flatten_cons,List.flatten_nil,List.append_nil,List.length_append,
      List.length_cons]
    omega
  · intro v
    have hv := cov v
    simp only [List.flatten_cons,List.flatten_nil,List.append_nil,List.mem_append,List.mem_cons]
    tauto
  · intro P hP
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hP
    rcases hP with rfl | rfl
    exacts [first,hc]
  · intro P hP
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hP
    rcases hP with rfl | rfl
    · simp; omega
    · exact rC

#print axioms pair_one_two_and_zero

set_option maxHeartbeats 1500000 in
/-- A matching chord repairs the 1--0--2 configuration even if every
bridge choice has bad port distances. The first arc is u :: (A₁ ++ s :: A₂);
the second is B₁ ++ t :: w :: B₂, with s adjacent to either t or w.
Here u is borrowed by the x port, and s together with the domino t,w
forms the only chord tile. The four listed gap paths tile independently.

Numbering each arc from the x end by 1,2,...: s is position 2 mod 3
of the arc from which u is borrowed; the opposite endpoint belongs
to positions 1 or 2 mod 3 on the other arc. -/
theorem repair_by_chord {a b x y u s t w : V} {L R A₁ A₂ B₁ B₂ : List V}
    (hl : (L++[a]).Chain' G.Adj) (hr : (b::R).Chain' G.Adj)
    (hA : (x :: u :: (A₁ ++ s :: A₂)).Chain' G.Adj)
    (hB : (B₁ ++ t :: w :: B₂).Chain' G.Adj)
    (ha : G.Adj a x) (hb : G.Adj y b) (chord : G.Adj s t ∨ G.Adj s w)
    (rL : L.length % 3 = 0) (rR : R.length % 3 = 1)
    (rA₁ : A₁.length % 3 = 0) (rA₂ : A₂.length % 3 = 0)
    (rB₁ : B₁.length % 3 = 0) (rB₂ : B₂.length % 3 = 0)
    (len : L.length + R.length + A₁.length + A₂.length + B₁.length + B₂.length + 8 =
      Fintype.card V)
    (cov : ∀ v : V, v ∈ L ∨ v = a ∨ v ∈ R ∨ v = b ∨ v = x ∨ v = y ∨ v = u ∨
      v ∈ A₁ ∨ v = s ∨ v ∈ A₂ ∨ v ∈ B₁ ∨ v = t ∨ v = w ∨ v ∈ B₂) :
    KelmansStarter.HasP3Factor G := by
  have left : (L ++ [a,x,u]).Chain' G.Adj :=
    List.chain'_append_cons_cons.mpr ⟨hl,ha,(List.chain'_singleton u).cons hA.rel_head⟩
  have right : (y::b::R).Chain' G.Adj := hr.cons hb
  have hAd : (A₁ ++ s :: A₂).Chain' G.Adj := hA.tail.tail
  have hB₁ := hB.left_of_append
  have hB₂ := hB.right_of_append.tail.tail
  have tw : G.Adj t w := (List.chain'_append_cons_cons.mp hB).2.1
  classical
  let T := if G.Adj s t then [s,t,w] else [s,w,t]
  classical
  have hT : T.Chain' G.Adj := by
    dsimp [T]
    split
    · rename_i e
      exact ((List.chain'_singleton w).cons tw).cons e
    · rename_i ne
      exact ((List.chain'_singleton t).cons tw.symm).cons (chord.resolve_left ne)
  have tl : T.length = 3 := by simp [T]; split <;> rfl
  have tm (v : V) : v ∈ T ↔ v = s ∨ v = t ∨ v = w := by
    by_cases h : G.Adj s t <;> simp [T,h,or_comm,or_left_comm]
  apply PortSwitch.factor_chains G [L++[a,x,u],y::b::R,A₁,A₂,B₁,B₂,T]
  · simp only [List.flatten_cons,List.flatten_nil,List.append_nil,List.length_append,
      List.length_cons,List.length_nil,tl]
    omega
  · intro v
    have hv := cov v
    simp only [List.flatten_cons,List.flatten_nil,List.append_nil,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false,tm]
    tauto
  · intro C hC
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [left,right,hAd.left_of_append,hAd.right_of_append.tail,hB₁,hB₂,hT]
  · intro C hC
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp; omega
    · simp; omega
    · exact rA₁
    · exact rA₂
    · exact rB₁
    · exact rB₂
    · rw [tl]

#print axioms factor_mixed_iff
#print axioms repair_by_chord
#print axioms residue_le_exception
#print axioms paired_gap_budget
end KelmansCactus.SpareChord
