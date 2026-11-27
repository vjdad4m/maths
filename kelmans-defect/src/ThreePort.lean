import Assemble

open Finset
namespace KelmansCactus.ThreePort
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {I : Type*} [Fintype I]

structure Seam (A : Finset V) (p q : I → V) : Prop where
  left : ∀ i, p i ∈ A
  right : ∀ i, q i ∉ A
  left_inj : Function.Injective p
  right_inj : Function.Injective q
  edge : ∀ a ∈ A, ∀ b ∉ A, G.Adj a b ↔ ∃ i, p i = a ∧ q i = b

structure AtPort (S : Finset V) (p : V) (F : Finset V) : Prop where
  inside : F ⊆ S
  includes : F.Nonempty → p ∈ F
  star : ∀ v ∈ F, v ≠ p → G.Adj p v

/-- Width zero leaves no open fragment. Width one leaves just the port.
Width two leaves the port and an adjacent vertex, for one crossing P3. -/
def Signature (S : Finset V) (p : I → V) (w : I → Nat) : Prop :=
  ∃ F : I → Finset V, (∀ i, (F i).card = w i ∧ AtPort (G:=G) S (p i) (F i)) ∧
    (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧
    ∃ P, Assemble.LocalPart G P (S \ univ.biUnion F)

/-- Two widths may both vanish; otherwise the opposite side must contribute
the complementary fraction of a three-vertex tile. -/
def Opposite (u v : Nat) : Prop := (u=0 ∧ v=0) ∨ (1≤u ∧ u≤2 ∧ 1≤v ∧ v≤2 ∧ u+v=3)

omit [Fintype V] [DecidableEq V] [Fintype I] in
private theorem no_many_cross {A : Finset V} {p q : I → V}
    (h : Seam (G:=G) A p q) {a b c : V} (ha : a ∈ A) (hb : b ∉ A) (hc : c ∉ A)
    (ab : G.Adj a b) (ac : G.Adj a c) : b = c := by
  obtain ⟨i,hi,bi⟩ := (h.edge a ha b hb).mp ab
  obtain ⟨j,hj,cj⟩ := (h.edge a ha c hc).mp ac
  have eq := h.left_inj (hi.trans hj.symm)
  subst j
  exact bi.symm.trans cj

omit [Fintype V] [DecidableEq V] [Fintype I] in
private theorem no_many_cross_rev {A : Finset V} {p q : I → V}
    (h : Seam (G:=G) A p q) {a b c : V} (ha : a ∉ A) (hb : b ∈ A) (hc : c ∈ A)
    (ab : G.Adj a b) (ac : G.Adj a c) : b = c := by
  obtain ⟨i,bi,hi⟩ := (h.edge b hb a ha).mp ab.symm
  obtain ⟨j,cj,hj⟩ := (h.edge c hc a ha).mp ac.symm
  have eq := h.right_inj (hi.trans hj.symm)
  subst j
  exact bi.symm.trans cj

omit [Fintype I] in
private theorem shape {A t : Finset V} {p q : I → V}
    (H : Seam (G:=G) A p q) (ht : KelmansStarter.IsTile G t) (mt : Mixed A t) :
    ∃ i, p i ∈ t ∧ q i ∈ t ∧
      AtPort (G:=G) A (p i) (t ∩ A) ∧ AtPort (G:=G) Aᶜ (q i) (t \ A) ∧
      ((t ∩ A).card = 1 ∨ (t \ A).card = 1) := by
  obtain ⟨o,ot,oa⟩ := ht.2
  obtain ⟨⟨a,at',aa⟩,⟨b,bt,ba⟩⟩ := mt
  have sd : t \ A ⊆ Aᶜ := fun x hx => mem_compl.mpr (mem_sdiff.mp hx).2
  by_cases cA : o ∈ A
  · have bo : b ≠ o := by rintro rfl; contradiction
    obtain ⟨i,ip,iq⟩ := (H.edge o cA b ba).mp (oa b bt bo)
    have singleton : t \ A = {b} := by
      ext v
      simp only [mem_sdiff,mem_singleton]
      constructor
      · rintro ⟨vt,na⟩
        exact no_many_cross H cA na ba (oa v vt (by rintro rfl; contradiction)) (oa b bt bo)
      · rintro rfl
        exact ⟨bt,ba⟩
    refine ⟨i,ip.symm ▸ ot,iq.symm ▸ bt,?_,?_,Or.inr ?_⟩
    · refine ⟨inter_subset_right,fun _ => mem_inter.mpr ⟨ip.symm ▸ ot,ip.symm ▸ cA⟩,?_⟩
      intro v hv ne
      rw [ip] at ne ⊢
      exact oa v (mem_inter.mp hv).1 ne
    · rw [iq,singleton]
      refine ⟨?_,fun _ => mem_singleton_self _,fun v hv ne => (ne (mem_singleton.mp hv)).elim⟩
      intro v hv
      obtain rfl := mem_singleton.mp hv
      exact mem_compl.mpr ba
    · rw [singleton,card_singleton]
  · have ao : a ≠ o := by rintro rfl; contradiction
    obtain ⟨i,ip,iq⟩ := (H.edge a aa o cA).mp (oa a at' ao).symm
    have singleton : t ∩ A = {a} := by
      ext v
      simp only [mem_inter,mem_singleton]
      constructor
      · rintro ⟨vt,va⟩
        exact no_many_cross_rev H cA va aa (oa v vt (by rintro rfl; contradiction)) (oa a at' ao)
      · rintro rfl
        exact ⟨at',aa⟩
    refine ⟨i,ip.symm ▸ at',iq.symm ▸ ot,?_,?_,Or.inl ?_⟩
    · rw [ip,singleton]
      refine ⟨?_,fun _ => mem_singleton_self _,fun v hv ne => (ne (mem_singleton.mp hv)).elim⟩
      intro v hv
      obtain rfl := mem_singleton.mp hv
      exact aa
    · refine ⟨sd,fun _ => mem_sdiff.mpr ⟨iq.symm ▸ ot,iq.symm ▸ cA⟩,?_⟩
      intro v hv ne
      rw [iq] at ne ⊢
      exact oa v (mem_sdiff.mp hv).1 ne
    · rw [singleton,card_singleton]

omit [Fintype V] [Fintype I] in
private theorem unique_index {A t : Finset V} {p q : I → V} {i j : I}
    (H : Seam (G:=G) A p q)
    (ip : p i ∈ t) (iq : q i ∈ t) (jp : p j ∈ t) (jq : q j ∈ t)
    (small : (t∩A).card = 1 ∨ (t\A).card = 1) : i=j := by
  rcases small with h | h
  · obtain ⟨x,ex⟩ := card_eq_one.mp h
    apply H.left_inj
    have hi : p i ∈ t∩A := mem_inter.mpr ⟨ip,H.left i⟩
    have hj : p j ∈ t∩A := mem_inter.mpr ⟨jp,H.left j⟩
    rw [ex] at hi hj
    exact (mem_singleton.mp hi).trans (mem_singleton.mp hj).symm
  · obtain ⟨x,ex⟩ := card_eq_one.mp h
    apply H.right_inj
    have hi : q i ∈ t\A := mem_sdiff.mpr ⟨iq,H.right i⟩
    have hj : q j ∈ t\A := mem_sdiff.mpr ⟨jq,H.right j⟩
    rw [ex] at hi hj
    exact (mem_singleton.mp hi).trans (mem_singleton.mp hj).symm

private theorem locals {P : Finset (Finset V)} (hf : Factor G P)
    (S : Finset V) (T : I → Finset V)
    (chosen : ∀ i, (T i).Nonempty → T i ∈ P ∧ Mixed S (T i))
    (exhaust : ∀ t ∈ P, Mixed S t → ∃ i, T i = t) :
    ∃ Q, Assemble.LocalPart G Q (S \ univ.biUnion (fun i => T i ∩ S)) := by
  let Q := P.filter (fun t => t ⊆ S)
  refine ⟨Q,⟨?_,?_,?_⟩⟩
  · intro t ht
    exact hf.tile t (mem_filter.mp ht).1
  · intro s hs t ht ne
    exact hf.disj s (mem_filter.mp hs).1 t (mem_filter.mp ht).1 ne
  · ext v
    constructor
    · intro hv
      obtain ⟨t,ht,tv⟩ := mem_biUnion.mp hv
      obtain ⟨hpt,hsub⟩ := mem_filter.mp ht
      refine mem_sdiff.mpr ⟨hsub tv,?_⟩
      intro hm
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp hm
      have hvi := (mem_inter.mp hi).1
      obtain ⟨hPi,hmix⟩ := chosen i ⟨v,hvi⟩
      have eq : t = T i := by
        by_contra ne
        exact disjoint_left.mp (hf.disj t hpt _ hPi ne) tv hvi
      obtain ⟨w,wt,wn⟩ := hmix.2
      exact wn (hsub (eq.symm ▸ wt))
    · intro hv
      obtain ⟨vS,vno⟩ := mem_sdiff.mp hv
      have hP : v ∈ P.biUnion id := hf.cover.symm ▸ mem_univ _
      obtain ⟨t,ht,tv⟩ := mem_biUnion.mp hP
      have hsub : t ⊆ S := by
        intro u ut
        by_contra un
        obtain ⟨i,hi⟩ := exhaust t ht ⟨⟨v,tv,vS⟩,⟨u,ut,un⟩⟩
        exact vno (mem_biUnion.mpr ⟨i,mem_univ _,mem_inter.mpr ⟨hi.symm ▸ tv,vS⟩⟩)
      exact mem_biUnion.mpr ⟨t,mem_filter.mpr ⟨ht,hsub⟩,tv⟩

private theorem mixed_compl {S t : Finset V} : Mixed S t ↔ Mixed Sᶜ t := by
  unfold Mixed
  simp only [mem_compl,not_not]
  exact and_comm

theorem signatures_from_fixed_factor {A : Finset V} {p q : I → V}
    (H : Seam (G:=G) A p q) {P : Finset (Finset V)} (hf : Factor G P) :
    ∃ s t : I → Nat, Signature (G:=G) A p s ∧ Signature (G:=G) Aᶜ q t ∧
      (∀ i, Opposite (s i) (t i)) ∧
      (∀ i, (∃ t ∈ P, p i ∈ t ∧ q i ∈ t) → s i ≠ 0) := by
  classical
  let uses (i : I) := ∃ t ∈ P, p i ∈ t ∧ q i ∈ t
  let T (i : I) := if h : uses i then Classical.choose h else ∅
  have Ttrue (i : I) (h : uses i) : T i ∈ P ∧ p i ∈ T i ∧ q i ∈ T i := by
    dsimp only [T]
    rw [dif_pos h]
    exact Classical.choose_spec h
  have Tfalse (i : I) (h : ¬ uses i) : T i = ∅ := by simp [T,h]
  have Tuse (i : I) (h : (T i).Nonempty) : uses i := by
    by_contra hn
    rw [Tfalse i hn] at h
    exact not_nonempty_empty h
  have Tmixed (i : I) (h : uses i) : Mixed A (T i) := by
    obtain ⟨_,hp,hq⟩ := Ttrue i h
    exact ⟨⟨p i,hp,H.left i⟩,⟨q i,hq,H.right i⟩⟩
  have Tadj (i : I) (h : uses i) :
      AtPort (G:=G) A (p i) (T i ∩ A) ∧
        AtPort (G:=G) Aᶜ (q i) (T i \ A) ∧
        ((T i∩A).card=1 ∨ (T i\A).card=1) := by
    obtain ⟨hP,hp,hq⟩ := Ttrue i h
    obtain ⟨j,jp,jq,a,b,s⟩ := shape H (hf.tile _ hP) (Tmixed i h)
    have he := unique_index H hp hq jp jq s
    subst j
    exact ⟨a,b,s⟩
  have Tout : ∀ r ∈ P, Mixed A r → ∃ i, T i = r := by
    intro r rp rm
    obtain ⟨i,ip,iq,_⟩ := shape H (hf.tile r rp) rm
    have hu : uses i := ⟨r,rp,ip,iq⟩
    obtain ⟨hP,hp,_⟩ := Ttrue i hu
    refine ⟨i,?_⟩
    by_contra ne
    exact disjoint_left.mp (hf.disj _ hP _ rp ne) hp ip
  have Tdis : ∀ i j, i ≠ j → Disjoint (T i) (T j) := by
    intro i j ne
    by_cases it : uses i
    · by_cases jt : uses j
      · obtain ⟨ip,pi,qi⟩ := Ttrue i it
        obtain ⟨jp,pj,qj⟩ := Ttrue j jt
        apply hf.disj _ ip _ jp
        intro he
        exact ne (unique_index H pi qi (he.symm ▸ pj) (he.symm ▸ qj) (Tadj i it).2.2)
      · simp [Tfalse j jt]
    · simp [Tfalse i it]
  let sl (i : I) := (T i ∩ A).card
  let sr (i : I) := (T i \ A).card
  refine ⟨sl,sr,?_,?_,?_,?_⟩
  · refine ⟨fun i => T i ∩ A,?_,?_,?_⟩
    · intro i
      refine ⟨rfl,?_⟩
      by_cases h : uses i
      · exact (Tadj i h).1
      · change AtPort (G:=G) A (p i) (T i ∩ A)
        rw [Tfalse i h,empty_inter]
        exact ⟨empty_subset _,fun e => False.elim (not_nonempty_empty e),by simp⟩
    · intro i j ne
      exact (Tdis i j ne).mono inter_subset_left inter_subset_left
    · exact locals hf A T (fun i h => ⟨(Ttrue i (Tuse i h)).1,Tmixed i (Tuse i h)⟩) Tout
  · have srEq (i : I) : T i \ A = T i ∩ Aᶜ := by
      ext v
      simp
    refine ⟨fun i => T i ∩ Aᶜ,?_,?_,?_⟩
    · intro i
      change (T i ∩ Aᶜ).card = sr i ∧ AtPort (G:=G) Aᶜ (q i) (T i ∩ Aᶜ)
      rw [← srEq]
      refine ⟨rfl,?_⟩
      by_cases h : uses i
      · exact (Tadj i h).2.1
      · rw [Tfalse i h,empty_sdiff]
        exact ⟨empty_subset _,fun e => False.elim (not_nonempty_empty e),by simp⟩
    · intro i j ne
      exact (Tdis i j ne).mono inter_subset_left inter_subset_left
    · exact locals hf Aᶜ T
        (fun i h => ⟨(Ttrue i (Tuse i h)).1,mixed_compl.mp (Tmixed i (Tuse i h))⟩)
        (fun t ht m => Tout t ht (mixed_compl.mpr m))
  · intro i
    by_cases h : uses i
    · right
      have cnt := card_sdiff_add_card_inter (T i) A
      have c3 := (hf.tile _ (Ttrue i h).1).1
      obtain ⟨_,_,m⟩ := Tadj i h
      dsimp [sl,sr]
      omega
    · left
      simp [sl,sr,Tfalse i h]

  · intro i h
    have hp := (Ttrue i h).2.1
    exact Nat.ne_of_gt (card_pos.mpr ⟨p i,mem_inter.mpr ⟨hp,H.left i⟩⟩)

private theorem signatures_from_factor {A : Finset V} {p q : I → V}
    (H : Seam (G:=G) A p q) (has : KelmansStarter.HasP3Factor G) :
    ∃ s t : I → Nat, Signature (G:=G) A p s ∧ Signature (G:=G) Aᶜ q t ∧
      ∀ i, Opposite (s i) (t i) := by
  obtain ⟨P,ht,hd,hc⟩ := has
  obtain ⟨s,t,hs,ht,op,_⟩ := signatures_from_fixed_factor H ⟨ht,hd,hc⟩
  exact ⟨s,t,hs,ht,op⟩

#print axioms signatures_from_fixed_factor
#print axioms signatures_from_factor

omit [Fintype V] in
theorem local_union {A B : Finset V} {P Q : Finset (Finset V)}
    (hP : Assemble.LocalPart G P A) (hQ : Assemble.LocalPart G Q B)
    (dis : Disjoint A B) : Assemble.LocalPart G (P∪Q) (A∪B) := by
  constructor
  · intro t ht
    rcases mem_union.mp ht with hp | hq
    · exact hP.tile _ hp
    · exact hQ.tile _ hq
  · intro s hs t ht ne
    rcases mem_union.mp hs with hp | hq <;> rcases mem_union.mp ht with hp' | hq'
    · exact hP.disj _ hp _ hp' ne
    · exact dis.mono (hP.tile_sub G hp) (hQ.tile_sub G hq')
    · exact dis.symm.mono (hQ.tile_sub G hq) (hP.tile_sub G hp')
    · exact hQ.disj _ hq _ hq' ne
  · rw [← hP.cover, ← hQ.cover]
    ext v
    simp only [mem_biUnion,mem_union]
    constructor
    · rintro ⟨s,hp,hs⟩
      exact hp.elim (fun h => Or.inl ⟨s,h,hs⟩) (fun h => Or.inr ⟨s,h,hs⟩)
    · rintro (⟨s,hp,hs⟩ | ⟨s,hq,hs⟩)
      · exact ⟨s,Or.inl hp,hs⟩
      · exact ⟨s,Or.inr hq,hs⟩

omit [Fintype V] in
theorem assemble_indexed {JType : Type*} (J : Finset JType) (D : JType → Finset V)
    (cellDis : (J : Set JType).PairwiseDisjoint D)
    (hlocal : ∀ i ∈ J, ∃ P, Assemble.LocalPart G P (D i)) :
    ∃ P, Assemble.LocalPart G P (J.biUnion D) := by
  classical
  induction J using Finset.induction_on with
  | empty => exact ⟨∅,⟨by simp,by simp,by simp⟩⟩
  | @insert i J ni ih =>
    obtain ⟨U,hU⟩ := hlocal i (mem_insert_self _ _)
    have inc : (J : Set JType) ⊆ (insert i J : Finset JType) :=
      fun _ hj => mem_insert_of_mem hj
    obtain ⟨W,hW⟩ := ih (cellDis.subset inc) (fun j hj => hlocal j (mem_insert_of_mem hj))
    have dd : Disjoint (D i) (J.biUnion D) := by
      apply disjoint_left.mpr
      intro v vi vw
      obtain ⟨j,hj,vj⟩ := mem_biUnion.mp vw
      have nij : i ≠ j := fun h => ni (h.symm ▸ hj)
      exact disjoint_left.mp (cellDis (mem_insert_self _ _) (mem_insert_of_mem hj) nij) vi vj
    exact ⟨U∪W,by simpa only [Finset.biUnion_insert] using local_union hU hW dd⟩

omit [Fintype V] in
theorem join_one_two {F K A B : Finset V} {p q : V}
    (hF : AtPort (G:=G) A p F) (hK : AtPort (G:=G) B q K)
    (f1 : F.card = 1) (k2 : K.card = 2) (dis : Disjoint F K) (pq : G.Adj p q) :
    KelmansStarter.IsTile G (F∪K) := by
  have pf := hF.includes (card_pos.mp (by omega))
  have qk := hK.includes (card_pos.mp (by omega))
  obtain ⟨u,hu⟩ := card_eq_one.mp f1
  have ep : F = {p} := by
    have e : p ∈ ({u} : Finset V) := hu ▸ pf
    rw [mem_singleton] at e
    simpa [e] using hu
  refine ⟨by rw [card_union_of_disjoint dis,f1,k2],q,mem_union_right _ qk,?_⟩
  intro v hv ne
  rcases mem_union.mp hv with h | h
  · rw [ep] at h
    obtain rfl := mem_singleton.mp h
    exact pq.symm
  · exact hK.star v h ne

omit [Fintype V] in
theorem join_ports {F K A B : Finset V} {p q : V}
    (hF : AtPort (G:=G) A p F) (hK : AtPort (G:=G) B q K)
    (c : Opposite F.card K.card) (dis : Disjoint F K) (pq : G.Adj p q) :
    F∪K = ∅ ∨ KelmansStarter.IsTile G (F∪K) := by
  rcases c with ⟨hf,hk⟩ | ⟨a,b,d,e,s⟩
  · left
    simp [card_eq_zero.mp hf,card_eq_zero.mp hk]
  · right
    by_cases h : F.card = 1
    · exact join_one_two hF hK h (by omega) dis pq
    · rw [union_comm]
      exact join_one_two hK hF (by omega) (by omega) dis.symm pq.symm

theorem signatures_to_factor {A : Finset V} {p q : I → V} {s t : I → ℕ}
    (links : ∀ i, G.Adj (p i) (q i))
    (hs : Signature (G:=G) A p s) (ht : Signature (G:=G) Aᶜ q t)
    (hmatch : ∀ i, Opposite (s i) (t i)) :
    KelmansStarter.HasP3Factor G := by
  classical
  obtain ⟨F,hF,dF,P,hP⟩ := hs
  obtain ⟨K,hK,dK,Q,hQ⟩ := ht
  let C (i : I) := F i ∪ K i
  let CF := univ.biUnion F
  let CK := univ.biUnion K
  have HF : CF ⊆ A := by
    intro v m
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp m
    exact (hF i).2.inside hi
  have HK : CK ⊆ Aᶜ := by
    intro v m
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp m
    exact (hK i).2.inside hi
  have comp : Disjoint A Aᶜ := disjoint_compl_right
  have c_dis : (↑(univ : Finset (I)) : Set (I)).PairwiseDisjoint C := by
    intro i hi j hj ne
    show Disjoint (F i ∪ K i) (F j ∪ K j)
    simp only [disjoint_union_left,disjoint_union_right]
    exact ⟨⟨dF i j ne,comp.symm.mono (hK i).2.inside (hF j).2.inside⟩,
      ⟨comp.mono (hF i).2.inside (hK j).2.inside,dK i j ne⟩⟩
  obtain ⟨U,hU⟩ := assemble_indexed univ C c_dis (by
    intro i _
    have o := hmatch i
    rw [← (hF i).1, ← (hK i).1] at o
    rcases join_ports (hF i).2 (hK i).2 o
      (comp.mono (hF i).2.inside (hK i).2.inside) (links i) with empty | tile
    · exact ⟨∅,by simpa [C,empty] using (show Assemble.LocalPart G (∅ : Finset (Finset V)) ∅ from
        ⟨by simp,by simp,by simp⟩)⟩
    · exact ⟨{C i},⟨by simpa using tile,by simp,by simp⟩⟩)
  have both : univ.biUnion C = CF ∪ CK := by
    ext v
    simp only [mem_biUnion,mem_union,mem_univ,true_and,C,CF,CK]
    exact exists_or
  rw [both] at hU
  have hPQ := local_union hP hQ (comp.mono sdiff_subset sdiff_subset)
  have hrest : Disjoint ((A\CF) ∪ (Aᶜ\CK)) (CF∪CK) := by
    simp only [disjoint_union_left,disjoint_union_right]
    exact ⟨⟨disjoint_sdiff_self_left,comp.symm.mono sdiff_subset HF⟩,
      ⟨comp.mono sdiff_subset HK,disjoint_sdiff_self_left⟩⟩
  have h := local_union hPQ hU hrest
  have full : ((A\CF) ∪ (Aᶜ\CK)) ∪ (CF∪CK) = univ := by
    apply eq_univ_of_forall
    intro v
    by_cases h1 : v ∈ CF
    · simp [h1]
    by_cases h2 : v ∈ CK
    · simp [h2]
    · simp [h1,h2,← or_assoc,em]
  exact ⟨_,h.tile,h.disj,h.cover.trans full⟩

omit [Fintype V] in
theorem width_congruence {S : Finset V} {p : I → V} {w : I → ℕ}
    (hs : Signature (G:=G) S p w) : (∑ i : I, w i) % 3 = S.card % 3 := by
  obtain ⟨F,hF,dF,P,hP⟩ := hs
  have covF : univ.biUnion F ⊆ S := by
    intro v vh
    obtain ⟨i,_,hv⟩ := mem_biUnion.mp vh
    exact (hF i).2.inside hv
  have d : (↑(univ : Finset (I)) : Set (I)).PairwiseDisjoint F := fun i _ j _ ne => dF i j ne
  have cardF : (univ.biUnion F).card = ∑ i : I, w i := by
    rw [card_biUnion d]
    exact Finset.sum_congr rfl fun i _ => (hF i).1
  have dP : (P : Set (Finset V)).PairwiseDisjoint id := fun s hs t ht ne => hP.disj _ hs _ ht ne
  have cardP : (S \ univ.biUnion F).card = P.card*3 := by
    rw [← hP.cover,card_biUnion dP]
    calc
      _ = ∑ x ∈ P, 3 := Finset.sum_congr rfl fun i ih => (hP.tile _ ih).1
      _ = _ := by simp
  have all := card_sdiff_add_card_eq_card covF
  omega

#print axioms width_congruence

/-- Exact signature theorem for any matching cut, including cubic 3-edge
sums and four-port joins. A separate tile may cross each used edge. No assumption of Helly-type consistency across signatures. -/
theorem factor_iff_signatures {A : Finset V} {p q : I → V} (H : Seam (G:=G) A p q) :
    KelmansStarter.HasP3Factor G ↔
      ∃ s t : I → Nat, Signature (G:=G) A p s ∧ Signature (G:=G) Aᶜ q t ∧
        ∀ i, Opposite (s i) (t i) := by
  constructor
  · exact signatures_from_factor H
  · rintro ⟨s,t,hs,ht,op⟩
    exact signatures_to_factor (fun i => (H.edge _ (H.left i) _ (H.right i)).mpr ⟨i,rfl,rfl⟩)
      hs ht op

#print axioms factor_iff_signatures
omit [Fintype I] in
/-- The exact geometry of a mixed tile is independent of whether
the rest of the ambient graph is fully packed. -/
theorem describe_mixed_tile {A t : Finset V} {p q : I → V}
    (H : Seam (G:=G) A p q) (ht : KelmansStarter.IsTile G t) (mt : Mixed A t) :
    ∃ i, p i ∈ t ∧ q i ∈ t ∧
      AtPort (G:=G) A (p i) (t ∩ A) ∧ AtPort (G:=G) Aᶜ (q i) (t \ A) ∧
      ((t ∩ A).card = 1 ∨ (t \ A).card = 1) :=
  shape H ht mt

omit [Fintype V] [Fintype I] in
theorem mixed_uses_only_one_slot {A t : Finset V} {p q : I → V} {i j : I}
    (H : Seam (G:=G) A p q)
    (ip : p i∈t) (iq : q i∈t) (jp : p j∈t) (jq : q j∈t)
    (small : (t∩A).card=1 ∨ (t\A).card=1) : i=j :=
  unique_index H ip iq jp jq small

end KelmansCactus.ThreePort
