import PathSlides
import Mathlib.Logic.Relation

open Finset
namespace KelmansCactus.ContactSlides

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
open PathSlides

/-- Every vertex of an actual tile has a neighbor in it. -/
theorem tile_neighbor {t : Finset V} (ht : KelmansStarter.IsTile G t)
    {v : V} (hv : v ∈ t) : ∃ w ∈ t, G.Adj v w := by
  obtain ⟨card,c,hc,star⟩ := ht
  by_cases eq : v=c
  · subst v
    have r : (t.erase c).Nonempty := card_pos.mp (by rw [card_erase_of_mem hc,card]; decide)
    obtain ⟨w,hw⟩ := r
    exact ⟨w,mem_of_mem_erase hw,star w (mem_of_mem_erase hw) (ne_of_mem_erase hw)⟩
  · exact ⟨c,hc,(star v hv eq).symm⟩

omit [DecidableEq V] in
private theorem noLoop (G : SimpleGraph V) {a b : V} (e : G.Adj a b) : a ≠ b :=
  G.ne_of_adj e

theorem path_tile (G : SimpleGraph V) {a b c : V} (ab : G.Adj a b) (bc : G.Adj b c)
    (ac : a ≠ c) : KelmansStarter.IsTile G ({a,b,c}:Finset V) := by
  refine ⟨by simp [noLoop G ab,noLoop G bc,ac],b,by simp,?_⟩
  intro u hu ne
  simp only [mem_insert,mem_singleton] at hu
  rcases hu with rfl | rfl | rfl
  · exact ab.symm
  · exact (ne rfl).elim
  · exact bc

/-- With an edge between the two kept vertices, exactly one contact suffices. -/
theorem contact_edge_iff {h a b : V} (ha : h ≠ a) (hb : h ≠ b) (ab : G.Adj a b) :
    KelmansStarter.IsTile G ({h,a,b}:Finset V) ↔ G.Adj h a ∨ G.Adj h b := by
  constructor
  · intro H
    have N := tile_neighbor H (show h ∈ ({h,a,b}:Finset V) from by simp)
    obtain ⟨w,hw,he⟩ := N
    simp only [mem_insert,mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact (G.irrefl he).elim
    · exact Or.inl he
    · exact Or.inr he
  · rintro (a'|b')
    · exact path_tile G a' ab hb
    · have t := path_tile G b' ab.symm ha
      convert t using 1
      ext x
      simp [or_comm,or_left_comm]

/-- With no edge between the two kept vertices, both contacts are necessary.
In particular a triangle-free old tile cannot free its center to an outside
vertex unless the new hole and old hole have both old leaves as neighbors. -/
theorem contact_nonedge_iff {h a b : V} (ha : h ≠ a) (hb : h ≠ b) (ab : a ≠ b)
    (no : ¬G.Adj a b) :
    KelmansStarter.IsTile G ({h,a,b}:Finset V) ↔ G.Adj h a ∧ G.Adj h b := by
  constructor
  · intro H
    obtain ⟨_,c,hc,star⟩ := H
    simp only [mem_insert,mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨star a (by simp) ha.symm,star b (by simp) hb.symm⟩
    · exact (no (star b (by simp) ab.symm)).elim
    · exact (no (star a (by simp) ab).symm).elim
  · rintro ⟨e,f⟩
    have t := path_tile G e.symm f ab
    convert t using 1
    ext x
    simp [or_comm,or_left_comm]

theorem PackIn.restrict {D : Finset V} {P Q : Parts V} (h : PackIn G D P) (sub : Q ⊆ P) :
    PackIn G D Q :=
  ⟨⟨fun t ht => h.part.tile _ (sub ht),
    fun s hs t ht ne => h.part.disj _ (sub hs) _ (sub ht) ne,rfl⟩,
   fun v hv => by
     obtain ⟨t,ht,tv⟩ := mem_biUnion.mp hv
     exact h.inside (mem_biUnion.mpr ⟨t,sub ht,tv⟩)⟩

/-- Insert a valid tile in a vacancy without changing the frame. -/
theorem PackIn.add {D : Finset V} {P : Parts V} (h : PackIn G D P) {t : Finset V}
    (tile : KelmansStarter.IsTile G t) (board : t ⊆ D)
    (free : Disjoint t (P.biUnion id)) : PackIn G D (insert t P) := by
  refine ⟨⟨?_,?_,rfl⟩,?_⟩
  · intro u hu
    rcases mem_insert.mp hu with rfl|hu
    · exact tile
    · exact h.part.tile _ hu
  · intro s hs u hu ne
    rcases mem_insert.mp hs with es|ps
    · rcases mem_insert.mp hu with eu|pu
      · exact (ne (es.trans eu.symm)).elim
      · rw [es]
        exact free.mono_right (Assemble.tile_sub_union pu)
    · rcases mem_insert.mp hu with eu|pu
      · rw [eu]
        exact free.symm.mono_left (Assemble.tile_sub_union ps)
      · exact h.part.disj _ ps _ pu ne
  · intro v hv
    obtain ⟨u,hu,vu⟩ := mem_biUnion.mp hv
    rcases mem_insert.mp hu with rfl|hu
    · exact board vu
    · exact h.inside (Assemble.tile_sub_union hu vu)

theorem not_in_frame {t : Finset V} {P : Parts V} (tile : KelmansStarter.IsTile G t)
    (free : Disjoint t (P.biUnion id)) : t ∉ P := by
  intro ht
  have np : t.Nonempty := card_pos.mp (by rw [tile.1]; decide)
  obtain ⟨v,vt⟩ := np
  exact disjoint_left.mp free vt (Assemble.tile_sub_union ht vt)

/-- A one-hole swap in the physical model. -/
structure MoveOne (G : SimpleGraph V) (D : Finset V) (P Q : Parts V) : Prop where
  start : PackIn G D P
  stop : PackIn G D Q
  one : ∃ K a b, a∉K ∧ b∉K ∧ (b\a).card=1 ∧ P=insert a K ∧ Q=insert b K

theorem MoveOne.slide {D : Finset V} {P Q : Parts V} (h : MoveOne G D P Q) :
    Slide G D P Q := by
  refine ⟨h.start,h.stop,?_⟩
  obtain ⟨K,a,b,ha,hb,diff,ea,eb⟩ := h.one
  have ne : a ≠ b := by intro eq; subst b; simp at diff
  exact ⟨K,a,b,ha,hb,ne,ea,eb⟩

inductive OneMoves (G : SimpleGraph V) (D : Finset V) :
    ℕ → Parts V → Parts V → Prop
  | nil (P) (ok : PackIn G D P) : OneMoves G D 0 P P
  | cons {n P Q R} : MoveOne G D P Q → OneMoves G D n Q R → OneMoves G D (n+1) P R

theorem OneMoves.slides {D : Finset V} {n : ℕ} {P Q : Parts V} (h : OneMoves G D n P Q) :
    Slides G D n P Q := by
  induction h with
  | nil _ ok => exact Slides.nil _ ok
  | cons step _ ih => exact Slides.cons step.slide ih

def CanFinish (G : SimpleGraph V) (D : Finset V) (P : Parts V) : Prop :=
  KelmansStarter.IsTile G (D \ P.biUnion id)

private theorem cover_insert (a : Finset V) (K : Parts V) :
    (insert a K).biUnion id = a ∪ K.biUnion id := by
  rw [←single_union,union_cover]
  simp

private theorem free_of_pack {D : Finset V} {K : Parts V} {a : Finset V}
    (h : PackIn G D (insert a K)) (ha : a∉K) : Disjoint a (K.biUnion id) := by
  apply disjoint_left.mpr
  intro x ax hx
  obtain ⟨t,ht,xt⟩ := mem_biUnion.mp hx
  exact disjoint_left.mp (h.part.disj a (mem_insert_self _ _) t
    (mem_insert_of_mem ht) (by rintro rfl; exact ha ht)) ax xt

/-- The new tile replaces exactly one old vertex by the arriving hole,
and the new vacancy set replaces exactly that hole by the released vertex. -/
theorem swap {D : Finset V} {P : Parts V} {t : Finset V} {h q : V}
    (start : PackIn G D P) (picked : t∈P) (hole : h∈D \ P.biUnion id) (leave : q∈t)
    (next : KelmansStarter.IsTile G (insert h (t.erase q))) :
    let Q := insert (insert h (t.erase q)) (P.erase t)
    MoveOne G D P Q ∧ (D \ Q.biUnion id) = insert q ((D \ P.biUnion id).erase h) := by
  let K := P.erase t
  let u := insert h (t.erase q)
  let Q := insert u K
  change MoveOne G D P Q ∧ D \ Q.biUnion id = insert q ((D \ P.biUnion id).erase h)
  have eqP : insert t K = P := insert_erase picked
  have splitP : P.biUnion id = t ∪ K.biUnion id := by rw [←cover_insert,eqP]
  have hD := (mem_sdiff.mp hole).1
  have hp := (mem_sdiff.mp hole).2
  have ht : h∉t := fun ht => hp (Assemble.tile_sub_union picked ht)
  have hk : h∉K.biUnion id := fun hk => hp (splitP.symm ▸ mem_union_right _ hk)
  have okP : PackIn G D (insert t K) := eqP.symm ▸ start
  have tk : t∉K := not_mem_erase _ _
  have sep := free_of_pack okP tk
  have uk : Disjoint u (K.biUnion id) := by
    apply disjoint_left.mpr
    intro x xu xK
    rcases mem_insert.mp xu with rfl|xu
    · exact hk xK
    · exact disjoint_left.mp sep (mem_of_mem_erase xu) xK
  have uD : u⊆D := by
    intro x xu
    rcases mem_insert.mp xu with rfl|xu
    · exact hD
    · exact start.inside (Assemble.tile_sub_union picked (mem_of_mem_erase xu))
  have frame : PackIn G D K := PackIn.restrict start (erase_subset _ _)
  have goodQ : PackIn G D Q := PackIn.add frame next uD uk
  have udiff : u\t={h} := by
    ext x
    simp only [u,mem_sdiff,mem_insert,mem_erase,mem_singleton]
    constructor
    · rintro ⟨e,n⟩
      exact e.elim id (fun hn => (n hn.2).elim)
    · rintro rfl
      exact ⟨Or.inl rfl,ht⟩
  refine ⟨⟨start,goodQ,K,t,u,tk,not_in_frame next uk,by simp [udiff],eqP.symm,rfl⟩,?_⟩
  have qD := start.inside (Assemble.tile_sub_union picked leave)
  have qK := fun qK => disjoint_left.mp sep leave qK
  have qh : q ≠ h := fun e => ht (e ▸ leave)
  ext x
  change x∈D \ (insert u K).biUnion id ↔ x ∈ insert q ((D \ P.biUnion id).erase h)
  rw [cover_insert,splitP]
  simp only [u,mem_sdiff,mem_union,mem_insert,mem_erase]
  by_cases xq : x=q
  · subst x
    have qNo : ∀ t∈K, q∉t := fun t tk qt => qK (mem_biUnion.mpr ⟨t,tk,qt⟩)
    simp [qD,qh]
    exact qNo
  · by_cases xh : x=h
    · subst x
      simp [xq]
    · simp only [xq,xh,false_or,not_false_eq_true,true_and]
      tauto

/-- Conversely, every one-hole neutral move has the contact description.
Thus a graph on complete packing states using these arcs is exact. -/
theorem MoveOne.exact_contact {D : Finset V} {P Q : Parts V} (m : MoveOne G D P Q) :
    ∃ t ∈ P, ∃ h ∈ D \ P.biUnion id, ∃ q ∈ t,
      KelmansStarter.IsTile G (insert h (t.erase q)) ∧
      Q = insert (insert h (t.erase q)) (P.erase t) ∧
      (D \ Q.biUnion id) = insert q ((D \ P.biUnion id).erase h) := by
  obtain ⟨K,t,u,ht,hu,one,rfl,rfl⟩ := m.one
  have tT := m.start.part.tile t (mem_insert_self _ _)
  have uT := m.stop.part.tile u (mem_insert_self _ _)
  have countT := tT.1
  have countU := uT.1
  have sumT := card_sdiff_add_card_inter t u
  have sumU := card_sdiff_add_card_inter u t
  rw [inter_comm u t] at sumU
  have other : (t\u).card=1 := by omega
  obtain ⟨h,hs⟩ := card_eq_one.mp one
  obtain ⟨q,qs⟩ := card_eq_one.mp other
  have hm : h∈u\t := hs.symm ▸ mem_singleton_self h
  have qm : q∈t\u := qs.symm ▸ mem_singleton_self q
  have ht' := (mem_sdiff.mp hm).2
  have qT := (mem_sdiff.mp qm).1
  have qU := (mem_sdiff.mp qm).2
  have hU := (mem_sdiff.mp hm).1
  have hK : h∉K.biUnion id := fun hk => disjoint_left.mp (free_of_pack m.stop hu) hU hk
  have hH : h∈D \ (insert t K).biUnion id := by
    rw [cover_insert]
    exact mem_sdiff.mpr ⟨m.stop.inside (Assemble.tile_sub_union (mem_insert_self _ _) hU),
      fun he => (mem_union.mp he).elim ht' hK⟩
  have exactU : u=insert h (t.erase q) := by
    ext x
    constructor
    · intro xu
      by_cases xt : x∈t
      · exact mem_insert_of_mem (mem_erase.mpr ⟨fun e => qU (e ▸ xu),xt⟩)
      · exact mem_insert.mpr (Or.inl (mem_singleton.mp (hs ▸ mem_sdiff.mpr ⟨xu,xt⟩)))
    · intro he
      rcases mem_insert.mp he with rfl | hx
      · exact hU
      · by_contra xu
        have xq : x=q := mem_singleton.mp (qs ▸ mem_sdiff.mpr ⟨mem_of_mem_erase hx,xu⟩)
        exact (ne_of_mem_erase hx) xq
  have step := swap m.start (mem_insert_self t K) hH qT (exactU ▸ uT)
  have fr : (insert t K).erase t = K := erase_insert ht
  refine ⟨t,mem_insert_self _ _,h,hH,q,qT,exactU ▸ uT,?_,?_⟩
  · rw [fr,←exactU]
  · simpa only [fr,←exactU] using step.2

/-- A nonterminal neutral replacement on a three-hole board changes at most
two holes. If it changes two, there is a two-step refinement in the same
four/five-vertex neighborhood, and every other tile stays fixed. -/
theorem refine_step {D : Finset V} {P Q : Parts V} (step : Slide G D P Q)
    (holes : (D \ P.biUnion id).card=3) :
    CanFinish G D P ∨ MoveOne G D P Q ∨
      ∃ R, MoveOne G D P R ∧ MoveOne G D R Q := by
  obtain ⟨K,a,b,ha,hb,ne,rfl,rfl⟩ := step.one
  have Ta := step.start.part.tile a (mem_insert_self _ _)
  have Tb := step.stop.part.tile b (mem_insert_self _ _)
  have notZero : (b\a).card ≠ 0 := by
    intro he
    have ha' : b ⊆ a := sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp he)
    exact ne (eq_of_subset_of_card_le ha' (by rw [Ta.1,Tb.1])).symm
  have bound : (b\a).card ≤ 3 := (card_le_card sdiff_subset).trans_eq Tb.1
  have freeA := free_of_pack step.start ha
  have freeB := free_of_pack step.stop hb
  have bD : b⊆D := fun _ hv => step.stop.inside (Assemble.tile_sub_union (mem_insert_self _ _) hv)
  have aD : a⊆D := fun _ hv => step.start.inside (Assemble.tile_sub_union (mem_insert_self _ _) hv)
  by_cases c1 : (b\a).card=1
  · exact Or.inr (Or.inl ⟨step.start,step.stop,⟨K,a,b,ha,hb,c1,rfl,rfl⟩⟩)
  by_cases c3 : (b\a).card=3
  · have eb : b\a=b := eq_of_subset_of_card_le sdiff_subset (by rw [c3,Tb.1])
    have incl : b ⊆ D \ (insert a K).biUnion id := by
      intro x hx
      have xn := (mem_sdiff.mp (eb.symm ▸ hx)).2
      rw [cover_insert]
      exact mem_sdiff.mpr ⟨bD hx,fun hh => (mem_union.mp hh).elim xn
        (fun hx' => disjoint_left.mp freeB hx hx')⟩
    have eq := eq_of_subset_of_card_le incl (by rw [holes,Tb.1])
    exact Or.inl (show KelmansStarter.IsTile G _ from eq ▸ Tb)
  have c2 : (b\a).card=2 := by omega
  have cnt := card_sdiff_add_card_inter b a
  have int : (b∩a).card=1 := by have hc := Tb.1; omega
  obtain ⟨v,hv⟩ := card_eq_one.mp int
  have vb : v∈b := (mem_inter.mp (show v∈b∩a by rw [hv]; simp)).1
  have va : v∈a := (mem_inter.mp (show v∈b∩a by rw [hv]; simp)).2
  obtain ⟨x,xb,vx⟩ := tile_neighbor Tb vb
  have xa : x∉a := by
    intro hxa
    have e : x∈b∩a := mem_inter.mpr ⟨xb,hxa⟩
    rw [hv,mem_singleton] at e
    exact (G.ne_of_adj vx) e.symm
  obtain ⟨w,wa,vw⟩ := tile_neighbor Ta va
  have wb : w∉b := by
    intro hwb
    have e : w∈b∩a := mem_inter.mpr ⟨hwb,wa⟩
    rw [hv,mem_singleton] at e
    exact (G.ne_of_adj vw) e.symm
  let c : Finset V := {x,v,w}
  have ct : KelmansStarter.IsTile G c := path_tile G vx.symm vw (fun h => xa (h.symm ▸ wa))
  have ds : c ⊆ a∪b := by
    intro u hu
    simp only [c,mem_insert,mem_singleton] at hu
    rcases hu with rfl|rfl|rfl
    · exact mem_union_right _ xb
    · exact mem_union_left _ va
    · exact mem_union_left _ wa
  have space : Disjoint c (K.biUnion id) := by
    apply disjoint_left.mpr
    intro u uc uk
    exact (mem_union.mp (ds uc)).elim
      (fun ha' => disjoint_left.mp freeA ha' uk) (fun hb' => disjoint_left.mp freeB hb' uk)
  have ck : c∉K := not_in_frame ct space
  have frame : PackIn G D K := PackIn.restrict step.start (by simp)
  have mid := PackIn.add frame ct (ds.trans (union_subset aD bD)) space
  have xdiff : c\a={x} := by
    ext u
    simp only [c,mem_sdiff,mem_insert,mem_singleton]
    constructor
    · rintro ⟨e,nu⟩
      rcases e with rfl|rfl|rfl
      · rfl
      · exact (nu va).elim
      · exact (nu wa).elim
    · rintro rfl
      exact ⟨Or.inl rfl,xa⟩
  have wdiff : c\b={w} := by
    ext u
    simp only [c,mem_sdiff,mem_insert,mem_singleton]
    constructor
    · rintro ⟨e,nu⟩
      rcases e with rfl|rfl|rfl
      · exact (nu xb).elim
      · exact (nu vb).elim
      · rfl
    · rintro rfl
      exact ⟨Or.inr (Or.inr rfl),wb⟩
  have bc : (b\c).card=1 := by
    have A := card_sdiff_add_card_inter c b
    have B := card_sdiff_add_card_inter b c
    rw [wdiff,card_singleton] at A
    rw [inter_comm c b] at A
    have ccard := ct.1
    have bcard := Tb.1
    omega
  refine Or.inr (Or.inr ⟨insert c K,⟨step.start,mid,K,a,c,ha,ck,?_,rfl,rfl⟩,
    ⟨mid,step.stop,K,c,b,ck,hb,bc,rfl,rfl⟩⟩)
  rw [xdiff,card_singleton]

/-- The three-hole condition is preserved by every neutral replacement. -/
theorem holes_invariant {D : Finset V} {P Q : Parts V} (step : Slide G D P Q) :
    (D \ P.biUnion id).card=(D \ Q.biUnion id).card := by
  have cov (R : Parts V) (h : PackIn G D R) : (R.biUnion id).card=3*R.card := by
    rw [card_biUnion]
    · have eq : ∀ t ∈ R, t.card = 3 := fun t ht => (h.part.tile t ht).1
      change (∑ u ∈ R, u.card) = 3 * R.card
      rw [sum_congr rfl eq]
      simp [sum_const_nat,Nat.mul_comm]
    · exact fun s hs t ht ne => h.part.disj s hs t ht ne
  have p := card_sdiff_add_card_inter D (P.biUnion id)
  have q := card_sdiff_add_card_inter D (Q.biUnion id)
  have ip : D ∩ P.biUnion id = P.biUnion id := inter_eq_right.mpr step.start.inside
  have iq : D ∩ Q.biUnion id = Q.biUnion id := inter_eq_right.mpr step.stop.inside
  rw [ip,cov P step.start] at p
  rw [iq,cov Q step.stop] at q
  have same := step.same_size
  omega

/-- Any successful sequence of arbitrary one-tile replacements can be
normalized to one-hole steps, without using more than twice as many steps.
One skips any suffix after an already augmentable state. -/
theorem normalize_to_single_holes {D : Finset V} {n : ℕ} {P Q : Parts V}
    (seq : Slides G D n P Q) (holes : (D \ P.biUnion id).card=3)
    (done : CanFinish G D Q) :
    ∃ m ≤ 2*n, ∃ R, OneMoves G D m P R ∧ CanFinish G D R := by
  induction seq with
  | nil P ok => exact ⟨0,by simp,P,OneMoves.nil P ok,done⟩
  | @cons n P Q R step tail ih =>
    rcases refine_step step holes with hp | h | ⟨S,a,b⟩
    · exact ⟨0,by omega,P,OneMoves.nil _ step.start,hp⟩
    · obtain ⟨m,hm,T,tr,fin⟩ := ih ((holes_invariant step) ▸ holes) done
      exact ⟨m+1,by omega,T,OneMoves.cons h tr,fin⟩
    · obtain ⟨m,hm,T,tr,fin⟩ := ih ((holes_invariant step) ▸ holes) done
      exact ⟨m+1+1,by omega,T,OneMoves.cons a (OneMoves.cons b tr),fin⟩

#print axioms contact_edge_iff
#print axioms contact_nonedge_iff
#print axioms swap
#print axioms MoveOne.exact_contact
#print axioms normalize_to_single_holes
end KelmansCactus.ContactSlides
