import ThetaAsymmetricFaithfulValid

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaAsymmetricFaithfulScope
open SquareCap (boundary SmallTrivial FactorOn)
open PentagonCap (SmallFourTrivial)
open ThetaAsymmetricFaithfulTable (Wire oldWires)
open ThetaAsymmetricFaithful (ambient candidate target link)
open ThetaAsymmetricFaithfulGeometry (ProperWires root3)
open ThetaAsymmetricFaithfulTiny (IndependentContacts)
open ThetaSevenFaithfulRefill (In)
open ThetaSevenFaithfulCap (core9)
open ThetaAsymmetricFaithfulValid (cap_valid_iff_independent_contacts reduce_of_independent_contacts)

noncomputable section
universe u

private theorem triple_of_card {W : Type*} (S : Finset W) (size : 3≤S.card) :
    ∃ a∈S,∃ b∈S,∃ c∈S,a≠b∧a≠c∧b≠c := by
  classical
  obtain ⟨a,ha,b,hb,ab⟩ := one_lt_card.mp (by omega : 1<S.card)
  have two : ({a,b}:Finset W).card=2 := by simp [card_insert_of_not_mem,ab]
  obtain ⟨c,hc,nd⟩ := exists_mem_not_mem_of_card_lt_card (by omega : ({a,b}:Finset W).card<S.card)
  have both : c≠a ∧ c≠b := by simpa using nd
  exact ⟨a,ha,b,hb,c,hc,ab,both.1.symm,both.2.symm⟩

private theorem small_dense_shore_impossible {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph W} [DecidableRel G.Adj] (cub : ∀ x,G.degree x=3)
    (small : SmallFourTrivial G)
    (S : Finset W) (inner : 3≤S.card) (outer : 3≤Fintype.card W-S.card) (upper : S.card≤4)
    (internal : ∀ u∈S,∃ a∈S,∃ b∈S,a≠b∧G.Adj u a∧G.Adj u b) : False := by
  classical
  let color : W→Bool := fun w=>decide (w∈S)
  have cut0 := TwinObstruction.cut_le_exposed_vertices (G:=G) S S
    (fun _ us _ _ _=>us) (fun u _=> (cub u).le) internal
  change (boundary G color).card≤S.card at cut0
  obtain ⟨b,hb⟩ := small color (cut0.trans upper)
  rw [←Finset.card_compl] at outer
  cases b with
  | false =>
    obtain ⟨a,ha,b,hbb,c,hc,ab,ac,bc⟩ := triple_of_card Sᶜ outer
    have ea : color a=false := by simpa [color] using ha
    have eb : color b=false := by simpa [color] using hbb
    have ec : color c=false := by simpa [color] using hc
    exact (hb a b c ea eb ec).elim ab (fun h=>h.elim ac bc)
  | true =>
    obtain ⟨a,ha,b,hbb,c,hc,ab,ac,bc⟩ := triple_of_card S inner
    have ea : color a=true := by simpa [color] using ha
    have eb : color b=true := by simpa [color] using hbb
    have ec : color c=true := by simpa [color] using hc
    exact (hb a b c ea eb ec).elim ab (fun h=>h.elim ac bc)

private theorem no_triangle {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph W} [DecidableRel G.Adj] (cub : ∀ x,G.degree x=3)
    (small : SmallFourTrivial G) (size : 6≤Fintype.card W) {a b c : W}
    (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a) : False := by
  let S : Finset W := {a,b,c}
  have cnt : S.card=3 := by simp [S,card_insert_of_not_mem,ab.ne,bc.ne,ca.ne.symm]
  apply small_dense_shore_impossible cub small S (by omega) (by omega) (by omega)
  intro x hx
  simp only [S,mem_insert,mem_singleton] at hx
  rcases hx with rfl|rfl|rfl
  · exact ⟨b,by simp [S],c,by simp [S],bc.ne,ab,ca.symm⟩
  · exact ⟨c,by simp [S],a,by simp [S],ca.ne,bc,ab.symm⟩
  · exact ⟨a,by simp [S],b,by simp [S],ab.ne,ca,bc.symm⟩

private theorem no_square {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph W} [DecidableRel G.Adj] (cub : ∀ x,G.degree x=3)
    (small : SmallFourTrivial G) (size : 7≤Fintype.card W) {a b c d : W}
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) (da : G.Adj d a)
    (ac : a≠c) (bd : b≠d) : False := by
  let S : Finset W := {a,b,c,d}
  have cnt : S.card=4 := by
    simp [S,card_insert_of_not_mem,ab.ne,bc.ne,cd.ne,da.ne.symm,ac,bd]
  apply small_dense_shore_impossible cub small S (by omega) (by omega) (by omega)
  intro x hx
  simp only [S,mem_insert,mem_singleton] at hx
  rcases hx with rfl|rfl|rfl|rfl
  · exact ⟨b,by simp [S],d,by simp [S],bd,ab,da.symm⟩
  · exact ⟨c,by simp [S],a,by simp [S],ac.symm,bc,ab.symm⟩
  · exact ⟨d,by simp [S],b,by simp [S],bd.symm,cd,bc.symm⟩
  · exact ⟨a,by simp [S],c,by simp [S],ac,da,cd.symm⟩


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {B : SimpleGraph V} [DecidableRel B.Adj] {p : Wire→V}

omit [DecidableEq V] in
private theorem room : 7≤Fintype.card (V⊕Fin 9) := by simp

/-- None of the three contact edges at C can occur in the original
cyclic-five graph. The fixtures may allow either true h neighbor to be
a repeated contact of the theta elsewhere. -/
theorem faithful_contacts_independent (cub : ∀ x,(ambient B p).degree x=3)
    (cyc5 : SmallFourTrivial (ambient B p)) :
    ¬B.Adj (p 4) (p 5) ∧ ¬B.Adj (p 4) (p 6) ∧ ¬B.Adj (p 5) (p 6) := by
  let G := ambient B p
  have a : G.Adj (In 7) (In 8) := (by decide : ThetaSevenFaithfulCap.core9.Adj 7 8)
  have b : G.Adj (In 7) (Sum.inl (p 4)) := ⟨4,rfl,by decide⟩
  have c : G.Adj (In 8) (Sum.inl (p 5)) := ⟨5,rfl,by decide⟩
  have d : G.Adj (In 8) (Sum.inl (p 6)) := ⟨6,rfl,by decide⟩
  refine ⟨?_,?_,?_⟩
  · intro e
    have x : G.Adj (Sum.inl (p 4)) (Sum.inl (p 5)) := e
    exact no_square cub cyc5 room a c x.symm b.symm Sum.noConfusion Sum.noConfusion
  · intro e
    have x : G.Adj (Sum.inl (p 4)) (Sum.inl (p 6)) := e
    exact no_square cub cyc5 room a d x.symm b.symm Sum.noConfusion Sum.noConfusion
  · intro e
    have x : G.Adj (Sum.inl (p 5)) (Sum.inl (p 6)) := e
    exact no_triangle cub cyc5 (Nat.le_trans (by decide) room) c x d.symm

/-- Only the four original surviving theta contacts must be assumed
different. The two genuine h neighbors are distinct by cubicity,
and neither can be t because that would form an ambient triangle. -/
theorem proper_of_four_injective (cub : ∀ x,(ambient B p).degree x=3)
    (cyc5 : SmallFourTrivial (ambient B p))
    (four : ∀ i j : Wire,i.val<4→j.val<4→p i=p j→i=j) :
    ProperWires p := by
  let G := ambient B p
  have a : G.Adj (In 7) (In 8) := (by decide : core9.Adj 7 8)
  have b : G.Adj (In 7) (Sum.inl (p 4)) := ⟨4,rfl,by decide⟩
  have c : G.Adj (In 8) (Sum.inl (p 5)) := ⟨5,rfl,by decide⟩
  have d : G.Adj (In 8) (Sum.inl (p 6)) := ⟨6,rfl,by decide⟩
  refine ⟨four,?_,?_,?_⟩
  · intro eq
    have e : G.Adj (In 8) (Sum.inl (p 4)) := eq.symm ▸ c
    exact no_triangle cub cyc5 (Nat.le_trans (by decide) room) a e b.symm
  · intro eq
    have e : G.Adj (In 8) (Sum.inl (p 4)) := eq.symm ▸ d
    exact no_triangle cub cyc5 (Nat.le_trans (by decide) room) a e b.symm
  · intro eq
    let S : Finset (V⊕Fin 9) := {In 7,Sum.inl (p 5)}
    have sub : G.neighborFinset (In 8) ⊆ S := by
      intro j hj
      have ad : G.Adj (In 8) j := (mem_neighborFinset _ _ _).mp hj
      cases j with
      | inr j =>
        have only : ∀ j : Fin 9,core9.Adj 8 j→j=7 := by decide
        have jj := only j ad
        simp [S,jj]
      | inl x =>
        obtain ⟨i,ix,hx⟩ : link p oldWires x 8 := ad
        have only : ∀ i : Wire,(i,8)∈oldWires→i=5∨i=6 := by decide
        rcases only i hx with rfl|rfl
        · simp [S,←ix]
        · simp [S,←ix,eq]
    have low := card_le_card sub
    rw [card_neighborFinset_eq_degree] at low
    have n : G.degree (In 8)=3 := cub _
    have m : S.card=2 := by simp [S,card_insert_of_not_mem,In]
    omega

omit [Fintype V] [DecidableEq V] in
private theorem groups_iff (B : SimpleGraph V) (p : Wire→V) :
    IndependentContacts B p ↔
      (¬B.Adj (p 1) (p 2) ∧ ¬B.Adj (p 0) (p 3) ∧
       ¬B.Adj (p 4) (p 5) ∧ ¬B.Adj (p 4) (p 6) ∧ ¬B.Adj (p 5) (p 6)) := by
  let P : List (Wire×Wire) := [(1,2),(0,3),(4,5),(4,6),(5,6)]
  have listed : ∀ i j : Wire,i≠j→ root3 i=root3 j→(i,j)∈P∨(j,i)∈P := by decide
  constructor
  · intro h
    exact ⟨h 1 2 (by decide) (by decide),h 0 3 (by decide) (by decide),
      h 4 5 (by decide) (by decide), h 4 6 (by decide) (by decide),h 5 6 (by decide) (by decide)⟩
  · rintro ⟨a,b,c,d,e⟩ i j ne shared
    have deny (u v : Wire) (h : (u,v)∈P) : ¬B.Adj (p u) (p v) := by
      simp [P] at h
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact a
      · exact b
      · exact c
      · exact d
      · exact e
    rcases listed i j ne shared with h|h
    · exact deny i j h
    · exact fun w=>deny j i h w.symm

/-- Exact criterion. In the no-original-ear branch the second bound
is already part of the input, leaving only p2--p3 to be tested. -/
theorem cap_valid_iff_two_edges_absent (proper : ProperWires p)
    (cub : ∀ x,(ambient B p).degree x=3) (cyc5 : SmallFourTrivial (ambient B p)) :
    SmallTrivial (candidate B p) ↔ ¬B.Adj (p 1) (p 2) ∧ ¬B.Adj (p 0) (p 3) := by
  rw [cap_valid_iff_independent_contacts proper cub cyc5,groups_iff]
  constructor
  · rintro ⟨a,b,_,_,_⟩
    exact ⟨a,b⟩
  · rintro ⟨a,b⟩
    exact ⟨a,b,faithful_contacts_independent cub cyc5⟩

/-- Strictly smaller cyclic-four F2 handles the entire asymmetric layout
except the two explicit pairs, of which p1--p4 is a prior no-ear premise. -/
theorem reduce_of_two_edges_absent
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 9)))
    (proper : ProperWires p) (cub : ∀ x,(ambient B p).degree x=3)
    (cyc5 : SmallFourTrivial (ambient B p))
    (ab : ¬B.Adj (p 1) (p 2)) (cd : ¬B.Adj (p 0) (p 3))
    (order : Fintype.card (V⊕Fin 9)%6=4) :
    FactorOn (target B p) (univ.erase (In 6)) :=
  reduce_of_independent_contacts smaller proper cub cyc5
    ((groups_iff B p).mpr ⟨ab,cd,faithful_contacts_independent cub cyc5⟩) order

/-- Final physical layout statement. The independent anchors are exactly
the four surviving original theta contacts; t may coincide with one of them. -/
theorem reduce_of_four_contacts
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 9)))
    (cub : ∀ x,(ambient B p).degree x=3)
    (cyc5 : SmallFourTrivial (ambient B p))
    (four : ∀ i j : Wire,i.val<4→j.val<4→p i=p j→i=j)
    (ab : ¬B.Adj (p 1) (p 2)) (cd : ¬B.Adj (p 0) (p 3))
    (order : Fintype.card (V⊕Fin 9)%6=4) :
    FactorOn (target B p) (univ.erase (In 6)) :=
  reduce_of_two_edges_absent smaller (proper_of_four_injective cub cyc5 four) cub cyc5 ab cd order

#print axioms proper_of_four_injective
#print axioms faithful_contacts_independent
#print axioms cap_valid_iff_two_edges_absent
#print axioms reduce_of_two_edges_absent
#print axioms reduce_of_four_contacts
end
end KelmansCactus.AtomicBridge.ThetaAsymmetricFaithfulScope
