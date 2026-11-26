import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Written on the Wall II, conjecture 299

The total domination number is at most the annihilation number plus
the number of degree-two vertices. The final theorem uses the literal
sorted degree prefix, with its equality to the subset version proved here.

Two constructions based on supports of leaves turn the remaining
domination requirement into a transversal problem. With order n, leaf
count L and degree-two count k, they give 12γₜ ≤ 6n+4L+3k.
A degree-sum estimate for the smallest nonleaf degrees gives the
annihilation bound needed to conclude.

The rank-three transversal argument is that of Chvátal and McDiarmid,
Small transversals in hypergraphs (1992), DOI 10.1007/BF01191201.
Jakovac's 2026 preprint (arXiv:2609.10795) concerns the related a+1
bound for minimum degree two; the theorem here includes graphs with leaves.
Catalogue: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf
Checked with Lean 4.19.0 and Mathlib v4.19.0.
-/

namespace Graffiti299
open Finset SimpleGraph
open scoped BigOperators

private theorem card_filter_eq_sum {V : Type*} (S : Finset V) (p : V → Prop)
    [DecidablePred p] : (S.filter p).card = ∑ x ∈ S, if p x then (1 : ℕ) else 0 := by
  rw [← sum_filter]
  simp

private theorem sum_card_incidence {V E : Type*} (V₀ : Finset V) (E₀ : Finset E)
    (p : V → E → Prop) [DecidableRel p] :
    (∑ v ∈ V₀, (E₀.filter (p v)).card) =
      ∑ e ∈ E₀, (V₀.filter (fun v => p v e)).card := by
  simp only [card_filter_eq_sum]
  exact sum_comm

private theorem choose_one {V E : Type*} [DecidableEq V]
    (E₀ : Finset E) (f : E → Finset V) (h : ∀ e ∈ E₀, (f e).Nonempty) :
    ∃ T : Finset V, T.card ≤ E₀.card ∧
      (∀ v ∈ T, ∃ e ∈ E₀, v ∈ f e) ∧ ∀ e ∈ E₀, ∃ v ∈ T, v ∈ f e := by
  classical
  have he (e : E₀) : ∃ v, v ∈ f e.1 := h e e.2
  choose pick hp using he
  refine ⟨E₀.attach.image pick,card_image_le.trans_eq card_attach,?_,?_⟩
  · intro v hv
    obtain ⟨e,_,rfl⟩ := mem_image.mp hv
    exact ⟨e,e.2,hp e⟩
  · intro e he
    exact ⟨pick ⟨e,he⟩,mem_image_of_mem _ (mem_attach _ _),hp ⟨e,he⟩⟩

section DualMatching
variable {V E : Type*} [DecidableEq V] [DecidableEq E]

private def PairMatching (oc : V → Finset E) (M : Finset V) : Prop :=
  (M : Set V).PairwiseDisjoint oc

set_option maxHeartbeats 2000000 in
/-- A multigraph of maximum degree three has a matching with at least a
quarter of its edges. Edges are indexed individually, allowing parallel edges. -/
private theorem matching_quarter (F : Finset V) (oc : V → Finset E) (I : Finset E)
    (hpair : ∀ x ∈ F, (oc x).card = 2 ∧ oc x ⊆ I)
    (hdeg : ∀ i ∈ I, (F.filter (fun x => i ∈ oc x)).card ≤ 3) :
    ∃ M ⊆ F, PairMatching oc M ∧ F.card ≤ 4*M.card := by
  classical
  let candidates := F.powerset.filter (PairMatching oc)
  have hEmpty : ∅ ∈ candidates := mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),by
    intro x hx; simp at hx⟩
  obtain ⟨M₀,hM₀,hmax⟩ := exists_max_image candidates card ⟨∅,hEmpty⟩
  let weight := fun x => (F.filter (fun y => oc y = oc x)).card
  let largest := candidates.filter (fun M => M.card = M₀.card)
  obtain ⟨M,hM,hbest⟩ := exists_max_image largest (fun M => ∑ x ∈ M, weight x)
    ⟨M₀,mem_filter.mpr ⟨hM₀,rfl⟩⟩
  have hm : M ⊆ F := mem_powerset.mp (mem_filter.mp (mem_filter.mp hM).1).1
  have hdis : PairMatching oc M := (mem_filter.mp (mem_filter.mp hM).1).2
  have hmaximum (B : Finset V) (hb : B ⊆ F) (hd : PairMatching oc B) : B.card ≤ M.card := by
    rw [(mem_filter.mp hM).2]
    exact hmax B (mem_filter.mpr ⟨mem_powerset.mpr hb,hd⟩)
  have hheaviest (B : Finset V) (hb : B ⊆ F) (hd : PairMatching oc B) (hMc : B.card = M.card) :
      (∑ x ∈ B, weight x) ≤ ∑ x ∈ M, weight x :=
    hbest B (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr hb,hd⟩,
      hMc.trans (mem_filter.mp hM).2⟩)
  let P := M.biUnion oc
  have hPI : P ⊆ I := fun i hi => by
    obtain ⟨x,hx,hix⟩ := mem_biUnion.mp hi
    exact (hpair x (hm hx)).2 hix
  have hPc : P.card = 2*M.card := by
    rw [card_biUnion hdis]
    rw [sum_const_nat (fun x hx => (hpair x (hm hx)).1), Nat.mul_comm]
  have disj_of_outside (x : V) (hx : x ∈ F) (hout : Disjoint (oc x) P) : False := by
    have hxM : x ∉ M := by
      intro h
      obtain ⟨i,hi⟩ := card_pos.mp (show 0 < (oc x).card by rw [(hpair x hx).1]; decide)
      exact disjoint_left.mp hout hi (mem_biUnion.mpr ⟨x,h,hi⟩)
    have hf : PairMatching oc (insert x M) := by
      intro a ha b hb hab
      simp only [mem_coe,mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact (hab rfl).elim
      · exact hout.mono_right (fun _ hi => mem_biUnion.mpr ⟨b,hb,hi⟩)
      · exact (hout.mono_right (fun _ hi => mem_biUnion.mpr ⟨a,ha,hi⟩)).symm
      · exact hdis ha hb hab
    have h := hmaximum _ (insert_subset hx hm) hf
    rw [card_insert_of_not_mem hxM] at h
    omega
  let X := F.filter (fun x => ∃ i ∈ oc x, i ∉ P)
  have has_matched (x : V) (hx : x ∈ F) : ∃ i ∈ oc x, i ∈ P := by
    apply Classical.byContradiction
    intro h
    exact disj_of_outside x hx (disjoint_left.mpr (fun i hi hiP => h ⟨i,hi,hiP⟩))
  have cross_shape {x : V} (hx : x ∈ X) {i : E} (hi : i ∈ oc x) (hiP : i ∈ P) :
      ∃ j, j ∉ P ∧ oc x = {i,j} := by
    obtain ⟨hxF,j,hj,hjP⟩ := mem_filter.mp hx
    have hij : i ≠ j := fun h => hjP (h ▸ hiP)
    refine ⟨j,hjP,(eq_of_subset_of_card_le (s := {i,j}) ?_ ?_).symm⟩
    · exact insert_subset hi (singleton_subset_iff.mpr hj)
    · simp [hij,(hpair x hxF).1]
  have not_cross (x : V) (hx : x ∈ M) : x ∉ X := by
    intro h
    obtain ⟨_,j,hj,hjn⟩ := mem_filter.mp h
    exact hjn (mem_biUnion.mpr ⟨x,hx,hj⟩)
  have old_disj {x : V} (hx : x ∈ M) {i j : E}
      (hi : i ∈ oc x) (hj : j ∉ P) (a : V) (ha : a ∈ M.erase x) :
      Disjoint ({i,j} : Finset E) (oc a) := by
    obtain ⟨hnx,haM⟩ := mem_erase.mp ha
    apply disjoint_left.mpr
    intro p hp hpa
    rcases mem_insert.mp hp with rfl | hp
    · exact disjoint_left.mp (hdis hx haM hnx.symm) hi hpa
    · rw [mem_singleton.mp hp] at hpa
      exact hj (mem_biUnion.mpr ⟨a,haM,hpa⟩)
  have replace {x : V} (hx : x ∈ M) (J : Finset V)
      (hj : J ⊆ F) (hjdis : PairMatching oc J)
      (hold : ∀ a ∈ J, ∀ b ∈ M.erase x, Disjoint (oc a) (oc b)) :
      (M.erase x ∪ J) ⊆ F ∧ PairMatching oc (M.erase x ∪ J) ∧
        (M.erase x ∪ J).card = M.card - 1 + J.card := by
    have hDJ : Disjoint (M.erase x) J := disjoint_left.mpr fun a ha hja => by
      have h := hold a hja a ha
      have hn := card_pos.mp (show 0 < (oc a).card by rw [(hpair a (hj hja)).1]; decide)
      obtain ⟨i,hi⟩ := hn
      exact disjoint_left.mp h hi hi
    refine ⟨union_subset ((erase_subset ..).trans hm) hj,?_,by
      rw [card_union_of_disjoint hDJ,card_erase_of_mem hx]⟩
    intro a ha b hb hab
    rcases mem_union.mp ha with ha | ha <;> rcases mem_union.mp hb with hb | hb
    · exact hdis (mem_of_mem_erase ha) (mem_of_mem_erase hb) hab
    · exact (hold b hb a ha).symm
    · exact hold a ha b hb
    · exact hjdis ha hb hab
  have no_extra {x y z : V} (hx : x ∈ M) (hy : y ∈ X) (hz : z ∈ X)
      {u v i j : E} (huv : u ≠ v) (hu : u ∈ oc x) (hv : v ∈ oc x)
      (hi : i ∉ P) (hj : j ∉ P) (hyoc : oc y = {u,i}) (hzoc : oc z = {v,j}) : i=j := by
    apply Classical.byContradiction
    intro hij
    have huP : u ∈ P := mem_biUnion.mpr ⟨x,hx,hu⟩
    have hvP : v ∈ P := mem_biUnion.mpr ⟨x,hx,hv⟩
    have hd : Disjoint (oc y) (oc z) := by
      rw [hyoc,hzoc]
      simp [Finset.disjoint_insert_left,Finset.disjoint_insert_right,huv.symm,Ne.symm hij,
        show j ≠ u from fun h => hj (h.symm ▸ huP),show v ≠ i from fun h => hi (h ▸ hvP)]
    have hyz : y ≠ z := by
      intro h
      subst z
      exact disjoint_left.mp hd (show u ∈ oc y by simp [hyoc])
        (show u ∈ oc y by simp [hyoc])
    have hrep := replace hx {y,z}
      (insert_subset (mem_filter.mp hy).1 (singleton_subset_iff.mpr (mem_filter.mp hz).1)) (by
        intro a ha b hb hab
        simp only [mem_coe,mem_insert,mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact (hab rfl).elim
        · exact hd
        · exact hd.symm
        · exact (hab rfl).elim) (by
        intro a ha b hb
        rcases mem_insert.mp ha with rfl | ha
        · rw [hyoc]
          exact old_disj hx hu hi b hb
        · rw [mem_singleton.mp ha,hzoc]
          exact old_disj hx hv hj b hb)
    have hmax' := hmaximum _ hrep.1 hrep.2.1
    have hpos := card_pos.mpr ⟨x,hx⟩
    have hc := hrep.2.2
    have hTwo : ({y,z} : Finset V).card = 2 := by simp [hyz]
    rw [hTwo] at hc
    omega
    -- Continuation of the matching-count proof.
  have forbid_heavy {x : V} (hx : x ∈ M) {u v : E} (huv : u ≠ v)
      (hu : u ∈ oc x) (hv : v ∈ oc x)
      (hu₂ : 2 ≤ (X.filter (fun y => u ∈ oc y)).card)
      (hv₁ : (X.filter (fun y => v ∈ oc y)).Nonempty) : False := by
    let Xu := X.filter (fun y => u ∈ oc y)
    obtain ⟨y₁,hy₁,y₂,hy₂,hyne⟩ := one_lt_card.mp (show 1 < Xu.card from hu₂)
    obtain ⟨z,hz⟩ := hv₁
    have hy₁X := (mem_filter.mp hy₁).1
    have hy₂X := (mem_filter.mp hy₂).1
    have hzX := (mem_filter.mp hz).1
    have huP : u ∈ P := mem_biUnion.mpr ⟨x,hx,hu⟩
    have hvP : v ∈ P := mem_biUnion.mpr ⟨x,hx,hv⟩
    obtain ⟨i₁,hi₁,he₁⟩ := cross_shape hy₁X (mem_filter.mp hy₁).2 huP
    obtain ⟨i₂,hi₂,he₂⟩ := cross_shape hy₂X (mem_filter.mp hy₂).2 huP
    obtain ⟨j,hj,hez⟩ := cross_shape hzX (mem_filter.mp hz).2 hvP
    have hij₁ := no_extra hx hy₁X hzX huv hu hv hi₁ hj he₁ hez
    have hij₂ := no_extra hx hy₂X hzX huv hu hv hi₂ hj he₂ hez
    have he : oc y₂ = oc y₁ := by rw [he₁,he₂,hij₁,hij₂]
    have hyw : 2 ≤ weight y₁ := by
      have hb : ({y₁,y₂} : Finset V) ⊆ F.filter (fun y => oc y = oc y₁) :=
        insert_subset (mem_filter.mpr ⟨(mem_filter.mp hy₁X).1,rfl⟩)
          (singleton_subset_iff.mpr (mem_filter.mpr ⟨(mem_filter.mp hy₂X).1,he⟩))
      simpa [hyne] using card_le_card hb
    let Par := F.filter (fun y => oc y = oc x)
    have huI : u ∈ I := hPI huP
    have hcap := hdeg u huI
    have hPS : Par ∪ Xu ⊆ F.filter (fun y => u ∈ oc y) := by
      intro y hy
      rcases mem_union.mp hy with hy | hy
      · obtain ⟨hyF,hey⟩ := mem_filter.mp hy
        exact mem_filter.mpr ⟨hyF,hey.symm ▸ hu⟩
      · exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hy).1).1,(mem_filter.mp hy).2⟩
    have hPD : Disjoint Par Xu := by
      apply disjoint_left.mpr
      intro y hp hxu
      obtain ⟨_,i,hi,hn⟩ := mem_filter.mp (mem_filter.mp hxu).1
      exact hn (mem_biUnion.mpr ⟨x,hx,(mem_filter.mp hp).2 ▸ hi⟩)
    have hbound := (card_le_card hPS).trans hcap
    rw [card_union_of_disjoint hPD] at hbound
    have hxw : weight x ≤ 1 := by change Par.card ≤ 1; change 2 ≤ Xu.card at hu₂; omega
    have hNew := replace hx {y₁}
      (singleton_subset_iff.mpr (mem_filter.mp hy₁X).1) (by
        intro a ha b hb hab
        simp only [mem_coe,mem_singleton] at ha hb
        exact (hab (ha.trans hb.symm)).elim) (by
        intro a ha b hb
        rw [mem_singleton.mp ha,he₁]
        exact old_disj hx hu hi₁ b hb)
    have hcard := hNew.2.2
    have hpos := card_pos.mpr ⟨x,hx⟩
    have hcard' : (M.erase x ∪ {y₁}).card = M.card := by simp only [card_singleton] at hcard; omega
    have hs := hheaviest _ hNew.1 hNew.2.1 hcard'
    have hn : y₁ ∉ M.erase x := fun h => not_cross y₁ (mem_of_mem_erase h) hy₁X
    have hUnion : M.erase x ∪ {y₁} = insert y₁ (M.erase x) := by
      ext z; simp [or_comm]
    rw [hUnion, sum_insert hn] at hs
    have heq := sum_erase_add _ (f := weight) hx
    omega
  have side_le {x : V} (hx : x ∈ M) {u : E} (hu : u ∈ oc x) :
      (X.filter (fun y => u ∈ oc y)).card ≤ 2 := by
    let T := X.filter (fun y => u ∈ oc y)
    have hnot : x ∉ T := fun h => not_cross x hx (mem_filter.mp h).1
    have hsub : insert x T ⊆ F.filter (fun y => u ∈ oc y) := by
      apply insert_subset (mem_filter.mpr ⟨hm hx,hu⟩)
      intro y hy
      exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hy).1).1,(mem_filter.mp hy).2⟩
    have h := (card_le_card hsub).trans (hdeg u (hPI (mem_biUnion.mpr ⟨x,hx,hu⟩)))
    rw [card_insert_of_not_mem hnot] at h
    change T.card ≤ 2
    omega
  let cross := fun x => X.filter (fun y => (oc y ∩ oc x).Nonempty)
  have each_cross (x : V) (hx : x ∈ M) : (cross x).card ≤ 2 := by
    obtain ⟨u,v,huv,he⟩ := card_eq_two.mp (hpair x (hm hx)).1
    have hu : u ∈ oc x := by simp [he]
    have hv : v ∈ oc x := by simp [he]
    let Xu := X.filter (fun y => u ∈ oc y)
    let Xv := X.filter (fun y => v ∈ oc y)
    have heq : cross x ⊆ Xu ∪ Xv := by
      intro y hy
      obtain ⟨hyX,i,hi⟩ := mem_filter.mp hy
      have hix := (mem_inter.mp hi).2
      rw [he] at hix
      rcases mem_insert.mp hix with rfl | h
      · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hyX,(mem_inter.mp hi).1⟩))
      · have hv' := mem_singleton.mp h
        exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hyX,hv' ▸ (mem_inter.mp hi).1⟩))
    have hb := (card_le_card heq).trans (card_union_le Xu Xv)
    have hu₂ := side_le hx hu
    have hv₂ := side_le hx hv
    change Xu.card ≤ 2 at hu₂
    change Xv.card ≤ 2 at hv₂
    change (cross x).card ≤ Xu.card + Xv.card at hb
    apply Classical.byContradiction
    intro h
    have hun : Xu.Nonempty := card_pos.mp (by omega)
    have hvn : Xv.Nonempty := card_pos.mp (by omega)
    by_cases huH : 2 ≤ Xu.card
    · exact forbid_heavy hx huv hu hv huH hvn
    · have hvH : 2 ≤ Xv.card := by omega
      exact forbid_heavy hx huv.symm hv hu hvH hun
  have hX : X.card ≤ 2*M.card := by
    have hsub : X ⊆ M.biUnion cross := by
      intro y hy
      obtain ⟨i,hi,hiP⟩ := has_matched y (mem_filter.mp hy).1
      obtain ⟨x,hx,hix⟩ := mem_biUnion.mp hiP
      exact mem_biUnion.mpr ⟨x,hx,mem_filter.mpr ⟨hy,i,mem_inter.mpr ⟨hi,hix⟩⟩⟩
    have h₁ := (card_le_card hsub).trans card_biUnion_le
    have h₂ := sum_le_sum (s := M) (fun x hx => each_cross x hx)
    rw [sum_const_nat (fun _ _ => rfl),Nat.mul_comm] at h₂
    exact h₁.trans h₂
  have hIncidence : (∑ x ∈ F, (P.filter (fun i => i ∈ oc x)).card) ≤ 3*P.card := by
    rw [sum_card_incidence]
    have hsum := sum_le_sum (s := P) (fun i hi => hdeg i (hPI hi))
    rwa [sum_const_nat (fun _ _ => rfl), Nat.mul_comm] at hsum
  have hLow : 2*F.card ≤ (∑ x ∈ F, (P.filter (fun i => i ∈ oc x)).card) + X.card := by
    let p := fun x : V => ∃ i ∈ oc x, i ∉ P
    have hpt (x : V) (hx : x ∈ F) :
        2 ≤ (P.filter (fun i => i ∈ oc x)).card + (if p x then 1 else 0) := by
      by_cases h : p x
      · obtain ⟨i,hi,hiP⟩ := has_matched x hx
        have hpos : 0 < (P.filter (fun i => i ∈ oc x)).card :=
          card_pos.mpr ⟨i,mem_filter.mpr ⟨hiP,hi⟩⟩
        rw [if_pos h]
        omega
      · have heq : P.filter (fun i => i ∈ oc x) = oc x := by
          ext i
          simp only [mem_filter]
          exact ⟨And.right,fun hi => ⟨Classical.byContradiction (fun hn => h ⟨i,hi,hn⟩),hi⟩⟩
        rw [if_neg h,heq,(hpair x hx).1]
    have hs := sum_le_sum hpt
    rw [sum_const_nat (f := fun _ => 2) (fun _ _ => rfl),sum_add_distrib,
      ← card_filter_eq_sum,Nat.mul_comm] at hs
    exact hs
  rw [hPc] at hIncidence
  exact ⟨M,hm,hdis,by omega⟩

end DualMatching

#print axioms matching_quarter

section Transversal

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

private def occurs (I : Finset E) (f : E → Finset V) (v : V) : Finset E :=
  I.filter (fun e => v ∈ f e)

private theorem transversal_of_low_incidence (W : Finset V) (I : Finset E) (f : E → Finset V)
    (hsub : ∀ e ∈ I, f e ⊆ W) (hne : ∀ e ∈ I, (f e).Nonempty)
    (hrank : ∀ e ∈ I, (f e).card ≤ 3)
    (hOcc : ∀ v ∈ W, (occurs I f v).card ≤ 2) :
    ∃ T ⊆ W, (∀ e ∈ I, ∃ v ∈ T, v ∈ f e) ∧
      4*T.card ≤ W.card + I.card + ∑ e ∈ I, (3 - (f e).card) := by
  classical
  let oc := occurs I f
  let F := W.filter (fun v => (oc v).card = 2)
  obtain ⟨M,hm,hM,hFour⟩ := matching_quarter F oc I
    (fun v hv => ⟨(mem_filter.mp hv).2,filter_subset _ _⟩) (by
      intro i hi
      apply (card_le_card ?_).trans (hrank i hi)
      intro v hv
      exact (mem_filter.mp (mem_filter.mp hv).2).2)
  let P := M.biUnion oc
  have hPI : P ⊆ I := by
    intro e he
    obtain ⟨v,hv,hve⟩ := mem_biUnion.mp he
    exact (mem_filter.mp hve).1
  have hcP : P.card = 2*M.card := by
    rw [card_biUnion hM,sum_const_nat (fun v hv => (mem_filter.mp (hm hv)).2),Nat.mul_comm]
  have hFW : F ⊆ W := filter_subset _ _
  have hIcount : (∑ e ∈ I, (f e).card) ≤ W.card + F.card := by
    have heq : (∑ v ∈ W, (oc v).card) = ∑ e ∈ I, (f e).card := by
      have h := sum_card_incidence W I (fun v e => v ∈ f e)
      change (∑ v ∈ W, (oc v).card) =
        ∑ e ∈ I, (W.filter (fun v => v ∈ f e)).card at h
      rw [h]
      apply sum_congr rfl
      intro e he
      have hset : W.filter (fun v => v ∈ f e) = f e := by
        ext v
        simp only [mem_filter]
        exact ⟨And.right,fun hv => ⟨hsub e he hv,hv⟩⟩
      rw [hset]
    rw [← heq]
    have hpoint (v : V) (hv : v ∈ W) : (oc v).card ≤
        1 + (if (oc v).card = 2 then 1 else 0) := by
      have h := hOcc v hv
      change (oc v).card ≤ 2 at h
      split <;> omega
    have hsum := sum_le_sum hpoint
    rw [sum_add_distrib, sum_const_nat (f := fun _ => 1) (fun _ _ => rfl),
      Nat.mul_one,← card_filter_eq_sum] at hsum
    exact hsum
  have hId : (∑ e ∈ I, (f e).card) + (∑ e ∈ I, (3-(f e).card)) = 3*I.card := by
    rw [← sum_add_distrib]
    calc
      _ = I.card * 3 := sum_const_nat (fun e he => by have := hrank e he; omega)
      _ = _ := Nat.mul_comm _ _
  obtain ⟨B,hB,hw,hBhit⟩ := choose_one (I \ P) f (fun e he => hne e (mem_sdiff.mp he).1)
  have hBW : B ⊆ W := by
    intro v hv
    obtain ⟨e,he,hve⟩ := hw v hv
    exact hsub e (mem_sdiff.mp he).1 hve
  refine ⟨M ∪ B,union_subset (hm.trans hFW) hBW,?_,?_⟩
  · intro e he
    by_cases hep : e ∈ P
    · obtain ⟨v,hv,hve⟩ := mem_biUnion.mp hep
      exact ⟨v,mem_union_left _ hv,(mem_filter.mp hve).2⟩
    · obtain ⟨v,hv,hve⟩ := hBhit e (mem_sdiff.mpr ⟨he,hep⟩)
      exact ⟨v,mem_union_right _ hv,hve⟩
  · rw [card_sdiff hPI,hcP] at hB
    have hMc := card_union_le M B
    have hPc := card_le_card hPI
    rw [hcP] at hPc
    omega

set_option maxHeartbeats 1500000 in
private theorem transversal_small_edges (W : Finset V) (I : Finset E) (f : E → Finset V)
    (hsub : ∀ e ∈ I, f e ⊆ W) (hne : ∀ e ∈ I, (f e).Nonempty)
    (hrank : ∀ e ∈ I, (f e).card ≤ 3) :
    ∃ T ⊆ W, (∀ e ∈ I, ∃ v ∈ T, v ∈ f e) ∧
      4*T.card ≤ W.card + I.card + ∑ e ∈ I, (3 - (f e).card) := by
  classical
  induction W using Finset.strongInductionOn generalizing I with
  | _ W ih =>
    by_cases hlarge : ∃ x ∈ W, 3 ≤ (occurs I f x).card
    · obtain ⟨x,hx,hxx⟩ := hlarge
      let I' := I \ occurs I f x
      have hI : I' ⊆ I := sdiff_subset
      have hFor (e : E) (he : e ∈ I') : x ∉ f e := by
        intro he'
        exact (mem_sdiff.mp he).2 (mem_filter.mpr ⟨hI he,he'⟩)
      obtain ⟨T,hT,hHit,hBound⟩ := ih (W.erase x) (erase_ssubset hx) I'
        (fun e he v hv => mem_erase.mpr ⟨fun eq => hFor e he (eq ▸ hv),hsub e (hI he) hv⟩)
        (fun e he => hne e (hI he)) (fun e he => hrank e (hI he))
      refine ⟨insert x T,insert_subset hx (hT.trans (erase_subset _ _)),?_,?_⟩
      · intro e he
        by_cases he' : e ∈ I'
        · obtain ⟨v,hv,hve⟩ := hHit e he'
          exact ⟨v,mem_insert_of_mem hv,hve⟩
        · have hOcc : e ∈ occurs I f x := Classical.byContradiction
            (fun h => he' (mem_sdiff.mpr ⟨he,h⟩))
          exact ⟨x,mem_insert_self _ _,(mem_filter.mp hOcc).2⟩
      · have hcost : (∑ e ∈ I', (3-(f e).card)) ≤ ∑ e ∈ I, (3-(f e).card) :=
          sum_le_sum_of_subset_of_nonneg hI (fun _ _ _ => Nat.zero_le _)
        have hcI : I'.card = I.card - (occurs I f x).card := card_sdiff (filter_subset _ _)
        have hle := card_le_card (filter_subset (fun e => x ∈ f e) I)
        change (occurs I f x).card ≤ I.card at hle
        rw [card_erase_of_mem hx,hcI] at hBound
        have hIns := card_insert_le x T
        have hp := card_pos.mpr ⟨x,hx⟩
        omega
    · exact transversal_of_low_incidence W I f hsub hne hrank
        (fun v hv => by have h : ¬3 ≤ (occurs I f v).card := fun hh => hlarge ⟨v,hv,hh⟩; omega)

/-- A transversal bound with one unit of deficit for each missing member
of an edge of size less than three. -/
theorem transversal_bound (W : Finset V) (I : Finset E) (f : E → Finset V)
    (hsub : ∀ e ∈ I, f e ⊆ W) (hne : ∀ e ∈ I, (f e).Nonempty) :
    ∃ T ⊆ W, (∀ e ∈ I, ∃ v ∈ T, v ∈ f e) ∧
      4*T.card ≤ W.card + I.card + ∑ e ∈ I, (3 - (f e).card) := by
  classical
  have h (e : E) : ∃ s ⊆ f e, s.card = min 3 (f e).card :=
    exists_subset_card_eq (min_le_right _ _)
  choose s hs hcard using h
  obtain ⟨T,hT,hHit,hBound⟩ := transversal_small_edges W I s
    (fun e he => (hs e).trans (hsub e he)) (fun e he => card_pos.mp (by
      have hp := card_pos.mpr (hne e he)
      rw [hcard]
      omega)) (fun e _ => (hcard e).le.trans (min_le_left _ _))
  have hSum : (∑ e ∈ I, (3-(s e).card)) = ∑ e ∈ I, (3-(f e).card) := by
    apply sum_congr rfl
    intro e _
    rw [hcard]
    omega
  rw [hSum] at hBound
  exact ⟨T,hT,fun e he => by
    obtain ⟨v,hv,hve⟩ := hHit e he
    exact ⟨v,hv,hs e hve⟩,hBound⟩

end Transversal

#print axioms transversal_bound


section Graph

noncomputable section
variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V
local instance (H : SimpleGraph V) : DecidableRel H.Adj := Classical.decRel H.Adj

def TotalDominates (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, ∃ w ∈ D, G.Adj v w

def totalDominationNumber (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ D, TotalDominates G D ∧ D.card = n}

def degreeTwo (G : SimpleGraph V) : Finset V :=
  univ.filter (fun v => G.degree v = 2)

private def leaves (G : SimpleGraph V) : Finset V :=
  univ.filter (fun v => G.degree v = 1)

private def supports (G : SimpleGraph V) : Finset V :=
  univ.filter (fun v => ∃ u ∈ leaves G, G.Adj v u)

private def covers (G : SimpleGraph V) (S : Finset V) (v : V) : Prop :=
  ∃ u ∈ S, G.Adj v u

private theorem mem_leaves (G : SimpleGraph V) (v : V) :
    v ∈ leaves G ↔ G.degree v = 1 := by simp [leaves]

private theorem mem_two (G : SimpleGraph V) (v : V) :
    v ∈ degreeTwo G ↔ G.degree v = 2 := by simp [degreeTwo]

private theorem mem_supports (G : SimpleGraph V) (v : V) :
    v ∈ supports G ↔ ∃ u ∈ leaves G, G.Adj v u := by simp [supports]

private theorem adj_of_connected {G : SimpleGraph V} (hc : G.Connected)
    (hn : 1 < Fintype.card V) (v : V) : ∃ w, G.Adj v w := by
  obtain ⟨w,hw⟩ := Fintype.exists_ne_of_one_lt_card hn v
  obtain ⟨p⟩ := hc v w
  cases p with
  | nil => exact (hw rfl).elim
  | cons h _ => exact ⟨_,h⟩

omit [Fintype V] in
private theorem walk_closed {G : SimpleGraph V} {u v : V} (P : V → Prop)
    (hc : ∀ x y, P x → G.Adj x y → P y) (p : G.Walk u v) : P u → P v := by
  induction p with
  | nil => exact id
  | cons h _ ih => exact fun hx => ih (hc _ _ hx h)

private theorem leaf_unique {G : SimpleGraph V} {v a b : V}
    (hv : v ∈ leaves G) (ha : G.Adj v a) (hb : G.Adj v b) : a = b := by
  have hcard : (G.neighborFinset v).card ≤ 1 := by
    rw [card_neighborFinset_eq_degree,(mem_leaves _ _).mp hv]
  exact card_le_one.mp hcard a ((G.mem_neighborFinset _ _).mpr ha)
    b ((G.mem_neighborFinset _ _).mpr hb)

private theorem neighbor_of_leaf_not_leaf {G : SimpleGraph V}
    (hc : G.Connected) (hn : 2 < Fintype.card V) {u v : V}
    (hu : u ∈ leaves G) (huv : G.Adj u v) : v ∉ leaves G := by
  intro hv
  have hAll (w : V) : w ∈ ({u,v} : Finset V) := by
    obtain ⟨p⟩ := hc u w
    apply walk_closed (fun z => z ∈ ({u,v} : Finset V)) _ p (by simp)
    intro a b ha hab
    simp only [mem_insert,mem_singleton] at ha ⊢
    rcases ha with rfl | rfl
    · exact Or.inr (leaf_unique hu hab huv)
    · exact Or.inl (leaf_unique hv hab huv.symm)
  have h := card_le_card (s := (univ : Finset V)) (t := {u,v}) (fun w _ => hAll w)
  rw [card_univ] at h
  have hs := card_le_two (a := u) (b := v)
  omega

private theorem supports_card_le (G : SimpleGraph V) : (supports G).card ≤ (leaves G).card := by
  classical
  have h (v : supports G) : ∃ u, u ∈ leaves G ∧ G.Adj v.1 u := (mem_supports _ _).mp v.2
  choose f hf using h
  have hi : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact leaf_unique (hf a).1 (hf a).2.symm (he.symm ▸ (hf b).2.symm)
  have hs : (supports G).attach.image f ⊆ leaves G := by
    intro u hu
    obtain ⟨v,_,rfl⟩ := mem_image.mp hu
    exact (hf v).1
  have hle := card_le_card hs
  rwa [card_image_of_injective _ hi,card_attach] at hle

private theorem sum_leaf_degrees (G : SimpleGraph V) :
    (∑ v ∈ leaves G, G.degree v) = (leaves G).card := by
  rw [sum_const_nat (fun v hv => (mem_leaves _ _).mp hv),Nat.mul_one]

private theorem neighbor_sum_leaf_bound (G : SimpleGraph V) (I : Finset V) :
    (∑ v ∈ I, ((leaves G).filter (G.Adj v)).card) ≤ (leaves G).card := by
  classical
  rw [sum_card_incidence,← sum_leaf_degrees]
  apply sum_le_sum
  intro v hv
  rw [← G.card_neighborFinset_eq_degree v]
  apply card_le_card
  intro u hu
  exact (G.mem_neighborFinset _ _).mpr (mem_filter.mp hu).2.symm

private theorem nonleaf_is_star_if_unattached {G : SimpleGraph V}
    (hc : G.Connected) {r : V} (hr : r ∉ leaves G)
    (h : ∀ v, G.Adj r v → v ∈ leaves G) :
    (∀ v, v ≠ r → G.Adj r v) ∧ (leaves G).card = Fintype.card V - 1 := by
  classical
  have hAll (v : V) : v = r ∨ G.Adj r v := by
    obtain ⟨p⟩ := hc r v
    apply walk_closed (fun w => w = r ∨ G.Adj r w) _ p (Or.inl rfl)
    intro a b ha hab
    rcases ha with rfl | ha
    · exact Or.inr hab
    · exact Or.inl (leaf_unique (h _ ha) hab ha.symm)
  have he : leaves G = (univ : Finset V).erase r := by
    ext v
    simp only [mem_erase,mem_univ,and_true]
    exact ⟨fun hv he => hr (he ▸ hv),fun hn => h v ((hAll v).resolve_left hn)⟩
  exact ⟨fun v hv => (hAll v).resolve_left hv,by rw [he,card_erase_of_mem (mem_univ _),card_univ]⟩

set_option maxHeartbeats 1800000 in
private theorem domination_two_choices (G : SimpleGraph V) (hc : G.Connected)
    (hn : 2 < Fintype.card V)
    (hNear : ∀ v ∉ leaves G, ∃ w ∉ leaves G, G.Adj v w) :
    ∃ D, TotalDominates G D ∧
      12*D.card ≤ 6*Fintype.card V + 4*(leaves G).card + 3*(degreeTwo G).card := by
  classical
  let Z := leaves G
  let Q := (univ : Finset V) \ Z
  let S := supports G
  let R := Q \ S
  let T := R.filter (covers G S)
  have hZ (v : V) : v ∈ Z ↔ G.degree v = 1 := mem_leaves G v
  have hQ (v : V) : v ∈ Q ↔ v ∉ Z := by simp [Q]
  have hR (v : V) : v ∈ R ↔ v ∉ Z ∧ v ∉ S := by simp [R,Q]
  have hS (v : V) : v ∈ S ↔ ∃ w ∈ Z, G.Adj v w := mem_supports G v
  have hSQ : S ⊆ Q := by
    intro v hv
    obtain ⟨w,hw,hvw⟩ := (hS v).mp hv
    exact (hQ v).mpr (neighbor_of_leaf_not_leaf hc hn hw hvw.symm)
  have hs := supports_card_le G
  change S.card ≤ Z.card at hs
  have hz (v : V) (hv : v ∈ Z) : covers G S v := by
    obtain ⟨w,hw⟩ := adj_of_connected hc (by omega) v
    exact ⟨w,(hS w).mpr ⟨v,hv,hw.symm⟩,hw⟩
  have hp (v : V) : 0 < G.degree v :=
    (G.degree_pos_iff_exists_adj v).mpr (adj_of_connected hc (by omega) v)
  have hDef (v : V) (hvl : v ∉ Z) :
      3 - G.degree v ≤ if G.degree v = 2 then (1:ℕ) else 0 := by
    have h := hp v
    have hne : G.degree v ≠ 1 := fun h => hvl ((hZ v).mpr h)
    split <;> omega
  have hFilterBound (I : Finset V) :
      (∑ v ∈ I, if G.degree v = 2 then (1:ℕ) else 0) ≤ (degreeTwo G).card := by
    rw [← card_filter_eq_sum]
    apply card_le_card
    intro v hv
    exact (mem_two G v).mpr (mem_filter.mp hv).2
  let I := Q.filter (fun v => ¬covers G S v)
  let f := fun v => R.filter (G.Adj v)
  have hmem (v : V) (hv : v ∈ I) : v ∉ Z ∧ ¬covers G S v :=
    ⟨(hQ v).mp (mem_filter.mp hv).1,(mem_filter.mp hv).2⟩
  have hNonempty (v : V) (hv : v ∈ I) : (f v).Nonempty := by
    obtain ⟨w,hw,had⟩ := hNear v (hmem v hv).1
    exact ⟨w,mem_filter.mpr ⟨(hR w).mpr ⟨hw,fun hs => (hmem v hv).2 ⟨w,hs,had⟩⟩,had⟩⟩
  obtain ⟨D,hD,hHit,hBound⟩ := transversal_bound R I f (fun v _ => filter_subset _ _) hNonempty
  have hTot : TotalDominates G (S ∪ D) := by
    intro v
    by_cases hv : covers G S v
    · obtain ⟨w,hw,ha⟩ := hv
      exact ⟨w,mem_union_left _ hw,ha⟩
    · have hV : v ∉ Z := fun hw => hv (hz v hw)
      obtain ⟨w,hw,hvw⟩ := hHit v (mem_filter.mpr ⟨(hQ v).mpr hV,hv⟩)
      exact ⟨w,mem_union_right _ hw,(mem_filter.mp hvw).2⟩
  have hDefsum : (∑ v ∈ I, (3-(f v).card)) ≤ Z.card + (degreeTwo G).card := by
    have hpt (v : V) (hv : v ∈ I) :
        3-(f v).card ≤ (Z.filter (G.Adj v)).card + (if G.degree v = 2 then (1:ℕ) else 0) := by
      let F := f v
      let B := Z.filter (G.Adj v)
      have hU : F ∪ B = G.neighborFinset v := by
        ext w
        change w ∈ (R.filter (G.Adj v) ∪ Z.filter (G.Adj v)) ↔ w ∈ G.neighborFinset v
        simp only [mem_union,mem_filter,mem_neighborFinset]
        constructor
        · rintro (⟨_,h⟩ | ⟨_,h⟩)
          · exact h
          · exact h
        · intro had
          by_cases hL : w ∈ Z
          · exact Or.inr ⟨hL,had⟩
          · exact Or.inl ⟨(hR w).mpr ⟨hL,fun hw => (hmem v hv).2 ⟨w,hw,had⟩⟩,had⟩
      have hC := card_union_le F B
      rw [hU,G.card_neighborFinset_eq_degree] at hC
      have hC' := hDef v (hmem v hv).1
      change 3-F.card ≤ B.card + _
      omega
    have hsum := sum_le_sum hpt
    rw [sum_add_distrib] at hsum
    have h₁ := neighbor_sum_leaf_bound G I
    have h₂ := hFilterBound I
    change (∑ v ∈ I, (Z.filter (G.Adj v)).card) ≤ Z.card at h₁
    omega
  have hQT : I.card + T.card ≤ Q.card := by
    have hDis : Disjoint I T := disjoint_left.mpr fun v hv hvt =>
      (mem_filter.mp hv).2 (mem_filter.mp hvt).2
    have h := card_le_card (union_subset (filter_subset _ _) ((filter_subset _ _).trans sdiff_subset)
      : I ∪ T ⊆ Q)
    rwa [card_union_of_disjoint hDis] at h
  have hQr : Q.card = Fintype.card V - Z.card := by
    exact (card_sdiff (subset_univ Z)).trans (by rw [card_univ])
  have hRr : R.card = Q.card - S.card := card_sdiff hSQ
  have hSQc := card_le_card hSQ
  have hZc := card_le_univ Z
  have hD₁ : 4*(S ∪ D).card + T.card ≤
      2*Fintype.card V + 2*Z.card + (degreeTwo G).card := by
    have h := card_union_le S D
    omega
  let U := S ∪ T
  let W := Q \ U
  let J := Q.filter (fun v => ¬covers G U v)
  have hUQ : U ⊆ Q := union_subset hSQ ((filter_subset _ _).trans sdiff_subset)
  have hUJ (v : V) (hv : v ∈ U) : covers G U v := by
    rcases mem_union.mp hv with hv | hv
    · obtain ⟨w,hw,hvw⟩ := hNear v ((hQ v).mp (hSQ hv))
      by_cases hws : w ∈ S
      · exact ⟨w,mem_union_left _ hws,hvw⟩
      · have hwr : w ∈ R := (hR w).mpr ⟨hw,hws⟩
        exact ⟨w,mem_union_right _ (mem_filter.mpr ⟨hwr,v,hv,hvw.symm⟩),hvw⟩
    · obtain ⟨w,hw,hvw⟩ := (mem_filter.mp hv).2
      exact ⟨w,mem_union_left _ hw,hvw⟩
  have hJW : J ⊆ W := by
    intro v hv
    exact mem_sdiff.mpr ⟨(mem_filter.mp hv).1,fun h => (mem_filter.mp hv).2 (hUJ v h)⟩
  have hN (v : V) (hv : v ∈ J) : W.filter (G.Adj v) = G.neighborFinset v := by
    ext w
    simp only [mem_filter,mem_neighborFinset]
    refine ⟨And.right,fun had => ⟨mem_sdiff.mpr ⟨?_,?_⟩,had⟩⟩
    · apply (hQ w).mpr
      intro hw
      have hvs := (hS v).mpr ⟨w,hw,had⟩
      exact (mem_sdiff.mp (hJW hv)).2 (mem_union_left _ hvs)
    · exact fun hw => (mem_filter.mp hv).2 ⟨w,hw,had⟩
  obtain ⟨B,hB,hBHit,hBCost⟩ := transversal_bound W J (fun v => W.filter (G.Adj v))
    (fun _ _ => filter_subset _ _) (fun v hv => by
      change (W.filter (G.Adj v)).Nonempty
      rw [hN v hv]
      apply card_pos.mp
      rw [card_neighborFinset_eq_degree]
      exact hp v)
  have hTot₂ : TotalDominates G (U ∪ B) := by
    intro v
    by_cases hv : covers G U v
    · obtain ⟨w,hw,ha⟩ := hv
      exact ⟨w,mem_union_left _ hw,ha⟩
    · have hV : v ∉ Z := fun hw => by
        obtain ⟨w,hwS,hvw⟩ := hz v hw
        exact hv ⟨w,mem_union_left _ hwS,hvw⟩
      obtain ⟨w,hw,hvw⟩ := hBHit v (mem_filter.mpr ⟨(hQ v).mpr hV,hv⟩)
      exact ⟨w,mem_union_right _ hw,(mem_filter.mp hvw).2⟩
  have hBDef : (∑ v ∈ J, (3-(W.filter (G.Adj v)).card)) ≤ (degreeTwo G).card := by
    refine (sum_le_sum (s := J) ?_).trans (hFilterBound J)
    intro v hv
    rw [hN v hv,G.card_neighborFinset_eq_degree]
    exact hDef v ((hQ v).mp (mem_filter.mp hv).1)
  have hUcard : U.card = S.card+T.card := card_union_of_disjoint
    (disjoint_left.mpr (fun x hx hxt => (hR x).mp (mem_filter.mp hxt).1 |>.2 hx))
  have hWcard : W.card = Q.card-U.card := card_sdiff hUQ
  have hWU := card_le_card hUQ
  have hJc := card_le_card hJW
  have hD₂ : 4*(U ∪ B).card ≤ 2*Fintype.card V + 2*T.card + (degreeTwo G).card := by
    have h := card_union_le U B
    omega
  change ∃ D, TotalDominates G D ∧
    12*D.card ≤ 6*Fintype.card V + 4*Z.card + 3*(degreeTwo G).card
  by_cases hsmall : 3*T.card ≤ 2*Z.card
  · exact ⟨U ∪ B,hTot₂,by omega⟩
  · exact ⟨S ∪ D,hTot,by omega⟩


/-- The largest size of a set whose degree sum is at most the edge count.
For a fixed size the sorted degree prefix has minimum sum. -/
def annihilation (G : SimpleGraph V) : ℕ :=
  ((univ : Finset V).powerset.filter
    (fun A => (∑ v ∈ A, G.degree v) ≤ G.edgeFinset.card)).sup card

private theorem le_annihilation {G : SimpleGraph V} {A : Finset V}
    (h : (∑ v ∈ A, G.degree v) ≤ G.edgeFinset.card) :
    A.card ≤ annihilation G :=
  le_sup (f := card) (mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),h⟩)

private theorem leaves_le_edges {G : SimpleGraph V} (hc : G.Connected)
    (hn : 2 < Fintype.card V) : (leaves G).card ≤ G.edgeFinset.card := by
  have hEdge := hc.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,← G.edgeFinset_card] at hEdge
  by_cases h : (leaves G).Nonempty
  · obtain ⟨u,hu⟩ := h
    obtain ⟨v,hv⟩ := adj_of_connected hc (by omega) u
    have hv' := neighbor_of_leaf_not_leaf hc hn hu hv
    have hs : leaves G ⊆ (univ : Finset V).erase v :=
      fun u' hu' => mem_erase.mpr ⟨fun h => hv' (h ▸ hu'),mem_univ _⟩
    have h' := card_le_card hs
    rw [card_erase_of_mem (mem_univ _),card_univ] at h'
    omega
  · rw [not_nonempty_iff_eq_empty.mp h,card_empty]
    exact Nat.zero_le _

private theorem sum_cross_le {W : Type*} (S R : Finset W) (d : W → ℕ)
    (h : ∀ x ∈ S, ∀ y ∈ R, d x ≤ d y) :
    R.card*(∑ x ∈ S, d x) ≤ S.card*(∑ y ∈ R, d y) := by
  calc
    _ = ∑ x ∈ S, ∑ _y ∈ R, d x := by
      simp [mul_sum, Nat.nsmul_eq_mul]
    _ ≤ ∑ _x ∈ S, ∑ y ∈ R, d y :=
      sum_le_sum (fun x hx => sum_le_sum (h x hx))
    _ = _ := by simp [Nat.nsmul_eq_mul]

private theorem choose_below_average {W : Type*} [DecidableEq W]
    (S : Finset W) (d : W → ℕ) {k : ℕ} (hk : k ≤ S.card) :
    ∃ B ⊆ S, B.card = k ∧ S.card*(∑ x ∈ B, d x) ≤ k*(∑ x ∈ S, d x) := by
  classical
  let A := S.powerset.filter (fun t => t.card = k)
  obtain ⟨B₀,h₀,hc⟩ := exists_subset_card_eq hk
  obtain ⟨B,hB,hmin⟩ := exists_min_image A (fun t => ∑ x ∈ t, d x)
    ⟨B₀,mem_filter.mpr ⟨mem_powerset.mpr h₀,hc⟩⟩
  have hbS := mem_powerset.mp (mem_filter.mp hB).1
  have hbc := (mem_filter.mp hB).2
  let R := S \ B
  have hOrder (x : W) (hx : x ∈ B) (y : W) (hy : y ∈ R) : d x ≤ d y := by
    let C := insert y (B.erase x)
    have hyB := (mem_sdiff.mp hy).2
    have hyr : y ∉ B.erase x := fun h => hyB (mem_of_mem_erase h)
    have hCS : C ⊆ S := insert_subset (mem_sdiff.mp hy).1 ((erase_subset _ _).trans hbS)
    have hCC : C.card = k := by
      have hp := card_pos.mpr ⟨x,hx⟩
      dsimp [C]
      rw [card_insert_of_not_mem hyr,card_erase_of_mem hx]
      omega
    have h := hmin C (mem_filter.mpr ⟨mem_powerset.mpr hCS,hCC⟩)
    have he := sum_erase_add _ (f := d) hx
    change (∑ z ∈ B, d z) ≤ ∑ z ∈ insert y (B.erase x), d z at h
    rw [sum_insert hyr] at h
    omega
  have hCross := sum_cross_le B R d hOrder
  have hsum : (∑ x ∈ R, d x) + ∑ x ∈ B, d x = ∑ x ∈ S, d x := sum_sdiff hbS
  have hcard : R.card + B.card = S.card := by
    have hl := card_le_card hbS
    change (S \ B).card + _ = _
    rw [card_sdiff hbS]
    omega
  refine ⟨B,hbS,hbc,?_⟩
  rw [← hcard,← hbc,← hsum,add_mul,mul_add]
  omega

private def highVertices (G : SimpleGraph V) : Finset V :=
  (univ : Finset V) \ (leaves G ∪ degreeTwo G)

private theorem counts_partition (G : SimpleGraph V) :
    Fintype.card V = (leaves G).card + (degreeTwo G).card + (highVertices G).card := by
  have hDis : Disjoint (leaves G) (degreeTwo G) := disjoint_left.mpr fun v h₁ h₂ => by
    have h₁ := (mem_leaves _ _).mp h₁
    have h₂ := (mem_two _ _).mp h₂
    omega
  have he := card_sdiff (subset_univ (leaves G ∪ degreeTwo G))
  have hc := card_le_univ (leaves G ∪ degreeTwo G)
  rw [card_univ,card_union_of_disjoint hDis] at he
  rw [card_union_of_disjoint hDis] at hc
  change (highVertices G).card = _ at he
  omega

private theorem annihilation_lower {G : SimpleGraph V} (hc : G.Connected)
    (hn : 2 < Fintype.card V) {b : ℕ}
    (hb : 6*b ≤ 5*(leaves G).card + 3*(highVertices G).card) :
    b ≤ annihilation G := by
  classical
  let L := leaves G
  let Q := highVertices G
  let l := L.card
  let q := Q.card
  let s := ∑ v ∈ Q, G.degree v
  change 6*b ≤ 5*l + 3*q at hb
  by_cases hsmall : b ≤ l
  · exact hsmall.trans (le_annihilation ((sum_leaf_degrees G).trans_le (leaves_le_edges hc hn)))
  let p := b-l
  have hp : p ≤ q := by dsimp [p]; omega
  obtain ⟨B,hBQ,hBc,hAvg⟩ := choose_below_average Q (fun v => G.degree v) hp
  let k := q-2*p
  have hk : q = 2*p+k := by dsimp [k,p]; omega
  have hlk : l ≤ 3*k := by dsimp [k,p]; omega
  have hq : 0 < q := by dsimp [p] at hp; omega
  have hsd : 3*q ≤ s := by
    rw [Nat.mul_comm 3 q, ← sum_const_nat (s := Q) (f := fun _ => 3) (fun _ _ => rfl)]
    apply sum_le_sum
    intro v hv
    have hd := (G.degree_pos_iff_exists_adj v).mpr (adj_of_connected hc (by omega) v)
    have hnot := (mem_sdiff.mp hv).2
    have h₁ : G.degree v ≠ 1 := fun h => hnot (mem_union_left _ ((mem_leaves _ _).mpr h))
    have h₂ : G.degree v ≠ 2 := fun h => hnot (mem_union_right _ ((mem_two _ _).mpr h))
    omega
  have hle : q*l ≤ k*s := by
    calc
      _ ≤ q*(3*k) := Nat.mul_le_mul_left _ hlk
      _ = k*(3*q) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hsd
  have hprod : q*s = 2*(p*s)+k*s := by
    calc
      _ = (2*p+k)*s := congrArg (fun q => q*s) hk
      _ = _ := by ring
  let t := ∑ v ∈ B, G.degree v
  change q*t ≤ p*s at hAvg
  have hsum : q*(2*t+l) ≤ q*s := by
    rw [mul_add, Nat.mul_left_comm q 2 t]
    omega
  have hAff := Nat.le_of_mul_le_mul_left hsum hq
  have hLQ : Disjoint L Q := by
    apply disjoint_left.mpr
    intro v hv hq'
    exact (mem_sdiff.mp hq').2 (mem_union_left _ hv)
  have hTot : l+s ≤ ∑ v, G.degree v := by
    have hsum := sum_le_sum_of_subset_of_nonneg (subset_univ (L ∪ Q))
      (f := fun v => G.degree v) (fun _ _ _ => Nat.zero_le _)
    rw [sum_union hLQ,sum_leaf_degrees] at hsum
    exact hsum
  rw [G.sum_degrees_eq_twice_card_edges] at hTot
  have hLB : Disjoint L B := hLQ.mono_right hBQ
  have hAff' : (∑ v ∈ L ∪ B, G.degree v) ≤ G.edgeFinset.card := by
    rw [sum_union hLB,sum_leaf_degrees]
    change l+t ≤ _
    omega
  have ha := le_annihilation hAff'
  rw [card_union_of_disjoint hLB,hBc] at ha
  change l+p ≤ _ at ha
  dsimp [p] at ha
  omega

private theorem bound_annihilation (G : SimpleGraph V) (hc : G.Connected) (hn : 2 < Fintype.card V) :
    totalDominationNumber G ≤ annihilation G + (degreeTwo G).card := by
  classical
  by_cases h : ∀ v ∉ leaves G, ∃ w ∉ leaves G, G.Adj v w
  · obtain ⟨D,hD,hb⟩ := domination_two_choices G hc hn h
    have hpart := counts_partition G
    have ha := annihilation_lower hc hn (b := D.card-(degreeTwo G).card) (by omega)
    have hd : totalDominationNumber G ≤ D.card := Nat.sInf_le ⟨D,hD,rfl⟩
    omega
  · push_neg at h
    obtain ⟨r,hr,hOnly⟩ := h
    obtain ⟨hAll,hcount⟩ := nonleaf_is_star_if_unattached hc hr (fun v hv =>
      Classical.byContradiction (fun hn => hOnly v hn hv))
    obtain ⟨w,hw⟩ := adj_of_connected hc (by omega) r
    have hd : TotalDominates G {r,w} := by
      intro v
      by_cases hv : v = r
      · subst v
        exact ⟨w,by simp,hw⟩
      · exact ⟨r,by simp,(hAll v hv).symm⟩
    have hγ : totalDominationNumber G ≤ ({r,w} : Finset V).card := Nat.sInf_le ⟨_,hd,rfl⟩
    have ha := le_annihilation ((sum_leaf_degrees G).trans_le (leaves_le_edges hc hn))
    have htwo := card_le_two (a := r) (b := w)
    omega


private def ascendingVertices (G : SimpleGraph V) : List V :=
  (univ : Finset V).toList.mergeSort (fun a b => decide (G.degree a ≤ G.degree b))

def ascendingDegreeSequence (G : SimpleGraph V) : List ℕ :=
  (ascendingVertices G).map (fun v => G.degree v)

/-- Catalogue definition 89 with the handshaking identity used for the budget. -/
def catalogueAnnihilation (G : SimpleGraph V) : ℕ :=
  ((range (Fintype.card V+1)).filter
    (fun k => ((ascendingDegreeSequence G).take k).sum ≤ G.edgeFinset.card)).sup id

private theorem equal_size_lighter {W : Type*} [DecidableEq W] (A B : Finset W)
    (d : W → ℕ) (h : A.card = B.card)
    (hcmp : ∀ x ∈ A \ B, ∀ y ∈ B \ A, d x ≤ d y) :
    (∑ x ∈ A, d x) ≤ ∑ x ∈ B, d x := by
  let R := A \ B
  let S := B \ A
  have hc : R.card = S.card := card_sdiff_comm h
  have hRS : (∑ x ∈ R, d x) ≤ ∑ x ∈ S, d x := by
    by_cases hb : R.Nonempty
    · have hv := sum_cross_le R S d hcmp
      rw [← hc] at hv
      exact Nat.le_of_mul_le_mul_left hv (card_pos.mpr hb)
    · simp [not_nonempty_iff_eq_empty.mp hb]
  have h₁ : (∑ x ∈ A \ (A ∩ B), d x) + (∑ x ∈ A ∩ B, d x) = ∑ x ∈ A, d x :=
    sum_sdiff inter_subset_left
  have h₂ : (∑ x ∈ B \ (A ∩ B), d x) + (∑ x ∈ A ∩ B, d x) = ∑ x ∈ B, d x :=
    sum_sdiff inter_subset_right
  have ha : A \ (A ∩ B) = R := by
    ext x
    by_cases hx : x ∈ A <;> by_cases hy : x ∈ B <;> simp [R,hx,hy]
  have hb : B \ (A ∩ B) = S := by
    ext x
    by_cases hx : x ∈ A <;> by_cases hy : x ∈ B <;> simp [S,hx,hy]
  rw [ha] at h₁
  rw [hb] at h₂
  omega

private theorem literal_prefix (G : SimpleGraph V) (k : ℕ) (hk : k ≤ Fintype.card V) :
    ∃ A : Finset V, A.card = k ∧
      (∑ a ∈ A, G.degree a) = ((ascendingDegreeSequence G).take k).sum ∧
      ∀ B : Finset V, B.card = k → (∑ a ∈ A, G.degree a) ≤ ∑ b ∈ B, G.degree b := by
  classical
  let s := ascendingVertices G
  let P := s.take k
  let Q := s.drop k
  have hperm : s.Perm (univ : Finset V).toList := List.mergeSort_perm _ _
  have hlen : s.length = Fintype.card V := by simpa using hperm.length_eq
  have hsd : s.Nodup := hperm.nodup_iff.mpr (univ : Finset V).nodup_toList
  have hpd : P.Nodup := hsd.sublist (List.take_sublist _ _)
  have hcard : P.toFinset.card = k := by
    rw [List.toFinset_card_of_nodup hpd]
    change (s.take k).length = k
    simp [hlen,Nat.min_eq_left hk]
  have hsum : (∑ v ∈ P.toFinset, G.degree v) = ((ascendingDegreeSequence G).take k).sum := by
    unfold ascendingDegreeSequence
    rw [← List.map_take]
    change (∑ v ∈ P.toFinset, G.degree v) = (P.map (fun v => G.degree v)).sum
    rw [← Multiset.sum_coe,← Multiset.map_coe]
    have hval : P.toFinset.val = (P : Multiset V) := by
      rw [List.toFinset_val,List.dedup_eq_self.mpr hpd]
    rw [← hval]
    rfl
  have hsorted : s.Pairwise (fun a b => G.degree a ≤ G.degree b) := by
    unfold s ascendingVertices
    have hh := List.sorted_mergeSort (le := fun a b : V => decide (G.degree a ≤ G.degree b))
      (fun a b c hab hbc => by simpa using (of_decide_eq_true hab).trans (of_decide_eq_true hbc))
      (fun a b => by simp [le_total]) (univ : Finset V).toList
    exact hh.imp (fun h => of_decide_eq_true h)
  have hap : P ++ Q = s := List.take_append_drop _ _
  have hpq : (P ++ Q).Pairwise (fun a b => G.degree a ≤ G.degree b) := hap.symm ▸ hsorted
  refine ⟨P.toFinset,hcard,hsum,?_⟩
  intro B hB
  apply equal_size_lighter _ _ (fun v => G.degree v) (hcard.trans hB.symm)
  intro a ha b hb
  have haP := List.mem_toFinset.mp (mem_sdiff.mp ha).1
  have hbP : b ∉ P := fun h => (mem_sdiff.mp hb).2 (List.mem_toFinset.mpr h)
  have hbs : b ∈ s := hperm.mem_iff.mpr (by simp)
  have hbQ : b ∈ Q := by rw [← hap] at hbs; exact (List.mem_append.mp hbs).resolve_left hbP
  exact (List.pairwise_append.mp hpq).2.2 a haP b hbQ

theorem annihilation_eq_catalogue (G : SimpleGraph V) :
    annihilation G = catalogueAnnihilation G := by
  classical
  apply le_antisymm
  · unfold annihilation
    apply Finset.sup_le
    intro A hA
    have hk : A.card ≤ Fintype.card V := card_le_univ A
    obtain ⟨B,_,hbs,hle⟩ := literal_prefix G A.card hk
    have hb := (hle A rfl).trans ((mem_filter.mp hA).2)
    rw [hbs] at hb
    exact le_sup (f := id) (mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hk),hb⟩)
  · unfold catalogueAnnihilation
    apply Finset.sup_le
    intro k hk
    obtain ⟨B,hbc,hbs,_⟩ := literal_prefix G k (by
      have := mem_range.mp (mem_filter.mp hk).1
      omega)
    have h := le_annihilation (hbs.symm ▸ (mem_filter.mp hk).2)
    exact hbc ▸ h

/-- Written on the Wall II #299 with the literal sorted-prefix annihilation number. -/
theorem conjecture299 (G : SimpleGraph V) (hc : G.Connected) (hn : 2 < Fintype.card V) :
    totalDominationNumber G ≤ catalogueAnnihilation G + (degreeTwo G).card := by
  rw [← annihilation_eq_catalogue]
  exact bound_annihilation G hc hn

#print axioms conjecture299
#print axioms annihilation_eq_catalogue

end
end Graph
end Graffiti299
