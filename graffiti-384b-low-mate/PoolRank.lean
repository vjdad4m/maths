import PoolFive
namespace Graffiti384b.PendantClose
open Finset SimpleGraph Donor JointRank
open private Repair.linkEdges Repair.edge_info Repair.triangles_le_choose from Repair384b
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private Donor.rankDegree from PendantBudget
open private RankTuran.floorD RankTuran.floor_ok from RankTuran384b
open private PendantRank.fiber from ActiveRank
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Only five-cliques inside X matter when the vertex and all its
neighbors lie in X. Apply the neighborhood Turán argument on this domain. -/
private theorem inner_turan {X : Finset V} {v : V} (vm : v∈X) (ns : G.neighborFinset v⊆X)
    (free : ∀C⊆X,¬G.IsNClique 5 C) :
    trianglesAt G v ≤ (turanGraph (G.degree v) 3).edgeFinset.card := by
  classical
  let N := G.neighborFinset v
  let J := G.induce (N : Set V)
  let emb : N ↪ V := Function.Embedding.subtype _
  have cf : J.CliqueFree 4 := by
    intro q cl
    have lifted : G.IsNClique 4 (q.map emb) :=
      cl.map.mono (G.spanningCoe_induce_le (s := (N : Set V)))
    apply free (insert v (q.map emb)) (insert_subset vm (by
      intro z zm; obtain ⟨a,_,rfl⟩ := mem_map.mp zm; exact ns a.property))
    apply lifted.insert
    intro w hw
    obtain ⟨x,_,rfl⟩ := mem_map.mp hw
    exact (G.mem_neighborFinset _ _).mp x.property
  let f : Sym2 N → Finset V := Sym2.lift ⟨fun a b => {a.val,b.val},fun a b => pair_comm _ _⟩
  have cover : Repair.linkEdges G v ⊆ J.edgeFinset.image f := by
    intro p hp
    obtain ⟨sub,sz,cl⟩ := Repair.edge_info G hp
    obtain ⟨x,y,ne,rfl⟩ := card_eq_two.mp sz
    have hx : x ∈ ({x,y} : Finset V) := mem_insert_self _ _
    have hy : y ∈ ({x,y} : Finset V) := mem_insert_of_mem (mem_singleton_self _)
    let a : N := ⟨x,sub hx⟩
    let b : N := ⟨y,sub hy⟩
    exact mem_image.mpr ⟨s(a,b),mem_edgeFinset.mpr (show J.Adj a b from cl x hx y hy ne),rfl⟩
  obtain ⟨M,dM,maximal⟩ := exists_isTuranMaximal (V := N) (show 0<3 by decide)
  letI := dM
  have cap := maximal.2 J cf
  obtain ⟨iso⟩ := maximal.nonempty_iso_turanGraph
  have t : trianglesAt G v ≤ M.edgeFinset.card := (card_le_card cover).trans (card_image_le.trans cap)
  rw [iso.card_edgeFinset_eq,Fintype.card_coe] at t
  exact t

private def charge (i : ℕ) :=
  let base := PendantRank.base
  let raw := FiniteRange.badCount 26 10
  let inside := if i=1 then max (base+raw 4) (base+raw 3-PendantRank.reward 3)
    else base+raw (RankTuran.floorD i)
  max (base+(26-Donor.rankDegree i).choose 10) inside

/-- In the internal five-clique-free case, an unexposed rank uses the
tripartite triangle cap. An exposed rank has one fixed external seed. -/
theorem exact_frame {X : Finset V} {e : V} (fr : Frame G X e) : gamma G≤Fintype.card V-15 := by
  classical
  by_contra! fail
  have free := five_free G fr fail
  let rank' := rank X (trianglesAt G)
  let A (v : V) := ((X.powersetCard 10).filter (fun k => v∈PendantRank.active G X k)).card
  let B (v : V) := ((X.powersetCard 10).filter (fun k => v∈FiniteRange.bad G X k)).card
  have each (v : V) (vm : v∈X) : PendantRank.base+B v≤charge (rank' v)+A v := by
    have ri : rank' v<26 := mem_range.mp (by rw [←fr.size,←rank_range X (trianglesAt G) fr.distinct]; exact mem_image_of_mem _ vm)
    have score := rank_lower X (trianglesAt G) fr.distinct 2 fr.scores vm
    change 2+rank' v≤trianglesAt G v at score
    have deg3 : 3≤G.degree v := (mem_filter.mp (fr.high_sub vm)).2
    have cap := Repair.triangles_le_choose G v
    unfold charge
    by_cases ext : v∈exposed G X
    · obtain ⟨w,wx,vw⟩ := (mem_filter.mp ext).2
      let d := Donor.rankDegree (rank' v)
      have ds : d≤8 := by dsimp [d]; unfold Donor.rankDegree; split_ifs <;> decide
      have lo : 1≤d := by dsimp [d]; unfold Donor.rankDegree; split_ifs <;> decide
      have dd : d≤G.degree v := by
        by_cases big : 8≤G.degree v
        · exact ds.trans big
        have tab : ∀a : Fin 8,∀r : Fin 26,2+r.val≤a.val.choose 2 → Donor.rankDegree r≤a := by decide
        exact tab ⟨_,Nat.lt_of_not_ge big⟩ ⟨_,ri⟩ (score.trans cap)
      have ct := BoundaryFiber.count G X 10 d vm wx vw dd lo
      rw [fr.size] at ct
      change B v≤(26-d).choose 10 at ct
      exact (Nat.add_le_add_left ct PendantRank.base).trans ((le_max_left ..).trans (Nat.le_add_right ..))
    · have ns : G.neighborFinset v⊆X := by
        intro a am
        by_contra na
        exact ext (mem_filter.mpr ⟨vm,a,na,(G.mem_neighborFinset ..).mp am⟩)
      have tu := inner_turan G vm ns free
      let j := RankTuran.floorD (rank' v)
      have js : j≤9 := by
        have tab : ∀r : Fin 26,RankTuran.floorD r≤9 := by decide
        exact tab ⟨_,ri⟩
      have jd : j≤G.degree v := by
        by_contra! short
        have cut := RankTuran.floor_ok.2 ⟨rank' v,by omega⟩ ⟨G.degree v,by omega⟩ deg3 short
        change (turanGraph (G.degree v) 3).edgeFinset.card<rank' v+2 at cut
        omega
      have raw (d : ℕ) (up : d<26) (dd : d≤G.degree v) : B v≤FiniteRange.badCount 26 10 d := by
        have ct := FiniteRange.count_bad G X 10 d v vm dd (by rw [fr.size]; exact up)
        rwa [fr.size] at ct
      apply le_trans _ (Nat.add_le_add_right (le_max_right ..) _)
      by_cases top : rank' v=1
      · rw [if_pos top]
        by_cases low : G.degree v=3
        · have sat : trianglesAt G v=(G.degree v).choose 2 := by
            rw [top] at score; rw [low] at cap ⊢; change trianglesAt G v≤3 at cap; change trianglesAt G v=3; omega
          have act : PendantRank.reward 3≤A v := PendantRank.fiber G X fr.size vm sat 9 3 low.ge (by decide)
          have cb := raw 3 (by decide) low.ge
          have rb : PendantRank.reward 3≤PendantRank.base := Nat.sub_le .. 
          have mx := le_max_right (PendantRank.base+FiniteRange.badCount 26 10 4)
            (PendantRank.base+FiniteRange.badCount 26 10 3-PendantRank.reward 3)
          omega
        · have cb := raw 4 (by decide) (by omega)
          exact (Nat.add_le_add_left cb PendantRank.base).trans ((le_max_left ..).trans (Nat.le_add_right ..))
      · rw [if_neg top]
        exact (Nat.add_le_add_left (raw j (by omega) jd) PendantRank.base).trans (Nat.le_add_right ..)
  have swap (f : Finset V→Finset V) (sub : ∀k∈X.powersetCard 10,f k⊆X) :
      (∑ k∈X.powersetCard 10,(f k).card)=∑v∈X,((X.powersetCard 10).filter (fun k => v∈f k)).card := by
    calc
      _ = ∑k∈X.powersetCard 10,∑v∈X,(if v∈f k then 1 else 0 : ℕ) := by
        apply sum_congr rfl; intro k km
        simp [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (sub k km)]
      _ = _ := by rw [sum_comm]; simp
  have mass := sum_le_sum each
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,fr.size] at mass
  rw [sum_by_rank X (trianglesAt G) fr.distinct,fr.size] at mass
  have cb := swap (FiniteRange.bad G X) (fun _ _ => (filter_subset ..).trans sdiff_subset)
  have ca := swap (PendantRank.active G X) (fun _ km => (filter_subset ..).trans (mem_powersetCard.mp km).1)
  change _=∑v∈X,B v at cb
  change _=∑v∈X,A v at ca
  rw [←cb,←ca] at mass
  have num : (∑i∈range 26,charge i)=26*PendantRank.base+15680531 := by
    unfold charge PendantRank.base PendantRank.reward FiniteRange.badCount Donor.rankDegree RankTuran.floorD
    simp only [Nat.choose_eq_fast_choose]
    decide
  rw [num] at mass
  have lower (k : Finset V) (km : k∈X.powersetCard 10) : 3+(PendantRank.active G X k).card≤(FiniteRange.bad G X k).card := by
    obtain ⟨sub,kb⟩ := mem_powersetCard.mp km
    have tr := PendantRank.trial G X k sub fr.distinct fr.exterior fr.separate fr.degree 0 (Or.inl rfl)
    have sz := fr.size
    have up := card_le_univ X
    omega
  have bound := sum_le_sum lower
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,card_powersetCard,fr.size] at bound
  rw [show (26:ℕ).choose 10=5311735 by decide] at bound
  omega

end Graffiti384b.PendantClose
#print axioms Graffiti384b.PendantClose.exact_frame
