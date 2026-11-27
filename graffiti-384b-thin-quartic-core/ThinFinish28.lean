import ThinCharges28

namespace Graffiti384b.Thin28
open Finset SimpleGraph HighEar JointRank Core28
open private ThreeChoice.balance from ThreeBudget33
open private Repair.full_nbr from Repair384b
open private Four28.core_data Four28.ear_one from FourFrontier28
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

set_option maxHeartbeats 1500000 in
/-- A unique common neighbor allows two complementary trials: keep the
two endpoints with eight exterior vertices, or keep the ear with ten. -/
theorem no_square_saving (n : Fintype.card V=28) (pos : ∀ v,0<trianglesAt H v)
    (fi : Function.Injective (trianglesAt H)) (free : H.CliqueFree 5) {e p q : V}
    (pq : H.Adj p q) (en : H.neighborFinset e={p,q}) (thin : additional H e p q=∅) :
    gamma H≤13 := by
  classical
  have ep : H.Adj e p := (H.mem_neighborFinset ..).mp (en ▸ mem_insert_self ..)
  have eq' : H.Adj e q := (H.mem_neighborFinset ..).mp (en ▸ mem_insert_of_mem (mem_singleton_self _))
  have one := Four28.ear_one H pq.ne en pos
  let U := (univ : Finset V).erase e
  let P : Finset V := {p,q}
  let W := (insert e P)ᶜ
  let r := rank U (trianglesAt H)
  let mass (v : V) := 3*hit H W P 8 v+hit H W {e} 10 v
  have pu : p∈U := by simp [U,ep.ne.symm]
  have qu : q∈U := by simp [U,eq'.ne.symm]
  have es : e∉P := by simp [P,ep.ne,eq'.ne]
  have pp : p∈P := mem_insert_self ..
  have qp : q∈P := mem_insert_of_mem (mem_singleton_self _)
  have psub : P⊆U := insert_subset pu (singleton_subset_iff.mpr qu)
  have dis : Disjoint P W := disjoint_left.mpr (fun v vp vw => mem_compl.mp vw (mem_insert_of_mem vp))
  have ew : e∉W := fun h => mem_compl.mp h (mem_insert_self ..)
  have wp : p∉W := disjoint_left.mp dis pp
  have wq : q∉W := disjoint_left.mp dis qp
  have diff : U\P=W := by ext z; simp [W,U,not_or]
  have wu : W⊆U := diff ▸ sdiff_subset
  have ps : P.card=2 := card_pair pq.ne
  have ws : W.card=25 := by rw [show W=(insert e P)ᶜ from rfl,card_compl,card_insert_of_not_mem es,ps,n]
  have us : U.card=27 := by simp [U,n]
  have range' (v : V) (vm : v∈U) : r v<27 := by
    have h := mem_image_of_mem (rank U (trianglesAt H)) vm
    rwa [rank_range _ _ fi.injOn,us,mem_range] at h
  have lower (v : V) (vm : v∈U) : r v+2≤trianglesAt H v := by
    have base (z : V) (zm : z∈U) : 2≤trianglesAt H z := by
      have ne := (mem_erase.mp zm).1
      have nz : trianglesAt H z≠1 := fun h => ne (fi (h.trans one.symm))
      have := pos z; omega
    exact (Nat.add_comm ..).le.trans (rank_lower U (trianglesAt H) fi.injOn 2 base vm)
  have per (v : V) (vm : v∈W) : mass v+205000*nbr H v P≤price (r v) := by
    have ve := (mem_erase.mp (wu vm)).1
    have non : ¬H.Adj v e := by
      intro h
      have m := (H.mem_neighborFinset ..).mpr h.symm
      rw [en] at m
      exact disjoint_left.mp dis m vm
    have only : nbr H v P≤1 := by
      apply Nat.le_of_not_gt
      intro big
      have same : P.filter (H.Adj v)=P := eq_of_subset_of_card_le (filter_subset ..) (by
        change P.card≤nbr H v P; omega)
      have vp := (mem_filter.mp ((by rw [same]; exact pp) : p∈P.filter (H.Adj v))).2
      have vq := (mem_filter.mp ((by rw [same]; exact qp) : q∈P.filter (H.Adj v))).2
      have m := (additional_mem H).mpr ⟨ve,vp.symm,vq.symm⟩
      simp [thin] at m
    have dg := Repair.full_nbr H v W
    have ext : nbr H v Wᶜ=nbr H v P := by
      simp only [W,compl_compl,nbr,Finset.filter_insert,non,if_false]
    rw [ext] at dg
    exact exterior_charge H ws vm dis only dg free ⟨r v,range' v (wu vm)⟩ (lower v (wu vm))
  have capP := thin_endpoint H en pq thin
  have thinQ : additional H e q p=∅ := by simpa only [additional,inter_comm] using thin
  have capQ := thin_endpoint H (en.trans (pair_comm ..)) pq.symm thinQ
  change trianglesAt H p≤1+(nbr H p W).choose 2 at capP
  have capQ' : trianglesAt H q≤1+(nbr H q W).choose 2 := by
    simpa only [W,P,pair_comm q p] using capQ
  have node {v : V} (vp : v∈P) (vu : v∈U) (ev : H.Adj e v)
      (cap : trianglesAt H v≤1+(nbr H v W).choose 2) :
      mass v+1734380≤price (r v)+205000*nbr H v W := by
    have vw : v∉W := disjoint_left.mp dis vp
    have a := kept H (W:=W) (b:=8) vp
    have b := credited H (b:=10) (mem_singleton_self e) ew ev.symm
    rw [ws,if_neg vw,Nat.sub_zero] at b
    have bs : nbr H v W≤25 := (card_filter_le ..).trans ws.le
    have row := endpoint_rows ⟨r v,range' v vu⟩ ⟨nbr H v W,by omega⟩ ((lower v vu).trans cap)
    change (25-nbr H v W).choose 10+1734380≤price (r v)+205000*nbr H v W at row
    dsimp only [mass]
    rw [a]; omega
  have left := node pp pu ep capP
  have right := node qp qu eq' capQ'
  have entire := sum_le_sum per
  simp only [sum_add_distrib,←mul_sum] at entire
  have counts := ThreeChoice.balance H P W
  rw [show (∑ a∈P,nbr H a W)=nbr H p W+nbr H q W from sum_pair pq.ne] at counts
  rw [counts] at entire
  have unionSum (g : V → ℕ) : (∑ w∈W,g w)+(g p+g q)=∑ w∈U,g w := by
    have h := sum_sdiff psub (f:=g)
    rw [diff,show (∑ w∈P,g w)=g p+g q from sum_pair pq.ne] at h
    exact h
  have zero : mass e=0 := by simp [mass,covered H pq.ne ep eq' pp qp,kept H (P:={e}) (mem_singleton_self e)]
  have allmass := sum_erase_add (univ : Finset V) mass (mem_univ e)
  change (∑ w∈U,mass w)+mass e=∑ w,mass w at allmass
  rw [zero,Nat.add_zero,←unionSum] at allmass
  have rankcost := sum_by_rank U (trianglesAt H) fi.injOn price
  rw [us,total_price] at rankcost
  change (∑ w∈U,price (r w))=26237251 at rankcost
  rw [←unionSum] at rankcost
  have upper : (∑ w,mass w)+2*1734380≤26237251 := by omega
  apply Nat.le_of_not_gt
  intro fail
  have b8 := budget H W P 8
  have b10 := budget H W {e} 10
  rw [ws,ps] at b8
  rw [ws,card_singleton] at b10
  have l8 : 4≤gamma H-2-8 := by omega
  have l10 : 3≤gamma H-1-10 := by omega
  have m8 := (Nat.mul_le_mul_left ((25:ℕ).choose 8) l8).trans b8
  have m10 := (Nat.mul_le_mul_left ((25:ℕ).choose 10) l10).trans b10
  have enough := Nat.add_le_add (Nat.mul_le_mul_left 3 m8) m10
  change 22785180≤_ at enough
  simp only [mass,sum_add_distrib,←mul_sum] at upper
  omega

theorem exact_no_ear_square (t : (types H).card=29) (q : (nonleaves H).card=28) :
    let J := triangleEdges (H.induce (nonleaves H:Set V))
    J.CliqueFree 5 → ∀ e a b,J.Adj a b → J.neighborFinset e={a,b} →
      additional J e a b=∅ → gamma H≤bound H := by
  dsimp only
  intro free e a b ab en thin
  by_contra! bad
  let J := triangleEdges (H.induce (nonleaves H:Set V))
  obtain ⟨n,pos,fi,half,_⟩ := Four28.core_data H t q bad
  have win := no_square_saving J n pos fi free ab en thin
  exact (Nat.not_succ_le_self 13) (half.trans win)

end Graffiti384b.Thin28
#print axioms Graffiti384b.Thin28.no_square_saving
#print axioms Graffiti384b.Thin28.exact_no_ear_square
