import SinglePrice28

namespace Graffiti384b.HighSquare28
open Finset SimpleGraph HighEar JointRank Thin28
open private ThreeChoice.balance from ThreeBudget33
open private Repair.full_nbr from Repair384b
open private Four28.ear_one from FourFrontier28
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

set_option maxHeartbeats 1600000 in
theorem one_external_cubic (n : Fintype.card V=28) (pos : ∀ v,0<trianglesAt H v)
    (fi : Function.Injective (trianglesAt H)) (free : H.CliqueFree 5) {e p q s u : V}
    (pq : H.Adj p q) (en : H.neighborFinset e={p,q}) (single : additional H e p q={s})
    (ds : 5≤H.degree s) (dp : 4≤H.degree p) (dq : 4≤H.degree q)
    (du : H.degree u=3) (off : u∉({e,p,q}:Finset V))
    (unique : ∀ v,v∉({e,p,q}:Finset V) → H.degree v=3 → v=u) :
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
  have uw : u∈W := mem_compl.mpr off
  have sm : s∈additional H e p q := single ▸ mem_singleton_self _
  obtain ⟨se,sp,sq⟩ := (additional_mem H).mp sm
  have sw : s∈W := by simp [W,P,se,sp.ne.symm,sq.ne.symm]
  have per (v : V) (vm : v∈W) : mass v+205000*nbr H v P≤residualPrice (r v)+
      (if v=u then 726750 else 0)+(if v=s then 292516 else 0) := by
    have non : ¬H.Adj v e := by
      intro h; have m := (H.mem_neighborFinset ..).mpr h.symm
      rw [en] at m
      exact disjoint_left.mp dis m vm
    have ve := (mem_erase.mp (wu vm)).1
    have both (h : nbr H v P=2) : v=s := by
      have eq : P.filter (H.Adj v)=P := eq_of_subset_of_card_le (filter_subset ..) (by
        change P.card≤nbr H v P; rw [h,ps])
      have vp := (mem_filter.mp ((by rw [eq]; exact pp) : p∈P.filter (H.Adj v))).2
      have vq := (mem_filter.mp ((by rw [eq]; exact qp) : q∈P.filter (H.Adj v))).2
      exact mem_singleton.mp (single ▸ (additional_mem H).mpr ⟨ve,vp.symm,vq.symm⟩)
    have dg := Repair.full_nbr H v W
    have ext : nbr H v Wᶜ=nbr H v P := by
      simp only [W,compl_compl,nbr,Finset.filter_insert,non,if_false]
    rw [ext] at dg
    have row := single_charge H (e:=e) ws vm dis ps free dg
      (fun h => both h ▸ ds) ⟨r v,range' v (wu vm)⟩ (lower v (wu vm))
    have c : H.degree v=3 → v=u := unique v (mem_compl.mp vm)
    dsimp only [mass]
    have z₁ : (if H.degree v=3 then 726750 else 0)≤(if v=u then 726750 else 0) := by
      by_cases d : H.degree v=3
      · rw [if_pos d,if_pos (c d)]
      · rw [if_neg d]; exact Nat.zero_le _
    have z₂ : (if nbr H v P=2 then 292516 else 0)≤(if v=s then 292516 else 0) := by
      by_cases d : nbr H v P=2
      · rw [if_pos d,if_pos (both d)]
      · rw [if_neg d]; exact Nat.zero_le _
    exact row.trans (Nat.add_le_add (Nat.add_le_add_left z₁ _) z₂)
  have singleQ : additional H e q p={s} := by simpa only [additional,inter_comm] using single
  obtain ⟨dgP,capP⟩ := endpoint_limit H en pq single
  have swapped := endpoint_limit H (en.trans (pair_comm ..)) pq.symm singleQ
  have hq : nbr H q W+2=H.degree q ∧ trianglesAt H q≤2+(nbr H q W).choose 2 := by
    simpa only [W,P,pair_comm q p] using swapped
  obtain ⟨dgQ,capQ⟩ := hq
  change nbr H p W+2=H.degree p at dgP
  change trianglesAt H p≤2+(nbr H p W).choose 2 at capP
  have ap : 2≤nbr H p W := by omega
  have aq : 2≤nbr H q W := by omega
  have sep : nbr H p W≠2 ∨ nbr H q W≠2 := by
    by_cases lp : nbr H p W=2
    · right
      intro lq
      rw [lp,Nat.choose_self] at capP
      rw [lq,Nat.choose_self] at capQ
      have su := cubic_scores H (e:=e) (by rw [←card_neighborFinset_eq_degree,en,card_pair pq.ne]) du pos fi
      have lowP := lower p pu
      have lowQ := lower q qu
      have distinct : trianglesAt H p≠trianglesAt H q := fun h => pq.ne (fi h)
      have uP : trianglesAt H u≠trianglesAt H p := fun h => wp (fi h ▸ uw)
      have uQ : trianglesAt H u≠trianglesAt H q := fun h => wq (fi h ▸ uw)
      omega
    · exact Or.inl lp
  have node {v : V} (vp : v∈P) (vu : v∈U) (ev : H.Adj e v) (small : 2≤nbr H v W)
      (cap : trianglesAt H v≤2+(nbr H v W).choose 2) :
      mass v+fee (nbr H v W)≤residualPrice (r v)+205000*nbr H v W := by
    have vw : v∉W := disjoint_left.mp dis vp
    have a := kept H (W:=W) (b:=8) vp
    have b := credited H (b:=10) (mem_singleton_self e) ew ev.symm
    rw [ws,if_neg vw,Nat.sub_zero] at b
    have bs : nbr H v W≤25 := (card_filter_le ..).trans ws.le
    have row := end_rows ⟨r v,range' v vu⟩ ⟨nbr H v W,by omega⟩ small ((lower v vu).trans cap)
    change (25-nbr H v W).choose 10+fee (nbr H v W)≤residualPrice (r v)+205000*nbr H v W at row
    dsimp only [mass]
    rw [a]; omega
  have left := node pp pu ep ap capP
  have right := node qp qu eq' aq capQ
  have fees : 3035850≤fee (nbr H p W)+fee (nbr H q W) := by
    unfold fee; split_ifs <;> omega
  have entire := sum_le_sum per
  simp only [sum_add_distrib,←mul_sum] at entire
  simp only [sum_ite_eq',uw,sw,ite_true] at entire
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
  have rankcost := sum_by_rank U (trianglesAt H) fi.injOn residualPrice
  rw [us,totals.2] at rankcost
  change (∑ w∈U,residualPrice (r w))=24783751 at rankcost
  rw [←unionSum] at rankcost
  have upper : (∑ w,mass w)≤22767167 := by omega
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

end Graffiti384b.HighSquare28
#print axioms Graffiti384b.HighSquare28.one_external_cubic
