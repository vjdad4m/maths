import PaletteFibers33

namespace Graffiti384b.EarPalette
open Finset SimpleGraph JointRank HighEar EarAnchor
open private FiniteRange.bad from FiniteRange384b
open private Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Removing the reserved score closes the gap in the triangle-count ranks. -/
private def compress (skip j : ℕ) := if j<skip then j else j-1

theorem sparse_sample {W U : Finset V} {skip : ℕ} (rare : skip=4 ∨ skip=5) (us : U.card=27) (ws : W.card=29) (sub : U⊆W)
    (cap : ∀ v∈U,(∀ w,w∉W → ¬H.Adj v w) → trianglesAt H v≤(turanGraph (H.degree v) 3).edgeFinset.card)
    (inj : Function.Injective (trianglesAt H))
    (scores : ∀ v∈U,2≤trianglesAt H v ∧ trianglesAt H v≠skip) :
    ∃ k∈W.powersetCard 10,((FiniteRange.bad H W k)∩U).card≤3 := by
  classical
  let f := fun v => compress skip (trianglesAt H v)
  have fi : Set.InjOn f (U : Set V) := by
    intro u um v vm eq
    apply inj
    have ⟨_,a⟩ := scores u um
    have ⟨_,b⟩ := scores v vm
    change compress skip (trianglesAt H u)=compress skip (trianglesAt H v) at eq
    unfold compress at eq; split_ifs at eq <;> omega
  have low (v : V) (vm : v∈U) : 2≤f v := by
    have ⟨_,_⟩ := scores v vm
    change 2≤compress skip (trianglesAt H v); unfold compress; split_ifs <;> omega
  let r := rank U f
  let opts := W.powersetCard 10
  let fail := fun k => FiniteRange.bad H W k
  let fiber := fun v => (opts.filter (fun k => v∈fail k)).card
  have per (v : V) (vm : v∈U) : fiber v≤cost (r v) := by
    have valid := mem_image_of_mem (rank U f) vm
    rw [rank_range U f fi,us] at valid
    have lo := rank_lower U f fi 2 low vm
    change 2+r v≤compress skip (trianglesAt H v) at lo
    have ⟨_,gap⟩ := scores v vm
    have score : threshold (r v)≤trianglesAt H v := by
      unfold threshold; unfold compress at lo
      split_ifs at * <;> omega
    exact rank_fiber H ws (sub vm) (cap v vm) (mem_range.mp valid) score
  have total : (∑ k∈opts,((fail k)∩U).card)=∑ v∈U,fiber v := by
    calc _ = ∑ k∈opts,∑ v∈U,if v∈fail k then 1 else 0 := by
           apply sum_congr rfl; intro k _
           simp [sum_boole,filter_mem_eq_inter,inter_comm]
         _ = _ := by rw [sum_comm]; simp [fiber,sum_boole]
  have lim := sum_le_sum per
  change (∑ v∈U,fiber v)≤∑ v∈U,cost (rank U f v) at lim
  rw [sum_by_rank U f fi cost,us] at lim
  by_contra! none
  have lots : (∑ _k∈opts,4)≤∑ k∈opts,((fail k)∩U).card := sum_le_sum (fun k km => none k km)
  have size : opts.card=(29:ℕ).choose 10 := by rw [show opts=W.powersetCard 10 from rfl,card_powersetCard,ws]
  rw [total] at lots
  simp only [sum_const,nsmul_eq_mul,size,Nat.cast_id] at lots
  have strict := sum_cost
  omega

/-- Retain the two ear endpoints, sample ten of the 29 remaining non-ear
vertices and add at most three deficient vertices. The two shared neighbors
and the ear see both retained vertices for every sample. -/
theorem sampled_bound {e a c s t : V} (n : Fintype.card V=32) (ear : H.neighborFinset e={a,c})
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (as' : H.Adj a s) (cs : H.Adj c s) (se : s≠e) (at' : H.Adj a t) (ct : H.Adj c t) (te : t≠e)
    (st : s≠t) {skip : ℕ} (rare : skip=4 ∨ skip=5)
    (reserved : ∃ w∈({a,c,s,t}:Finset V),trianglesAt H w=skip) (one : trianglesAt H e=1)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (hit : ∀ C,H.IsNClique 5 C → a∈C ∨ c∈C) : gamma H≤15 := by
  classical
  let W := outside e a c
  let U := W\{s,t}
  have ws : W.card=29 := by simp [W,outside,card_compl,ea.ne,ec.ne,ac.ne,n]
  have sm : s∈W := outside_mem.mpr ⟨se,as'.ne.symm,cs.ne.symm⟩
  have tm : t∈W := outside_mem.mpr ⟨te,at'.ne.symm,ct.ne.symm⟩
  have sz : U.card=27 := by
    rw [show U=W\{s,t} from rfl,card_sdiff (insert_subset sm (singleton_subset_iff.mpr tm)),ws,card_pair st]
  have outs {v : V} (vm : v∈W) : ¬H.Adj v e := by
    intro edge
    have m := (H.mem_neighborFinset _ _).mpr edge.symm
    rw [ear] at m
    exact (mem_insert.mp m).elim (outside_mem.mp vm).2.1 (fun h => (outside_mem.mp vm).2.2 (mem_singleton.mp h))
  have scores (v : V) (vm : v∈U) : 2≤trianglesAt H v ∧ trianglesAt H v≠skip := by
    have ⟨ve,va,_⟩ := outside_mem.mp (mem_sdiff.mp vm).1
    have diff : trianglesAt H v≠1 := fun h => ve (inj (h.trans one.symm))
    have po := pos v
    refine ⟨by omega,?_⟩
    intro h
    obtain ⟨w,wm,ranked⟩ := reserved
    have vw := inj (h.trans ranked.symm)
    have here : v∈({a,c,s,t}:Finset V) := vw ▸ wm
    rcases mem_insert.mp here with eq|rest
    · exact va eq
    rcases mem_insert.mp rest with eq|pair
    · exact (outside_mem.mp (mem_sdiff.mp vm).1).2.2 eq
    · exact (mem_sdiff.mp vm).2 pair
  have cap (v : V) (vm : v∈U) (away : ∀ w,w∉W → ¬H.Adj v w) :
      trianglesAt H v≤(turanGraph (H.degree v) 3).edgeFinset.card := by
    have part := outside_mem.mp (mem_sdiff.mp vm).1
    exact pair_turan H ac.ne part.2.1 part.2.2
      (away _ (fun m => (outside_mem.mp m).2.1 rfl)) (away _ (fun m => (outside_mem.mp m).2.2 rfl)) hit
  obtain ⟨k,km,small⟩ := sparse_sample H rare sz ws sdiff_subset cap inj scores
  obtain ⟨kw,kb⟩ := mem_powersetCard.mp km
  let bad := (FiniteRange.bad H W k)∩U
  let D := ({a,c}:Finset V)∪k∪bad
  have am : a∈D := mem_union_left _ (mem_union_left _ (mem_insert_self ..))
  have cm : c∈D := mem_union_left _ (mem_union_left _ (mem_insert_of_mem (mem_singleton_self _)))
  have fixed {v : V} (va : H.Adj v a) (vc : H.Adj v c) : 2≤nbr H v D :=
    PinnedColor34.two H ac.ne va vc am cm
  have dom : TwoDominates H D := by
    intro v out
    by_cases ve : v=e
    · exact ve ▸ fixed ea ec
    have va : v≠a := fun h => out (h ▸ am)
    have vc : v≠c := fun h => out (h ▸ cm)
    have vm : v∈W := outside_mem.mpr ⟨ve,va,vc⟩
    by_cases vs : v=s
    · exact vs ▸ fixed as'.symm cs.symm
    by_cases vt : v=t
    · exact vt ▸ fixed at'.symm ct.symm
    have vu : v∈U := mem_sdiff.mpr ⟨vm,by simp [vs,vt]⟩
    have notk : v∉k := fun h => out (mem_union_left _ (mem_union_right _ h))
    have ok : 2≤nbr H v (Wᶜ∪k) := by
      apply Nat.le_of_not_gt; intro low
      exact out (mem_union_right _ (mem_inter.mpr ⟨mem_filter.mpr ⟨mem_sdiff.mpr ⟨vm,notk⟩,low⟩,vu⟩))
    apply ok.trans; apply card_le_card; intro w wm
    obtain ⟨where_,edge⟩ := mem_filter.mp wm
    refine mem_filter.mpr ⟨?_,edge⟩
    rcases mem_union.mp where_ with extW|wk
    · have outsideW : w=e ∨ w=a ∨ w=c := by simpa [W,outside] using extW
      rcases outsideW with eq|eq|eq
      · exact (outs vm (eq ▸ edge)).elim
      · exact eq ▸ am
      · exact eq ▸ cm
    · exact mem_union_left _ (mem_union_right _ wk)
  have up : gamma H≤D.card := Nat.sInf_le ⟨D,dom,rfl⟩
  have h₁ := card_union_le ({a,c}:Finset V) k
  have h₂ := card_union_le (({a,c}:Finset V)∪k) bad
  rw [card_pair ac.ne,kb] at h₁
  change bad.card≤3 at small
  change gamma H≤((({a,c}:Finset V)∪k)∪bad).card at up
  omega

end Graffiti384b.EarPalette
#print axioms Graffiti384b.EarPalette.sparse_sample
#print axioms Graffiti384b.EarPalette.sampled_bound
