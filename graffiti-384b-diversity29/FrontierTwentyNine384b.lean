import QuotaFinish29
import QuotaLocal29
import OddShore384b
import IsolateBasic384b
import DiversityThirty384b

namespace Graffiti384b.Quota29
open Finset SimpleGraph
open private Quota29.scarcity Quota29.single from ExposedQuota29
open private LowSample.two_degree from LowSample384b
open private OddQuota.core_data from OddQuota384b
open private Repair.linkEdges Repair.edge_info Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- With 28 high vertices, all neighbors of a degree-two vertex are
high. Every subfamily has precisely two distinct anchors per member. -/
theorem disjoint_anchors (t : (types G).card=29) (h : (high G).card=28) (fail : bound G<gamma G) :
    (∀ v∈LowSample.twos G,G.neighborFinset v⊆high G) ∧
    ∀ I⊆LowSample.twos G,(anchors G I).card=2*I.card := by
  classical
  have allH {v : V} (vm : v∈LowSample.twos G) : G.neighborFinset v⊆high G := by
    have z := Quota29.scarcity G t fail (singleton_subset_iff.mpr vm) (by
      intro a am b bm; rw [mem_singleton.mp am,mem_singleton.mp bm]; exact G.loopless _)
    rw [Quota29.single,card_singleton,h] at z
    have sub : (high G).filter (G.Adj v)⊆G.neighborFinset v := fun _ m => (G.mem_neighborFinset ..).mpr (mem_filter.mp m).2
    have equal := eq_of_subset_of_card_le sub (by
      rw [card_neighborFinset_eq_degree,LowSample.two_degree G vm]
      change 2≤nbr G v (high G); omega)
    rw [←equal]; exact filter_subset ..
  refine ⟨fun _ vm => allH vm,?_⟩
  intro I inc
  have ind (v : V) (vm : v∈I) (w : V) (wm : w∈I) (vw : G.Adj v w) : False :=
    (mem_sdiff.mp (inc wm)).2 (allH (inc vm) ((G.mem_neighborFinset ..).mpr vw))
  have low := Quota29.scarcity G t fail inc ind
  have asub : anchors G I⊆I.biUnion (fun v => G.neighborFinset v) := by
    intro z zm; obtain ⟨_,v,vm,vz⟩ := mem_filter.mp zm
    exact mem_biUnion.mpr ⟨v,vm,(G.mem_neighborFinset ..).mpr vz⟩
  have cap := (card_le_card asub).trans (card_biUnion_le (s:=I) (t:=fun v => G.neighborFinset v))
  have total : (∑ v∈I,(G.neighborFinset v).card)=2*I.card := by
    calc _ = ∑ _v∈I,2 := sum_congr rfl (fun v vm => (card_neighborFinset_eq_degree ..).trans (LowSample.two_degree G (inc vm)))
         _ = _ := by simp [Nat.mul_comm]
  omega

/-- An isolated vertex supplies the thirtieth type when every original
triangle count is positive. Its forced inclusion preserves the omissions. -/
theorem exact_of_no_zero (t : (types G).card=29) (zero : 0∉types G) : gamma G≤bound G := by
  have extend : (types (IsolateBasic.extend G)).card=30 := by
    rw [IsolateBasic.palette,card_insert_of_not_mem zero,t]
  have h := Diversity30.exact_thirty_types (IsolateBasic.extend G) extend
  unfold bound at h ⊢
  rw [IsolateBasic.domination,Fintype.card_sum,Fintype.card_unit,extend] at h
  rw [t]; omega

/-- Parameter ranges for the original graph, at every order. -/
theorem residual (t : (types G).card=29) (fail : bound G<gamma G) :
    0∈types G ∧ 27≤(high G).card ∧ (high G).card≤28 ∧
    28≤(nonleaves G).card ∧ (nonleaves G).card≤30 := by
  have lim := type_bound G
  have miss : ((high G).card+1)/2<((types G).card+1)/2 :=
    Nat.lt_of_not_ge (fun le => (not_lt_of_ge (exact_of_high G le)) fail)
  have q : (nonleaves G).card<31 := Nat.lt_of_not_ge (fun ge => (not_lt_of_ge (Finish.many_nonleaves G t ge)) fail)
  have lo : 28≤(nonleaves G).card := by
    by_contra! small
    have data := OddQuota.core_data G (show (nonleaves G).card<(types G).card by omega)
    have eq := data.1
    change (types G).card=(nonleaves G).card+1 at eq
    omega
  exact ⟨Classical.byContradiction (fun no => (not_lt_of_ge (exact_of_no_zero G t no)) fail),by omega,by omega,lo,by omega⟩

/-- Local version of RankTuran.local_turan, with the forbidden five-cliques
restricted to those through the specified center. -/
private theorem local_clique {v : V} (dv : G.degree v≤8)
    (big : RankTable.cap (G.degree v) 3<trianglesAt G v) : ∃ C,G.IsNClique 5 C ∧ v∈C := by
  classical
  by_contra! no
  let N := G.neighborFinset v
  let J := G.induce (N : Set V)
  let emb : N ↪ V := Function.Embedding.subtype _
  have cf : J.CliqueFree 4 := by
    intro q cl
    have lifted : G.IsNClique 4 (q.map emb) :=
      cl.map.mono (G.spanningCoe_induce_le (s := (N : Set V)))
    apply no (insert v (q.map emb)) ?_ (mem_insert_self ..)
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
  obtain ⟨M,dM,maximal⟩ := exists_isTuranMaximal (V := N) (by decide : 0<3)
  letI := dM
  have cap := maximal.2 J cf
  obtain ⟨iso⟩ := maximal.nonempty_iso_turanGraph
  have t : trianglesAt G v ≤ M.edgeFinset.card := (card_le_card cover).trans (card_image_le.trans cap)
  rw [iso.card_edgeFinset_eq,Fintype.card_coe] at t
  have bnd : trianglesAt G v≤(turanGraph (G.degree v) 3).edgeFinset.card := t
  have num := RankTable.cap_table ⟨G.degree v,by omega⟩ ⟨3,by decide⟩ (by decide)
  exact (not_lt_of_ge (bnd.trans_eq num)) big

/-- The upper remaining quota requires a five-clique through a center of
degree four through eight exceeding its tripartite Turán bound. -/
theorem boundary (t : (types G).card=29) (q : (nonleaves G).card=30) (fail : bound G<gamma G) :
    ∃ v,4≤G.degree v ∧ G.degree v≤8 ∧ RankTable.cap (G.degree v) 3<trianglesAt G v ∧
      ∃ C,G.IsNClique 5 C ∧ v∈C := by
  classical
  have witness : ∃ v,4≤G.degree v ∧ G.degree v≤8 ∧ RankTable.cap (G.degree v) 3<trianglesAt G v := by
    by_contra! no
    apply (not_lt_of_ge (Local.exact_of_local_cap G t q.ge ?_)) fail
    intro v d
    by_cases lo : 4≤G.degree v
    · exact no v lo d
    · have cap : (G.degree v).choose 2=RankTable.cap (G.degree v) 3 :=
        (show ∀ d : Fin 4,d.val.choose 2=RankTable.cap d.val 3 by decide) ⟨G.degree v,by omega⟩
      exact (Repair.triangles_le_choose G v).trans_eq cap
  obtain ⟨v,lo,hi,sc⟩ := witness
  exact ⟨v,lo,hi,sc,local_clique G hi sc⟩

/-- Every connected failure with 29 types has an induced connected
failure of order 29, 30 or 31 with the identical triangle-count palette. -/
theorem induced (conn : G.Connected) (t : (types G).card=29) (fail : bound G<gamma G) :
    ∃ S : Finset V,29≤S.card ∧ S.card≤31 ∧ (G.induce (S:Set V)).Connected ∧
      types (G.induce (S:Set V))=types G ∧ bound (G.induce (S:Set V))<gamma (G.induce (S:Set V)) := by
  have full : (types G).card≤Fintype.card V := (card_image_le (s:=(univ:Finset V)) (f:=trianglesAt G)).trans_eq card_univ
  obtain ⟨S,_,cap,_,connected,same,bad⟩ := Prune.prune_failure G conn (by omega) fail
  have count : (types (G.induce (S:Set V))).card≤S.card := by
    simpa only [types,card_univ,Fintype.card_coe] using
      (card_image_le (s:=(univ:Finset S)) (f:=trianglesAt (G.induce (S:Set V))))
  have maxQ := (residual G t fail).2.2.2.2
  rw [same,t] at count
  exact ⟨S,count,by omega,connected,same,bad⟩

/-- The 28-nonleaf case requires a 28-vertex core of 2-domination
number fourteen. All its triangle-edge components have even order. -/
theorem minimum (t : (types G).card=29) (q : (nonleaves G).card=28) (fail : bound G<gamma G) :
    let P := nonleaves G
    let H := G.induce (P:Set V)
    (∀ v,0<trianglesAt H v) ∧ Function.Injective (trianglesAt H) ∧ gamma H=14 ∧
      ∀ S : Finset P,OddQuota.TriangleClosed H S → S.card%2=0 := by
  let P := nonleaves G
  let H := G.induce (P:Set V)
  obtain ⟨pos,fi,eq⟩ := OddQuota.core_of_failure G (by omega) (by omega) fail
  change 2*gamma H=P.card at eq
  change P.card=28 at q
  change (∀ v,0<trianglesAt H v) ∧ Function.Injective (trianglesAt H) ∧ gamma H=14 ∧ _
  exact ⟨pos,fi,by omega,fun S cl => OddQuota.even_shore H pos fi ((Fintype.card_coe P).le.trans eq.ge) S cl⟩

end Graffiti384b.Quota29
#print axioms Graffiti384b.Quota29.disjoint_anchors
#print axioms Graffiti384b.Quota29.exact_of_no_zero
#print axioms Graffiti384b.Quota29.residual
#print axioms Graffiti384b.Quota29.boundary
#print axioms Graffiti384b.Quota29.induced
#print axioms Graffiti384b.Quota29.minimum
