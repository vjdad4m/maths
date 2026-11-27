import RemoteSquareEvenScaffold
import RemoteGapRunPacking

namespace KelmansCactus.AtomicBridge.RemoteSquareRankFactor
open SimpleGraph
open scoped Sym2
open RemoteSquareConvergence RemoteSquareEvenScaffold
open RemoteGapRunPacking (run_factor)
open SquareCap (HasFactor)
variable {V I : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem closed_tail_membership {G : SimpleGraph V} {u x : V}
    {p : G.Walk u u} (h : ¬p.Nil) : x∈p.support ↔ x∈p.support.tail := by
  constructor
  · intro hx
    rw [p.support_eq_cons,List.mem_cons] at hx
    rcases hx with rfl|hx
    · exact p.end_mem_tail_support h
    · exact hx
  · exact List.mem_of_mem_tail

/-- Elementary bridge to the run-packing layer: a connected finite degree-two graph
gives a single spanning, nonrepeating route. No factoring hypothesis is used. -/
theorem spanning_run_of_two_regular (G : SimpleGraph V) [DecidableRel G.Adj]
    (regular : ∀ x,G.degree x=2) (con : G.Preconnected) :
    ∃ L : List V,L.Nodup ∧ L.Chain' G.Adj ∧ L.toFinset=Finset.univ := by
  rcases isEmpty_or_nonempty V with isEmpty|nonempty
  · refine ⟨[],by simp,by simp,?_⟩
    ext x
    exact (isEmpty.false x).elim
  rcases nonempty with ⟨a⟩
  have pos : 0<G.degree a := by rw [regular]; decide
  obtain ⟨b,bm⟩ := Finset.card_pos.mp pos
  have adj : G.Adj a b := (SimpleGraph.mem_neighborFinset _ _ _).mp bm
  have alt := even_degree_alternate G (fun x=>by rw [regular]; decide) adj
  obtain ⟨u,p,pc,ep⟩ := SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle.mp ⟨adj,alt⟩
  clear ep
  have closed {x y : V} (xmem : x∈p.support) (xy : G.Adj x y) : y∈p.support := by
    let q := p.rotate xmem
    have qc : q.IsCycle := pc.rotate xmem
    have supmap {z : V} (hz : z∈q.support) : z∈p.support :=
      (closed_tail_membership pc.not_nil).mpr
        ((p.support_rotate xmem).mem_iff.mp ((closed_tail_membership qc.not_nil).mp hz))
    have aa : G.Adj x q.snd := q.adj_snd qc.not_nil
    have bb : G.Adj x q.penultimate := (q.adj_penultimate qc.not_nil).symm
    have ne : q.snd≠q.penultimate := qc.snd_ne_penultimate
    have allN : G.neighborFinset x = {q.snd,q.penultimate} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro z zm
        simp only [Finset.mem_insert,Finset.mem_singleton] at zm
        rcases zm with rfl|rfl
        · exact (SimpleGraph.mem_neighborFinset _ _ _).mpr aa
        · exact (SimpleGraph.mem_neighborFinset _ _ _).mpr bb
      · rw [SimpleGraph.card_neighborFinset_eq_degree,regular]
        simp [ne]
    have m : y ∈ G.neighborFinset x := (SimpleGraph.mem_neighborFinset _ _ _).mpr xy
    rw [allN] at m
    simp only [Finset.mem_insert,Finset.mem_singleton] at m
    rcases m with rfl|rfl
    · exact supmap (q.getVert_mem_support 1)
    · exact supmap (q.getVert_mem_support (q.length-1))
  have all (x : V) : x∈p.support := by
    have reach := con u x
    rw [SimpleGraph.reachable_iff_reflTransGen] at reach
    induction reach with
    | refl => exact p.start_mem_support
    | tail _ e ih => exact closed ih e
  refine ⟨p.support.tail,pc.support_nodup,?_,?_⟩
  · exact p.chain'_adj_support.tail
  · ext x
    simp only [List.mem_toFinset,Finset.mem_univ,iff_true]
    exact (closed_tail_membership pc.not_nil).mp (all x)

theorem factor_of_two_regular_preconnected (G : SimpleGraph V) [DecidableRel G.Adj]
    (regular : ∀ x,G.degree x=2) (con : G.Preconnected) (size : 3∣Fintype.card V) :
    HasFactor G := by
  obtain ⟨L,nod,run,covers⟩ := spanning_run_of_two_regular G regular con
  have eq : L.length=Fintype.card V := by
    rw [← List.toFinset_card_of_nodup nod,covers,Finset.card_univ]
  rw [←eq] at size
  have f := run_factor L nod run size
  rwa [covers] at f

def TwoRegular (G : SimpleGraph V) : Prop :=
  ∃ _ : DecidableRel G.Adj, ∀ x,G.degree x=2

/-- Applicable after subdividing any fixed marked edges already present in the base
graph. Each rank choice is 2-regular; a connected union then chooses rank paths
covering the whole ambient graph in triples. -/
theorem square_rank_factor [DecidableEq I] (G B : SimpleGraph V) (gates : I→Quad V)
    (sub : unionNetwork B gates ≤ G)
    (reg : ∀ s, TwoRegular (network B gates s))
    (conn : (unionNetwork B gates).Preconnected) (size : 3∣Fintype.card V)
    (start : I→Bool) :
    ∃ final, HasFactor (network B gates final) ∧ HasFactor G := by
  have ok : CanBypass B gates := by
    apply bypass_of_alternate
    intro s i
    obtain ⟨inst,deg⟩ := reg s
    letI := inst
    rcases present_edges B gates s i with ⟨a,b⟩
    exact ⟨even_degree_alternate _ (fun x=>by rw [deg]; decide) a,
      even_degree_alternate _ (fun x=>by rw [deg]; decide) b⟩
  obtain ⟨f,_,all⟩ := square_convergence B gates ok start
  obtain ⟨inst,deg⟩ := reg f
  letI := inst
  have hf : HasFactor (network B gates f) :=
    factor_of_two_regular_preconnected _ deg (fun x y=>(all x y).mpr (conn x y)) size
  obtain ⟨pack,legal,apart,covers⟩ := hf
  exact ⟨f,⟨pack,legal,apart,covers⟩,pack,fun R m=>by
    obtain ⟨ct,c,cm,adjs⟩ := legal R m
    exact ⟨ct,c,cm,fun x xm ne=>sub ((network_le_union B gates f) (adjs x xm ne))⟩,apart,covers⟩

#print axioms spanning_run_of_two_regular
#print axioms factor_of_two_regular_preconnected
#print axioms square_rank_factor
end KelmansCactus.AtomicBridge.RemoteSquareRankFactor
