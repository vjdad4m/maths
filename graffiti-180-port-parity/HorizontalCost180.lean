import OddCutBudget180

set_option warningAsError true
namespace Minimal180.PortParity
open Finset SimpleGraph Graffiti177 Graffiti318 Graffiti180 Rooted180 Converse180 Assembly180 HigherRank
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact degree and leaf accounting in any tree with independent
complement of P. Each edge inside P enters the identity exactly once. -/
theorem horizontal_identity (T : SimpleGraph V) [DecidableRel T.Adj] (tr : T.IsTree)
    (hn : 1<Fintype.card V) (P : Finset V) (ind : Indep T (univ\P)) :
    Fintype.card V+(leaves T).card+(T.edgeFinset∩P.sym2).card=
      2*P.card+1+(leaves T\P).card+(∑ v∈P,(T.degree v-2)) := by
  classical
  let O : Finset V := univ\P
  have cover : O.biUnion (fun v => T.incidenceFinset v)=T.edgeFinset\P.sym2 := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [O,mem_biUnion,incidenceFinset_eq_filter,mem_filter,mem_edgeFinset,Sym2.mem_iff,
        mem_sdiff,mem_univ,true_and,mk_mem_sym2_iff]
      constructor
      · rintro ⟨v,out,h,eq|eq⟩ <;> subst v <;> tauto
      · rintro ⟨edge,out⟩
        by_cases ap : a∈P
        · exact ⟨b,fun bp => out ⟨ap,bp⟩,edge,Or.inr rfl⟩
        · exact ⟨a,ap,edge,Or.inl rfl⟩
  have mass := independent_mass T O ind
  rw [cover] at mass
  have splitE := card_sdiff_add_card_inter T.edgeFinset P.sym2
  have dis : Disjoint P O := disjoint_left.mpr (fun _ a b => (mem_sdiff.mp b).2 a)
  have union : P∪O=univ := by ext x; simp [O]
  have decomp : (∑ v∈P∪O,T.degree v)=(∑ v∈P,T.degree v)+(∑ v∈O,T.degree v) := sum_union dis
  rw [union,T.sum_degrees_eq_twice_card_edges,mass] at decomp
  have point (v : V) : T.degree v+(if v∈leaves T then 1 else 0)=2+(T.degree v-2) := by
    obtain ⟨w,e⟩ := exists_adj T tr.isConnected hn v
    have pos := (T.degree_pos_iff_exists_adj v).mpr ⟨w,e⟩
    have lf : v∈leaves T ↔ T.degree v=1 := by simp [leaves,SimpleGraph.degree,SimpleGraph.neighborFinset]
    split_ifs with h
    · have := lf.mp h; omega
    · have := mt lf.mpr h; omega
  have sum : (∑ v∈P,(T.degree v+if v∈leaves T then 1 else 0))=(∑ v∈P,(2+(T.degree v-2))) :=
    sum_congr rfl (fun v _ => point v)
  simp only [sum_add_distrib,sum_const,smul_eq_mul] at sum
  have cnt : (∑ v∈P, if v∈leaves T then 1 else 0 : ℕ)=(P∩leaves T).card := by simp [filter_mem_eq_inter]
  rw [cnt] at sum
  have parts := card_sdiff_add_card_inter (leaves T) P
  rw [inter_comm (leaves T) P] at parts
  have edges := tr.card_edgeFinset
  omega

/-- One extra even-even edge can pay for at most one odd leaf or unit
of even branching at a hypothetical borderline failure. This applies to
every spanning tree of the original graph. -/
theorem charge_horizontal (G : SimpleGraph V) [DecidableRel G.Adj] (gc : G.Connected)
    (hn : 1<Fintype.card V) (r : V)
    (rank : Fintype.card V≤bipartiteNum G+secondDegree G+1)
    (bad : maxLeaves G+bipartiteNum G<1+independence G+evenCount G r)
    (T : SimpleGraph V) [DecidableRel T.Adj] (sub : T≤G) (tr : T.IsTree) :
    let P := parity G r false
    (leaves T\P).card+(∑ v∈P,(T.degree v-2))≤(T.edgeFinset∩P.sym2).card := by
  classical
  intro P
  have ⟨_,_,eq,ind⟩ := saturated_counts G gc hn r rank bad
  have same : univ\P=oddSet G r := by ext v; simp [P,oddSet,mem_parity]
  have odd : Indep T (univ\P) := by
    rw [same]; exact fun x hx y hy ne e => ind x hx y hy ne (sub e)
  have id := @horizontal_identity V _ _ T ‹DecidableRel T.Adj› tr hn P odd
  have cap : (leaves T).card≤maxLeaves G := by
    simpa only [univ_inter,weighted_all] using score_of_tree G T sub tr univ
  rw [even_equiv] at eq
  change maxLeaves G+Fintype.card V=2*P.card+1 at eq
  omega

#print axioms horizontal_identity
#print axioms charge_horizontal
end Minimal180.PortParity
