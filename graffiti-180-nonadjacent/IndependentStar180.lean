import PairColors180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact leaf budget for an independent mark. Every tree edge missing the
mark and every degree above two in the mark pays one extra unit. -/
theorem independent_tree_identity (T : SimpleGraph V) [DecidableRel T.Adj] (tr : T.IsTree)
    (hn : 1<Fintype.card V) (P : Finset V) (pi : Indep T P) :
    Fintype.card V+(P∩leaves T).card =
      1+2*P.card+(T.edgeFinset∩(univ\P).sym2).card+∑ v∈P,(T.degree v-2) := by
  classical
  let E := P.biUnion (fun x => T.incidenceFinset x)
  have inc {i a b : V} : s(a,b)∈T.incidenceFinset i ↔ T.Adj a b ∧ (i=a ∨ i=b) := by
    rw [T.incidenceFinset_eq_filter]
    simp [Sym2.mem_iff]
  have eq : T.edgeFinset\E=T.edgeFinset∩(univ\P).sym2 := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [E,mem_sdiff,mem_edgeFinset,mem_biUnion,inc,mem_inter,mk_mem_sym2_iff,mem_univ,true_and]
      constructor
      · rintro ⟨ab,no⟩
        exact ⟨ab,fun am => no ⟨a,am,ab,Or.inl rfl⟩,fun bm => no ⟨b,bm,ab,Or.inr rfl⟩⟩
      · rintro ⟨ab,am,bm⟩
        refine ⟨ab,?_⟩
        rintro ⟨i,im,_,rfl|rfl⟩
        · exact am im
        · exact bm im
  have sub : E⊆T.edgeFinset := by
    intro e em
    obtain ⟨i,_,h⟩ := mem_biUnion.mp em
    rw [T.incidenceFinset_eq_filter] at h
    exact (mem_filter.mp h).1
  have cnt := card_sdiff_add_card_eq_card sub
  rw [eq] at cnt
  have mass : (∑ v∈P,T.degree v)=E.card := independent_mass T P pi
  have point (v : V) : T.degree v+(if v∈leaves T then 1 else 0)=2+(T.degree v-2) := by
    obtain ⟨w,e⟩ := exists_adj T tr.isConnected hn v
    have pos := (T.degree_pos_iff_exists_adj v).mpr ⟨w,e⟩
    have lf : v∈leaves T ↔ T.degree v=1 := by simp [leaves,SimpleGraph.degree,SimpleGraph.neighborFinset]
    split_ifs with h
    · have := lf.mp h; omega
    · have := mt lf.mpr h; omega
  have s : (∑ v∈P,(T.degree v+(if v∈leaves T then 1 else 0)))=∑ v∈P,(2+(T.degree v-2)) :=
    sum_congr rfl (fun v _ => point v)
  have c : (∑ v∈P,if v∈leaves T then 1 else 0 : ℕ)=(P∩leaves T).card := by simp [filter_mem_eq_inter]
  simp only [sum_add_distrib,sum_const,smul_eq_mul,c,mass] at s
  have := tr.card_edgeFinset
  omega

/-- A full root star and one edge with an endpoint outside that star
extend simultaneously to a spanning tree. -/
theorem star_and_edge (G : SimpleGraph V) (gc : G.Connected) (r u v : V)
    (ur : u≠r) (vr : v≠r) (ed : G.Adj u v) (off : ¬G.Adj r v) :
    ∃ T≤G,T.IsTree ∧ T.Adj u v ∧ ∀ x,G.Adj r x → T.Adj r x := by
  classical
  let p (x : V) := if x=v then u else r
  let d (x : V) := if x=r then 0 else if x=v then 2 else 1
  have down (x : V) (ne : x≠r) : d (p x)<d x := by
    by_cases eq : x=v
    · subst x; simp [p,d,ur,vr,ed.ne]
    · simp [p,d,eq,ne]
  obtain ⟨K,kt,keep⟩ := virtual_tree r p d down
  obtain ⟨T,tg,tr,sub⟩ := keep_target G K gc kt
  refine ⟨T,tg,tr,sub ⟨ed,?_⟩,fun x rx => sub ⟨rx,?_⟩⟩
  · simpa [p] using (keep v vr).symm
  · have ne : x≠v := fun e => off (e ▸ rx)
    simpa [p,ne] using (keep x rx.ne.symm).symm

#print axioms independent_tree_identity
#print axioms star_and_edge
end Minimal180.PairRepair
