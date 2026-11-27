import Bypass180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

private theorem sole_old_edge (J T S : SimpleGraph V) (tr : T.IsTree) (st : S.IsTree)
    (u v : V) (sub : T≤J⊔SimpleGraph.edge u v) (used : T.Adj u v)
    [DecidableRel T.Adj] [DecidableRel S.Adj] (sj : S≤J) (keep : T⊓J≤S) (absent : ¬J.Adj u v) :
    (S.edgeFinset\T.edgeFinset).card=1 := by
  classical
  have missing : T.edgeFinset \ S.edgeFinset={s(u,v)} := by
    ext z
    induction z using Sym2.ind with
    | _ x y =>
      simp only [mem_sdiff,mem_edgeFinset,mem_singleton]
      constructor
      · rintro ⟨t,s⟩
        rcases sub t with j|e
        · exact (s (keep ⟨t,j⟩)).elim
        · exact ((adj_edge ..).mp e).1.symm
      · intro eq
        rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact ⟨used,fun e => absent (sj e)⟩
        · exact ⟨used.symm,fun e => absent (sj e).symm⟩
  have count := card_sdiff_add_card_inter T.edgeFinset S.edgeFinset
  rw [missing,card_singleton,inter_comm] at count
  have rev := card_sdiff_add_card_inter S.edgeFinset T.edgeFinset
  have := tr.card_edgeFinset
  have := st.card_edgeFinset
  omega

/-- When the chord endpoints have a common old neighbor w, any upper tree
beating the lower optimum comes from a lower optimum by a single endpoint
rotation exposing w. All other eligible leaves are identical. -/
theorem common_neighbor_rotation (J T : SimpleGraph V) (hn : 1<Fintype.card V) (u v w : V)
    (uv : u≠v) (no : ¬J.Adj u v) (uw : J.Adj u w) (wv : J.Adj w v) (U : Finset V)
    (sub : T≤J⊔SimpleGraph.edge u v) (tr : T.IsTree) (gain : weightedLeaves J U<(U∩leaves T).card) :
    w∈U ∩ leaves T ∧ T.Adj u v ∧ ∃ S≤J, S.IsTree ∧ (U∩leaves S).card=weightedLeaves J U ∧
      w∉U∩leaves S ∧ U∩leaves T=insert w (U∩leaves S) ∧ T⊓J≤S ∧
      ∃ z, (z=u ∨ z=v) ∧ S.Adj w z ∧ ¬ T.Adj w z ∧ S≤T⊔SimpleGraph.edge w z := by
  classical
  have used : T.Adj u v := by
    apply Classical.byContradiction
    intro n
    have tj : T≤J := by
      intro i j ij
      rcases sub ij with h|e
      · exact h
      · rcases ((edge_adj ..).mp e).1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact (n ij).elim
        · exact (n ij.symm).elim
    exact (Nat.not_le_of_lt gain) (le_sup (f:=fun K => (U∩leaves K).card) (mem_filter.mpr ⟨mem_univ _,tj,tr⟩))
  let p : J.Walk u v := (Walk.nil.cons wv).cons uw
  have simple : p.IsPath := by simp [p,Walk.cons_isPath_iff,uw.ne,uv,wv.ne]
  have inside : interior p=({w}:Finset V) := by ext x; simp [interior,p]; aesop
  obtain ⟨S,sj,st,keep,locality,repair⟩ := bypass_repair J T hn u v uv tr sub used p simple
  rw [inside] at repair
  let B := U∩leaves T
  let C := U∩leaves S
  have cover : B ⊆ insert w C := by
    intro x hx
    by_cases eq : x=w
    · exact eq ▸ mem_insert_self _ _
    · obtain ⟨a,b⟩ := mem_inter.mp hx
      exact mem_insert_of_mem (mem_inter.mpr ⟨a,repair (mem_sdiff.mpr ⟨b,by simpa using eq⟩)⟩)
  have cap : C.card≤weightedLeaves J U := le_sup (f:=fun K => (U∩leaves K).card)
    (mem_filter.mpr ⟨mem_univ _,sj,st⟩)
  change weightedLeaves J U<B.card at gain
  have bound := card_le_card cover
  have count := card_insert_le w C
  have eq := eq_of_subset_of_card_le cover (by omega)
  have outside : w∉C := by
    intro mem
    rw [insert_eq_of_mem mem] at eq
    rw [eq] at gain
    omega
  have win : w∈B := by rw [eq]; exact mem_insert_self _ _
  refine ⟨win,used,S,sj,st,by change C.card=_; omega,outside,eq,keep,?_⟩
  obtain ⟨f,only⟩ := card_eq_one.mp (sole_old_edge J T S tr st u v sub used sj keep no)
  induction f using Sym2.ind with
  | _ i j =>
    have both : s(i,j)∈S.edgeFinset\T.edgeFinset := by rw [only]; simp
    have e := mem_edgeFinset.mp (mem_sdiff.mp both).1
    have absent : ¬T.Adj i j := fun h => (mem_sdiff.mp both).2 (mem_edgeFinset.mpr h)
    have path : p.toSubgraph.Adj i j := (locality e).resolve_left (fun h => absent h.1)
    have choice : s(i,j)=s(w,u) ∨ s(i,j)=s(w,v) := by
      simp [p,Walk.toSubgraph,subgraphOfAdj_adj] at path
      simp [Sym2.eq_iff]
      aesop
    have finish {z : V} (endpt : z=u ∨ z=v) (same : s(i,j)=s(w,z)) :
        ∃ q, (q=u ∨ q=v) ∧ S.Adj w q ∧ ¬T.Adj w q ∧ S≤T⊔SimpleGraph.edge w q := by
      have mi := both
      rw [same,mem_sdiff,mem_edgeFinset,mem_edgeFinset] at mi
      refine ⟨z,endpt,mi.1,mi.2,?_⟩
      intro a b ab
      by_cases old : T.Adj a b
      · exact Or.inl old
      have fresh : s(a,b)∈S.edgeFinset\T.edgeFinset := mem_sdiff.mpr
        ⟨mem_edgeFinset.mpr ab,fun h => old (mem_edgeFinset.mp h)⟩
      rw [only,mem_singleton] at fresh
      exact Or.inr ((adj_edge ..).mpr ⟨(fresh.trans same).symm,ab.ne⟩)
    exact choice.elim (finish (Or.inl rfl)) (finish (Or.inr rfl))

#print axioms common_neighbor_rotation
end Minimal180
