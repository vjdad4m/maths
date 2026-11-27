import SpineTree180

set_option warningAsError true
namespace Minimal180.DescentOne
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem count_spine (T : SimpleGraph V) (tr : T.IsTree) (hn : 1<Fintype.card V)
    (I D U : Finset V) (ind : Indep T I) (iu : I⊆U) (du : D⊆U) (apart : Disjoint I D)
    {a b w : V} (ai : a∉I) (bi : b∉I) (ad : a∉D) (bd : b∉D) (wi : w∉I)
    (ab : T.Adj a b) (leaf : ∃ v∈D,v∈leaves T) (p : V→V) (d : V→ℕ)
    (step : ∀ i∈D,T.Adj i (p i) ∧ (p i∈D ∨ p i=w) ∧ d (p i)<d i) :
    2*I.card+D.card+2≤(U∩leaves T).card+(Fintype.card V-1) := by
  classical
  let f (i : V) := s(i,p i)
  have inj : Set.InjOn f (↑D : Set V) := by
    intro i hi j hj eq
    rcases Sym2.eq_iff.mp eq with e|⟨e,k⟩
    · exact e.1
    · have a := (step i hi).2.2
      have b := (step j hj).2.2
      have bad : d j<d (p j) := (congrArg d k.symm).trans_lt (a.trans_eq (congrArg d e))
      omega
  let E := insert s(a,b) (D.image f)
  have fresh : s(a,b)∉D.image f := by
    intro z
    obtain ⟨i,id,pair⟩ := mem_image.mp z
    rcases Sym2.eq_iff.mp pair with e|e
    · exact ad (e.1 ▸ id)
    · exact bd (e.1 ▸ id)
  have ec : E.card=D.card+1 := by rw [show E=insert s(a,b) (D.image f) from rfl,card_insert_of_not_mem fresh,card_image_of_injOn inj]
  let M := I.biUnion (fun i => T.incidenceFinset i)
  have es : E⊆T.edgeFinset := by
    intro u ue
    rcases mem_insert.mp ue with rfl|u
    · exact mem_edgeFinset.mpr ab
    · obtain ⟨i,id,rfl⟩ := mem_image.mp u
      exact mem_edgeFinset.mpr (step i id).1
  have ms : M⊆T.edgeFinset := by
    intro e em
    obtain ⟨i,_,h⟩ := mem_biUnion.mp em
    rw [T.incidenceFinset_eq_filter] at h
    exact (mem_filter.mp h).1
  have outside {u v : V} (ui : u∉I) (vi : v∉I) : s(u,v)∉M := by
    intro edge
    obtain ⟨i,hi,he⟩ := mem_biUnion.mp edge
    rw [T.incidenceFinset_eq_filter] at he
    rcases Sym2.mem_iff.mp (mem_filter.mp he).2 with e|e
    · exact ui (e ▸ hi)
    · exact vi (e ▸ hi)
  have dis : Disjoint E M := by
    apply disjoint_left.mpr
    intro e he
    rcases mem_insert.mp he with rfl|old
    · exact outside ai bi
    · obtain ⟨i,id,rfl⟩ := mem_image.mp old
      have no {z : V} (zd : z∈D) : z∉I := fun zi => disjoint_left.mp apart zi zd
      exact outside (no id) ((step i id).2.1.elim (fun q => no q) (fun eq => eq ▸ wi))
  have cap := card_le_card (union_subset es ms)
  rw [card_union_of_disjoint dis,ec] at cap
  have mass : (∑ v∈I,T.degree v)=M.card := independent_mass T I ind
  have vi (v : V) : 2≤T.degree v+(if v∈leaves T then 1 else 0) := by
    obtain ⟨i,e⟩ := exists_adj T tr.isConnected hn v
    have pos := (T.degree_pos_iff_exists_adj v).mpr ⟨i,e⟩
    have lf : v∈leaves T ↔ T.degree v=1 := by simp [leaves,SimpleGraph.degree,SimpleGraph.neighborFinset]
    split_ifs with h
    · have := lf.mp h; omega
    · have := mt lf.mpr h; omega
  have s := sum_le_sum (s:=I) (fun v _ => vi v)
  have c : (∑ v∈I,if v∈leaves T then 1 else 0 : ℕ)=(I∩leaves T).card := by simp [filter_mem_eq_inter]
  rw [sum_add_distrib,c,mass] at s
  simp only [sum_const,smul_eq_mul] at s
  obtain ⟨v,vd,vl⟩ := leaf
  have more := card_le_card (show insert v (I∩leaves T)⊆U∩leaves T from
    insert_subset (mem_inter.mpr ⟨du vd,vl⟩) (fun i hi => mem_inter.mpr ⟨iu (mem_inter.mp hi).1,(mem_inter.mp hi).2⟩))
  rw [card_insert_of_not_mem (fun z => disjoint_left.mp apart (mem_inter.mp z).1 vd)] at more
  have := tr.card_edgeFinset
  omega

/-- In a failed tight cut at lower deficit one, the vertices missed by both
marks are independent, even in the upper graph. -/
theorem unmarked_independent {J : SimpleGraph V} {S T : Finset V} {x y w : V}
    {r : ↥S} {odd : Bool} {A : Finset V} (h : TightCut J S T x y w r odd A)
    (one : bipartiteNum J+1=Fintype.card V) :
    let G := J⊔edge x y
    let P := parity G r.val odd
    let U := eligible A P r.val
    ¬weightedLeaves J U<weightedLeaves G U → Indep G (univ\(A∪P)) := by
  classical
  intro G P U ng
  let I := A∩P
  let D := (A∪P)\I
  obtain ⟨cover,nw,t,_,_,tw,sp⟩ := failed_spine h one ng
  change Spine J r.val D t at sp
  change U=A∪P at cover
  have impossible (a b : V) (aa : a∉A∪P) (bb : b∉A∪P) (aw : a≠w) (ab : G.Adj a b) : False := by
    have noD {i : V} (out : i∉A∪P) : i∉D := fun m => out (mem_sdiff.mp m).1
    have noI {i : V} (out : i∉A∪P) : i∉I := fun m => out (mem_union_left _ (mem_inter.mp m).1)
    obtain ⟨M,mg,tree,edge,leaf,p,d,step⟩ := spine_tree (G:=G) le_sup_left h.block (by have := h.order; omega)
      sp (noD nw) (Or.inl tw) (noD aa) (noD bb) aw ab
    have iu : I⊆U := cover ▸ (inter_subset_left.trans subset_union_left)
    have du : D⊆U := cover ▸ sdiff_subset
    have dis : Disjoint I D := disjoint_left.mpr fun _ a b => (mem_sdiff.mp b).2 a
    have ind : Indep M I := fun i im j jm ne e => h.independent i (mem_inter.mp im).1 j (mem_inter.mp jm).1 ne (mg e)
    have lower := count_spine M tree (by have := h.order; omega) I D U ind iu du dis
      (noI aa) (noI bb) (noD aa) (noD bb) (noI nw) edge leaf p d step
    have upper : (U∩leaves M).card≤weightedLeaves G U := le_sup (f:=fun K => (U∩leaves K).card)
      (mem_filter.mpr ⟨mem_univ _,mg,tree⟩)
    have eq := h.tight
    change weightedLeaves J U+bipartiteNum J=1+A.card+P.card at eq
    have ci := card_union_add_card_inter A P
    have ii : I⊆A∪P := inter_subset_left.trans subset_union_left
    have cd := card_sdiff_add_card_eq_card ii
    change D.card+I.card=(A∪P).card at cd
    change (A∪P).card+I.card=A.card+P.card at ci
    omega
  intro i im j jm ne e
  by_cases iw : i=w
  · exact impossible j i (mem_sdiff.mp jm).2 (mem_sdiff.mp im).2 (by intro eq; exact ne (iw.trans eq.symm)) e.symm
  · exact impossible i j (mem_sdiff.mp im).2 (mem_sdiff.mp jm).2 iw e

#print axioms count_spine
#print axioms unmarked_independent
end Minimal180.DescentOne
