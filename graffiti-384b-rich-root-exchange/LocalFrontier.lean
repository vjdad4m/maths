import ArticulationRoot
namespace Graffiti384b.RichRoot
open Finset SimpleGraph OddStars
open private RichRoot.quota RichRoot.outside from RichLeafRoot
open private TrianglePrune.triangle_iff from TrianglePrune384b
open private Repair.full_nbr Repair.nbr_add from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Failure with a positive-score leaf root and a surviving componentwise palette
forces all root contacts into one larger shore. Every closed region away from any
contact has no contacts and is exactly balanced in that same split. -/
theorem root_failure {r z : V} (score : 0<trianglesAt G r) (rz : G.Adj r z) (leaf : G.degree z=1)
    (profile : HasResidualPalette G (rootPool G r)) (bad : bound G<gamma G) :
    let S := rootPool G r
    let T := S.filter (G.Adj r)
    ∃L R,Split (triangleEdges G S) S L R ∧ T⊆L ∧ L.card=R.card+1 ∧
      ∀C,region (triangleEdges G S) C → (T\C).Nonempty →
        Disjoint T C ∧ (L∩C).card=(R∩C).card := by
  obtain ⟨x,y,rx,ry,xy⟩ := (TrianglePrune.triangle_iff G r).mp score
  have rm : r∈nonleaves G := mem_filter.mpr ⟨mem_univ _,PositivePalette.Prerequisites.deg2 G xy.ne rx ry⟩
  have xm : x∈nonleaves G := mem_filter.mpr ⟨mem_univ _,PositivePalette.Prerequisites.deg2 G ry.ne rx.symm xy⟩
  have t := RichRoot.quota G
  have q := card_erase_add_one rm
  apply region_barrier G (F:=∅) (b:=r) (k:=z) (by simp) (by simp)
    (fun h => (mem_erase.mp h).1 rfl) (by simp) (fun m => RichRoot.outside G leaf (erase_subset _ _ m)) rz
    (by simp) profile ⟨x,mem_filter.mpr ⟨mem_erase.mpr ⟨rx.ne.symm,xm⟩,rx⟩⟩
  unfold bound at bad; simp only [rootPool,card_empty,zero_add]; omega

/-- The density tests for the ear's other anchor force a low-degree obstruction
in the original graph even if deleting the two pivots destroys triangles. -/
theorem low_degree_obstruction {r z e b : V} (rm : r∈nonleaves G) (em : e∈nonleaves G) (bm : b∈nonleaves G)
    (rz : G.Adj r z) (leaf : G.degree z=1) (re : G.Adj r e) (be : G.Adj b e) (br : b≠r)
    (density : let S := exchangePool G r e b; let T := S.filter (G.Adj b)
      (S.card+1)/2<T.card ∨ ∃v∈T,nbr G v (S\T)<nbr G v T)
    (bad : bound G<gamma G) :
    let S := exchangePool G r e b
    let K := (insert b (({r}:Finset V)∪S))ᶜ
    ∃v∈S,G.degree v+nbr G v K<3+nbr G v {r,b} ∧ G.degree v≤4 := by
  classical
  let S := exchangePool G r e b
  let X : Finset V := {r,b}
  let K := (insert b (({r}:Finset V)∪S))ᶜ
  have fail : ¬∀v∈S,3≤nbr G v S+2*nbr G v K :=
    fun h => (not_lt_of_ge (path_exchange G rm em bm rz leaf re be br (Or.inr ⟨h,density⟩))) bad
  push_neg at fail
  obtain ⟨v,vs,weak⟩ := fail
  have ds : Disjoint S X := by
    apply disjoint_left.mpr
    intro w ws wx
    rcases mem_insert.mp wx with h|h
    · exact (mem_erase.mp (mem_erase.mp (mem_erase.mp ws).2).2).1 h
    · exact (mem_erase.mp ws).1 (mem_singleton.mp h)
  have eq : S∪X=insert b (({r}:Finset V)∪S) := by
    ext w; simp only [X,mem_union,mem_insert,mem_singleton]; tauto
  have deg := Repair.full_nbr G v (S∪X)
  have kdef : (S∪X)ᶜ=K := by rw [eq]
  rw [kdef,Repair.nbr_add G v ds] at deg
  have size : nbr G v X≤2 := (card_filter_le ..).trans_eq (card_pair br.symm)
  change ∃v∈S,G.degree v+nbr G v K<3+nbr G v X ∧ G.degree v≤4
  exact ⟨v,vs,by omega,by omega⟩

/-- A score-one ear between the root and its mate satisfies the original conjecture
if every other nonleaf has degree at least five and the mate meets strictly more
than half (rounded up) of those other nonleaves. The proof permits chords and
also applies to any middle core vertex with the same two adjacencies. -/
theorem dense_mate {r z e b : V} (rm : r∈nonleaves G) (em : e∈nonleaves G) (bm : b∈nonleaves G)
    (rz : G.Adj r z) (leaf : G.degree z=1) (re : G.Adj r e) (be : G.Adj b e) (br : b≠r)
    (high : ∀v∈exchangePool G r e b,5≤G.degree v)
    (many : ((exchangePool G r e b).card+1)/2<nbr G b (exchangePool G r e b)) :
    gamma G≤bound G := by
  by_contra! bad
  obtain ⟨v,vm,_,small⟩ := low_degree_obstruction G rm em bm rz leaf re be br (Or.inl many) bad
  have big := high v vm
  omega

end Graffiti384b.RichRoot
#print axioms Graffiti384b.RichRoot.root_failure
#print axioms Graffiti384b.RichRoot.low_degree_obstruction

#print axioms Graffiti384b.RichRoot.dense_mate
