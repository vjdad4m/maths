import DegreeFiveRouteBasic189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- With at most one low residual degree, a five-vertex set contains a
four-vertex path. No finite model enumeration is used. -/
theorem four_path_in_five_with_pair_degree_two (R : Finset V) (five : R.card=5)
    (degree : ∀ u∈R,∀ v∈R,u≠v →
      2 ≤ (R.filter (G.Adj u)).card ∨ 2 ≤ (R.filter (G.Adj v)).card) :
    ∃ P⊆R,P.card=4 ∧ ∃ u∈P,∃ v∈P,RouteOn G P u v := by
  classical
  have build {a b c d : V} (ar : a∈R) (br : b∈R) (cr : c∈R) (dr : d∈R)
      (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d)
      (ac : a≠c) (ad : a≠d) (bd : b≠d) :
      ∃ P⊆R,P.card=4 ∧ ∃ u∈P,∃ v∈P,RouteOn G P u v := by
    let T : Finset V := {a,b,c}
    have off : d∉T := by simp [T,ad.symm,bd.symm,cd.ne.symm]
    have rc : RouteOn G T a c := RouteOn.three ab bc ac
    let P := insert d T
    have pc : P.card=4 := by
      rw [card_insert_of_not_mem off]
      have h : a∉({b,c} : Finset V) := by simp [ab.ne,ac]
      change (insert a ({b,c} : Finset V)).card+1=4
      rw [card_insert_of_not_mem h]
      simp [bc.ne]
    have sub : P⊆R := by
      simpa [P,T] using (show insert d ({a,b,c} : Finset V)⊆R from
        insert_subset_iff.mpr ⟨dr,insert_subset_iff.mpr ⟨ar,insert_subset_iff.mpr ⟨br,
          singleton_subset_iff.mpr cr⟩⟩⟩)
    exact ⟨P,sub,pc,a,by simp [P,T],d,by simp [P],rc.suffix cd off⟩
  apply Classical.byContradiction
  intro no
  obtain ⟨u,ur,v,vr,uv⟩ := one_lt_card.mp (show 1<R.card by omega)
  obtain ⟨y,yr,hi⟩ : ∃ y∈R,1<(R.filter (G.Adj y)).card := by
    rcases degree u ur v vr uv with h|h
    · exact ⟨u,ur,by omega⟩
    exact ⟨v,vr,by omega⟩
  obtain ⟨x,xf,z,zf,xz⟩ := one_lt_card.mp hi
  obtain ⟨xr,yx⟩ := mem_filter.mp xf
  obtain ⟨zr,yz⟩ := mem_filter.mp zf
  let S : Finset V := {x,y,z}
  let Q := R\S
  have ss : S⊆R := insert_subset_iff.mpr ⟨xr,insert_subset_iff.mpr ⟨yr,singleton_subset_iff.mpr zr⟩⟩
  have s3 : S.card=3 := by
    have h : x∉({y,z} : Finset V) := by simp [yx.ne.symm,xz]
    change (insert x ({y,z} : Finset V)).card=3
    rw [card_insert_of_not_mem h]
    simp [yz.ne]
  have q2 : Q.card=2 := by
    have h : Q.card+S.card=R.card := card_sdiff_add_card_eq_card ss
    omega
  have decompose {w : V} (wq : w∈Q) :
      w∈R ∧ w≠x ∧ w≠y ∧ w≠z := by
    obtain ⟨wr,ws⟩ := mem_sdiff.mp wq
    exact ⟨wr,by simpa [S,not_or] using ws⟩
  have noX {w : V} (wq : w∈Q) : ¬G.Adj x w := by
    intro xw
    obtain ⟨wr,wx,wy,wz⟩ := decompose wq
    exact no (build wr xr yr zr xw.symm yx.symm yz wy wz xz)
  have noZ {w : V} (wq : w∈Q) : ¬G.Adj z w := by
    intro zw
    obtain ⟨wr,wx,wy,wz⟩ := decompose wq
    exact no (build xr yr zr wr yx.symm yz zw xz wx.symm wy.symm)
  by_cases e : G.Adj x z
  · have noY {w : V} (wq : w∈Q) : ¬G.Adj y w := by
      intro yw
      obtain ⟨wr,wx,wy,wz⟩ := decompose wq
      exact no (build wr yr xr zr yw.symm yx e wx wz yz.ne)
    have low (w : V) (wq : w∈Q) : (R.filter (G.Adj w)).card≤1 := by
      have sub : R.filter (G.Adj w)⊆Q.erase w := by
        intro t tm
        obtain ⟨tr,wt⟩ := mem_filter.mp tm
        refine mem_erase.mpr ⟨wt.ne.symm,mem_sdiff.mpr ⟨tr,?_⟩⟩
        intro ts
        rcases mem_insert.mp ts with rfl|ts
        · exact noX wq wt.symm
        rcases mem_insert.mp ts with rfl|ts
        · exact noY wq wt.symm
        obtain rfl := mem_singleton.mp ts
        exact noZ wq wt.symm
      have k := card_le_card sub
      rw [card_erase_of_mem wq,q2] at k
      exact k
    obtain ⟨p,pq,q,qq,pne⟩ := one_lt_card.mp (show 1<Q.card by omega)
    have pw := low p pq
    have qw := low q qq
    exact (degree p (decompose pq).1 q (decompose qq).1 pne).elim
      (fun h=>by omega) (fun h=>by omega)
  have xLow : (R.filter (G.Adj x)).card≤1 := by
    have sub : R.filter (G.Adj x)⊆{y} := by
      intro t tm
      obtain ⟨tr,xt⟩ := mem_filter.mp tm
      have ts : t∈S := Classical.byContradiction (fun n=>noX (mem_sdiff.mpr ⟨tr,n⟩) xt)
      rcases mem_insert.mp ts with rfl|ts
      · exact (G.loopless _ xt).elim
      rcases mem_insert.mp ts with rfl|ts
      · exact mem_singleton_self _
      obtain rfl := mem_singleton.mp ts
      exact (e xt).elim
    simpa using card_le_card sub
  have zLow : (R.filter (G.Adj z)).card≤1 := by
    have sub : R.filter (G.Adj z)⊆{y} := by
      intro t tm
      obtain ⟨tr,zt⟩ := mem_filter.mp tm
      have ts : t∈S := Classical.byContradiction (fun n=>noZ (mem_sdiff.mpr ⟨tr,n⟩) zt)
      rcases mem_insert.mp ts with rfl|ts
      · exact (e zt.symm).elim
      rcases mem_insert.mp ts with rfl|ts
      · exact mem_singleton_self _
      obtain rfl := mem_singleton.mp ts
      exact (G.loopless _ zt).elim
    simpa using card_le_card sub
  exact (degree x xr z zr xz).elim (fun h=>by omega) (fun h=>by omega)

#print axioms four_path_in_five_with_pair_degree_two
end Graffiti189LongestPath.CrossSaturation
