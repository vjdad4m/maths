import Inactive180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem restore_wing (G : SimpleGraph V) (b : V) (Y O : Finset V) (dis : Disjoint Y O)
    (cross : ∀ x∈O,∀ y∈Y,G.Adj x y → y=b) (core : TwoColor G Y) (wing : TwoColor G (insert b O)) :
    TwoColor G (Y∪O) := by
  classical
  obtain ⟨e,old⟩ := (color_function ..).mp core
  obtain ⟨f,side⟩ := (color_function ..).mp wing
  let k (x : V) := if f x=f b then e b else !(e b)
  let c (x : V) := if x∈O then k x else e x
  have cy (x : V) (xm : x∈Y) : c x=e x := by simp [c,disjoint_left.mp dis xm]
  have co (x : V) (xm : x∈O) : c x=k x := by simp [c,xm]
  have res (x : V) (xm : x∈insert b O) (y : V) (ym : y∈insert b O) (ed : G.Adj x y) : k x≠k y := by
    have diff := side x xm y ym ed
    cases h : f x <;> cases j : f y <;> cases i : f b <;> cases w : e b <;> simp_all [k]
  have between (x : V) (xm : x∈O) (y : V) (ym : y∈Y) (ed : G.Adj x y) : c x≠c y := by
    obtain rfl := cross x xm y ym ed
    rw [co x xm,cy y ym,←show k y=e y by simp [k]]
    exact res x (mem_insert_of_mem xm) y (mem_insert_self ..) ed
  refine (color_function ..).mpr ⟨c,fun x xm y ym ed => ?_⟩
  rcases mem_union.mp xm with xm|xm <;> rcases mem_union.mp ym with ym|ym
  · rw [cy x xm,cy y ym];exact old x xm y ym ed
  · exact (between y ym x xm ed.symm).symm
  · exact between x xm y ym ed
  · rw [co x xm,co y ym];exact res x (mem_insert_of_mem xm) y (mem_insert_of_mem ym) ed

/-- The entire inactive union may be restored without spending any
budget, whether or not the unprotected terminal itself was deleted.
This includes the single-active-component branch. -/
theorem active_core_iff (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (rk : Fintype.card V≤bipartiteNum G+2) (r : V) (p : Bool) (A : Finset V) (ai : Indep G A)
    (a b : V) (ab : a≠b) (na : ¬G.Adj a b) (am : a∈A) (pm : a∈parity G r p)
    (sat : G.degree a=allowance G r p A+2) (O : Finset V) (sub : O⊆univ\({a,b}:Finset V))
    (cl : ClosedIn G (univ\{a,b}) O) (empty : ∀ x∈O,¬G.Adj a x) :
    Protected G r p A ↔ ∃ M : Finset V,M⊆univ\O ∧ Disjoint M (A∩insert r (parity G r p)) ∧
      M.card≤allowance G r p A ∧ TwoColor G ((univ\O)\M) := by
  classical
  let K := A∩insert r (parity G r p)
  obtain ⟨e,full,_,_⟩ := inactive_free G gc hn rk r p A ai a b ab na am pm sat O sub cl empty false
  have wing : TwoColor G (insert b O) := by
    have inc : insert b O⊆({a,b}:Finset V)∪O := by
      intro x xm
      rcases mem_insert.mp xm with eq|m
      · exact eq ▸ mem_union_left _ (mem_insert_of_mem (mem_singleton_self _))
      · exact mem_union_right _ m
    exact (color_function ..).mpr ⟨e,fun x xm y ym => full x (inc xm) y (inc ym)⟩
  rw [protected_iff G gc hn r p A ai]
  constructor
  · rintro ⟨Z,bi,keep,budget⟩
    let M := (univ\Z)\O
    have count := card_sdiff_add_card_eq_card (subset_univ Z)
    have sz := card_le_card (show M⊆univ\Z from sdiff_subset)
    rw [card_univ] at count
    have inc : (univ\O)\M⊆Z := by
      intro x xm
      have xo := (mem_sdiff.mp (mem_sdiff.mp xm).1).2
      by_contra no
      exact (mem_sdiff.mp xm).2 (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,no⟩,xo⟩)
    obtain ⟨f,ok⟩ := (color_function ..).mp bi
    exact ⟨M,fun x xm => mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp xm).2⟩,
      disjoint_left.mpr (fun _ xm xk => (mem_sdiff.mp (mem_sdiff.mp xm).1).2 (keep xk)),
      by omega,(color_function ..).mpr ⟨f,fun x xm y ym => ok x (inc xm) y (inc ym)⟩⟩
  · rintro ⟨M,mc,dis,budget,col⟩
    let Y := (univ\O)\M
    have away : Disjoint Y O := disjoint_left.mpr (fun _ ym => (mem_sdiff.mp (mem_sdiff.mp ym).1).2)
    have cross (x : V) (xm : x∈O) (y : V) (ym : y∈Y) (ed : G.Adj x y) : y=b := by
      by_contra yb
      have ya : y≠a := fun eq => empty x xm (eq ▸ ed.symm)
      have yr : y∈univ\({a,b}:Finset V) := by simp [ya,yb]
      exact disjoint_left.mp away ym ((cl x (sub xm) y yr ed).mp xm)
    have restore := restore_wing G b Y O away cross col wing
    have form : Y∪O=univ\M := by
      ext x
      have no : x∈M → x∉O := fun m => (mem_sdiff.mp (mc m)).2
      simp only [Y,mem_union,mem_sdiff,mem_univ,true_and];tauto
    rw [form] at restore
    have count := card_sdiff_add_card_eq_card (subset_univ M)
    rw [card_univ] at count
    exact ⟨_,restore,fun x xk => mem_sdiff.mpr ⟨mem_univ _,fun xm => disjoint_left.mp dis xm xk⟩,by omega⟩

#print axioms active_core_iff
end Minimal180.PairRepair
