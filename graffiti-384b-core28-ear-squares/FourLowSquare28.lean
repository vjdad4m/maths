import FourSquareSaving28

namespace Graffiti384b.Four28
open Finset SimpleGraph HighEar
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- When the fourth vertex has score two, its second triangle contains
all uncredited exterior neighbors on triangle edges. -/
theorem two_layout {s p q : V} (pq : G.Adj p q) (sp : G.Adj s p) (sq : G.Adj s q)
    (two : trianglesAt G s=2) (supported : ∀ w,G.Adj s w → ∃ z,G.Adj s z ∧ G.Adj w z) :
    (leaks G s p q).card≤1 ∨ ∃ x y,leaks G s p q={x,y} ∧ G.Adj x y := by
  classical
  let E := pairs G (G.neighborFinset s)
  let root : Finset V := {p,q}
  have rm : root∈E := (pair_mem G).mpr ⟨p,(G.mem_neighborFinset ..).mpr sp,q,
    (G.mem_neighborFinset ..).mpr sq,pq,rfl⟩
  have size : E.card=2 := two
  have one : (E.erase root).card=1 := by rw [card_erase_of_mem rm,size]
  obtain ⟨K,only⟩ := card_eq_one.mp one
  obtain ⟨x,_,y,_,xy,pair⟩ := (pair_mem G).mp
    (erase_subset _ _ (show K∈E.erase root from only ▸ mem_singleton_self _))
  have sub : leaks G s p q⊆{x,y} := by
    intro w wm
    obtain ⟨wn,wp,wq,_,_⟩ := mem_filter.mp wm
    obtain ⟨z,sz,wz⟩ := supported w ((G.mem_neighborFinset ..).mp wn)
    have link : ({w,z}:Finset V)∈E := (pair_mem G).mpr ⟨w,wn,z,(G.mem_neighborFinset ..).mpr sz,wz,rfl⟩
    have diff : ({w,z}:Finset V)≠root := by
      intro eq
      have m : w∈root := eq ▸ mem_insert_self .. 
      exact (mem_insert.mp m).elim wp (fun u => wq (mem_singleton.mp u))
    have rest := mem_erase.mpr ⟨diff,link⟩
    rw [only,mem_singleton,pair] at rest
    exact rest ▸ mem_insert_self .. 
  by_cases small : (leaks G s p q).card≤1
  · exact Or.inl small
  · exact Or.inr ⟨x,y,eq_of_subset_of_card_le sub (by rw [card_pair xy.ne]; omega),xy⟩

private theorem degree_four_budgets {s p q : V} (pq : p≠q) (sp : G.Adj s p) (sq : G.Adj s q)
    (ds : G.degree s=4) :
    (3≤trianglesAt G s → (leaks G s p q).card≤1) ∧
    (5≤trianglesAt G s → (leaks G s p q).card=0) := by
  classical
  let N := G.neighborFinset s
  let A := N\{p,q}
  have ps : ({p,q}:Finset V)⊆N := insert_subset ((G.mem_neighborFinset ..).mpr sp)
    (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr sq))
  have sz : A.card=2 := by rw [show A=N\{p,q} from rfl,card_sdiff ps,card_neighborFinset_eq_degree,ds,card_pair pq]
  have la : leaks G s p q⊆A := by
    intro w wm; obtain ⟨wn,wp,wq,_,_⟩ := mem_filter.mp wm
    exact mem_sdiff.mpr ⟨wn,by simp [wp,wq]⟩
  have pp : p∉A := fun m => (mem_sdiff.mp m).2 (mem_insert_self ..)
  have qq : q∉A := fun m => (mem_sdiff.mp m).2 (mem_insert_of_mem (mem_singleton_self _))
  have split : N=insert p (insert q A) := by
    calc N = {p,q}∪A := (union_sdiff_of_subset ps).symm
         _ = _ := by ext; simp [or_assoc]
  constructor
  · intro big
    by_contra! too
    have eq : leaks G s p q=A := eq_of_subset_of_card_le la (by rw [sz]; omega)
    have pzero : A.filter (G.Adj p)=∅ := filter_eq_empty_iff.mpr (by
      intro w wm ed; exact (mem_filter.mp (eq ▸ wm)).2.2.2.1 ed.symm)
    have qzero : A.filter (G.Adj q)=∅ := filter_eq_empty_iff.mpr (by
      intro w wm ed; exact (mem_filter.mp (eq ▸ wm)).2.2.2.2 ed.symm)
    have limit : (pairs G A).card≤1 := (card_filter_le ..).trans (by rw [card_powersetCard,sz]; decide)
    change 3≤(pairs G N).card at big
    rw [split,pairs_insert G (by simp [pq,pp]),pairs_insert G qq] at big
    unfold nbr at big
    by_cases ed : G.Adj p q <;> simp [Finset.filter_insert,ed,pzero,qzero] at big <;> omega
  · intro big
    apply card_eq_zero.mpr; apply eq_empty_iff_forall_not_mem.mpr
    intro x xm
    obtain ⟨xn,xp,xq,np,nq⟩ := mem_filter.mp xm
    let R := N.erase x
    have szR : R.card=3 := by rw [show R=N.erase x from rfl,card_erase_of_mem xn,card_neighborFinset_eq_degree,ds]
    have roots : ({p,q}:Finset V)⊆R := insert_subset (mem_erase.mpr ⟨xp.symm,(G.mem_neighborFinset ..).mpr sp⟩)
      (singleton_subset_iff.mpr (mem_erase.mpr ⟨xq.symm,(G.mem_neighborFinset ..).mpr sq⟩))
    have inside : R.filter (G.Adj x)⊆R\{p,q} := by
      intro a m; obtain ⟨ar,ed⟩ := mem_filter.mp m
      refine mem_sdiff.mpr ⟨ar,?_⟩; intro pin
      rcases mem_insert.mp pin with rfl|pin
      · exact np ed
      · exact nq (mem_singleton.mp pin ▸ ed)
    have small := card_le_card inside
    rw [card_sdiff roots,szR,card_pair pq] at small
    have limit : (pairs G R).card≤3 := (card_filter_le ..).trans (by rw [card_powersetCard,szR]; decide)
    change 5≤(pairs G N).card at big
    rw [←insert_erase (show x∈N from xn),pairs_insert G (not_mem_erase x N)] at big
    change 5≤(pairs G R).card+(R.filter (G.Adj x)).card at big
    omega

/-- A score-two supported fourth vertex, a cubic fourth vertex, or one of
degree four with score three or five supplies fifteen omitted vertices. -/
theorem low_square {e s p q : V} (n : Fintype.card V=28) (pq : G.Adj p q)
    (en : G.neighborFinset e={p,q}) (es : e≠s) (sp : G.Adj s p) (sq : G.Adj s q)
    (se : trianglesAt G e=1) (pos : ∀ v,0<trianglesAt G v) (fi : Function.Injective (trianglesAt G))
    (free : G.CliqueFree 5) (sup : ∀ w,G.Adj s w → ∃ z,G.Adj s z ∧ G.Adj w z)
    (profile : trianglesAt G s=2 ∨ G.degree s=3 ∨
      (G.degree s=4 ∧ (trianglesAt G s=3 ∨ trianglesAt G s=5))) : gamma G≤13 := by
  classical
  have ep : G.Adj e p := (G.mem_neighborFinset ..).mp (en ▸ mem_insert_self ..)
  have eq' : G.Adj e q := (G.mem_neighborFinset ..).mp (en ▸ mem_insert_of_mem (mem_singleton_self _))
  rcases profile with score|deg|⟨deg,score⟩
  · apply square_saving_routes G n pq.ne en es ep eq' sp sq se pos fi free (mem_Icc.mpr (by omega))
    rcases two_layout G pq sp sq score sup with few|pair
    · exact Or.inl (by simpa [allowance,score] using few)
    · exact Or.inr ⟨Or.inl score,pair⟩
  · exact cubic_square G n pq.ne en es sp sq se pos fi free deg
  · have cut := degree_four_budgets G pq.ne sp sq deg
    apply square_saving_routes G n pq.ne en es ep eq' sp sq se pos fi free (mem_Icc.mpr (by omega))
    apply Or.inl
    rcases score with three|five
    · simpa [allowance,three] using cut.1 three.ge
    · rw [cut.2 five.ge]; exact Nat.zero_le _
end Graffiti384b.Four28
#print axioms Graffiti384b.Four28.two_layout
#print axioms Graffiti384b.Four28.low_square
