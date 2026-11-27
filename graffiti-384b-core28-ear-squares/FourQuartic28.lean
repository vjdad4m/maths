import FourLowSquare28
namespace Graffiti384b.Four28
open Finset SimpleGraph HighEar
open private Four28.degree_four_budgets from FourLowSquare28
open private Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A surviving degree-four fourth vertex has a pendant edge on a triangle
in its link. The attachment of that edge is a second fourth vertex on the
ear's square. -/
theorem quartic_link {e s p q : V} (n : Fintype.card V=28) (pq : G.Adj p q)
    (en : G.neighborFinset e={p,q}) (es : e≠s) (sp : G.Adj s p) (sq : G.Adj s q)
    (se : trianglesAt G e=1) (pos : ∀ v,0<trianglesAt G v) (fi : Function.Injective (trianglesAt G))
    (free : G.CliqueFree 5) (half : 14≤gamma G)
    (sup : ∀ w,G.Adj s w → ∃ z,G.Adj s z ∧ G.Adj w z) (ds : G.degree s=4) :
    trianglesAt G s=4 ∧ ∃ x y,leaks G s p q={x} ∧
      G.neighborFinset s={p,q,x,y} ∧ G.Adj x y ∧ y∈additional G e p q ∧ y≠s := by
  classical
  have cap := RankTuran.local_turan G 3 (by decide) free s
  rw [ds] at cap
  have val : (turanGraph 4 3).edgeFinset.card=5 :=
    (RankTable.cap_table ⟨4,by decide⟩ ⟨3,by decide⟩ (by decide)).trans (by decide)
  rw [val] at cap
  have ne : trianglesAt G s≠1 := fun eq => es (fi (se.trans eq.symm))
  have badscore : ¬(trianglesAt G s=2 ∨ trianglesAt G s=3 ∨ trianglesAt G s=5) := by
    intro m
    have small := low_square G n pq en es sp sq se pos fi free sup (m.elim Or.inl (fun h => Or.inr (Or.inr ⟨ds,h⟩)))
    omega
  have sc : trianglesAt G s=4 := by have := pos s; omega
  have few := (Four28.degree_four_budgets G pq.ne sp sq ds).1 (by omega)
  have some' : 0<(leaks G s p q).card := by
    by_contra! zero
    have low := square_saving_routes G n pq.ne en es ((G.mem_neighborFinset ..).mp (en ▸ mem_insert_self ..))
      ((G.mem_neighborFinset ..).mp (en ▸ mem_insert_of_mem (mem_singleton_self _))) sp sq se pos fi free
      (mem_Icc.mpr (by omega)) (Or.inl (by omega))
    omega
  obtain ⟨x,ex⟩ := card_eq_one.mp (show (leaks G s p q).card=1 by omega)
  obtain ⟨xn,xp,xq,np,nq⟩ := mem_filter.mp (show x∈leaks G s p q from ex ▸ mem_singleton_self _)
  let N := G.neighborFinset s
  let R := N.erase x
  have sz : R.card=3 := by rw [show R=N.erase x from rfl,card_erase_of_mem xn,card_neighborFinset_eq_degree,ds]
  have roots : ({p,q}:Finset V)⊆R := insert_subset (mem_erase.mpr ⟨xp.symm,(G.mem_neighborFinset ..).mpr sp⟩)
    (singleton_subset_iff.mpr (mem_erase.mpr ⟨xq.symm,(G.mem_neighborFinset ..).mpr sq⟩))
  have sy : (R\{p,q}).card=1 := by rw [card_sdiff roots,sz,card_pair pq.ne]
  obtain ⟨y,ey⟩ := card_eq_one.mp sy
  have ym : y∈R\{p,q} := ey ▸ mem_singleton_self _
  have yr := (mem_sdiff.mp ym).1
  have yp : y≠p := fun eq => (mem_sdiff.mp ym).2 (eq ▸ mem_insert_self ..)
  have yq : y≠q := fun eq => (mem_sdiff.mp ym).2 (eq ▸ mem_insert_of_mem (mem_singleton_self _))
  have rr : R={p,q,y} := (eq_of_subset_of_card_le (insert_subset (roots (mem_insert_self ..))
    (insert_subset (roots (mem_insert_of_mem (mem_singleton_self _))) (singleton_subset_iff.mpr yr)))
    (by rw [sz]; simp [pq.ne,yp.symm,yq.symm])).symm
  have sx := (G.mem_neighborFinset ..).mp xn
  have sy' := (G.mem_neighborFinset ..).mp (mem_erase.mp yr).2
  have nx : N=insert x R := (insert_erase (show x∈N from xn)).symm
  have cnt := pairs_insert G (D:=R) (not_mem_erase x N)
  rw [←nx] at cnt
  change trianglesAt G s=(pairs G R).card+nbr G x R at cnt
  have small : (R.filter (G.Adj x))⊆{y} := by
    intro z zm
    have zr := (mem_filter.mp zm).1; rw [rr] at zr
    rcases mem_insert.mp zr with rfl|zr
    · exact (np (mem_filter.mp zm).2).elim
    · rcases mem_insert.mp zr with rfl|zy
      · exact (nq (mem_filter.mp zm).2).elim
      · exact zy
  have one := (card_le_card small).trans_eq (card_singleton _)
  change nbr G x R≤1 at one
  have maxed : (pairs G R)=R.powersetCard 2 := eq_of_subset_of_card_le (filter_subset ..) (by
    rw [card_powersetCard,sz]; change 3≤(pairs G R).card; omega)
  have complete {a b : V} (ar : a∈R) (br : b∈R) (ab : a≠b) : G.Adj a b := by
    have present : ({a,b}:Finset V)∈pairs G R := maxed ▸ mem_powersetCard.mpr
      ⟨insert_subset ar (singleton_subset_iff.mpr br),card_pair ab⟩
    exact (mem_filter.mp present).2 a (mem_insert_self ..) b (mem_insert_of_mem (mem_singleton_self _)) ab
  have eR : (pairs G R).card=3 := by rw [maxed,card_powersetCard,sz]; decide
  have linked : G.Adj x y := by
    obtain ⟨w,wm⟩ := card_pos.mp (show 0<(R.filter (G.Adj x)).card by change 0<nbr G x R; omega)
    exact mem_singleton.mp (small wm) ▸ (mem_filter.mp wm).2
  have ye : y≠e := by
    intro eq; subst y
    have m := (G.mem_neighborFinset ..).mpr sy'.symm
    rw [en] at m
    exact (mem_insert.mp m).elim sp.ne (fun z => sq.ne (mem_singleton.mp z))
  refine ⟨sc,x,y,ex,?_,linked,(additional_mem G).mpr ⟨ye,complete (roots (mem_insert_self ..)) yr yp.symm,
    complete (roots (mem_insert_of_mem (mem_singleton_self _))) yr yq.symm⟩,sy'.ne.symm⟩
  change N=_
  rw [nx,rr]; ext; simp [or_comm,or_assoc,or_left_comm]
end Graffiti384b.Four28
#print axioms Graffiti384b.Four28.quartic_link
