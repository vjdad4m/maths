import DiversityElevenPendantOneTag384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [DecidableEq V]

/-- Three 2-element bad sets indexed by a loopless symmetric relation
on their own indices cannot cover a six-element universe. -/
theorem small_symmetric_bad_family (T M : Finset V) (ts : T.card=6)
    (sub : M⊆T) (ms : M.card≤3) (bad : V → Finset V)
    (bs : ∀ x∈M,(bad x).card≤2) (diag : ∀ x∈M,x∉bad x)
    (sym : ∀ x∈M,∀ y∈M,x∈bad y → y∈bad x) :
    ∃ b∈T, b∉M.biUnion bad := by
  classical
  by_contra! all
  have major := card_le_card (show T⊆M.biUnion bad from all)
  have minor := (card_biUnion_le (s:=M) (t:=bad)).trans
    (sum_le_sum bs)
  rw [ts] at major
  have mult : (M.biUnion bad).card≤M.card*2 := by simpa using minor
  have m3 : M.card=3 := by omega
  obtain ⟨x,xm⟩ := card_pos.mp (show 0<M.card by omega)
  obtain ⟨y,ym,hxy⟩ := mem_biUnion.mp (all x (sub xm))
  have xy : x≠y := fun h => diag y ym (h ▸ hxy)
  let P : Finset V := {x,y}
  have ps : P⊆M := insert_subset xm (singleton_subset_iff.mpr ym)
  have pc : P.card=2 := card_pair xy
  obtain ⟨z,zmZ⟩ := card_pos.mp (show 0<(M\P).card by rw [card_sdiff ps,m3,pc]; decide)
  obtain ⟨zm,zP⟩ := mem_sdiff.mp zmZ
  have zx : z≠x := fun e => zP (e ▸ mem_insert_self ..)
  have zy : z≠y := fun e => zP (e ▸ mem_insert_of_mem (mem_singleton_self _))
  have repr : M={x,y,z} := by
    symm
    refine eq_of_subset_of_card_le (insert_subset xm (insert_subset ym (singleton_subset_iff.mpr zm))) ?_
    rw [m3,card_insert_of_not_mem (by simp [xy,zx.symm]),card_pair zy.symm]
  have no_pair {a b c w : V} (am : a∈M) (bm : b∈M) (cm : c∈M)
      (re : M={a,b,c}) (wa : w∈bad a) (wb : w∈bad b) : False := by
    have cnt := card_union_add_card_inter (bad a) (bad b)
    have pos := card_pos.mpr (show (bad a ∩ bad b).Nonempty from ⟨w,mem_inter.mpr ⟨wa,wb⟩⟩)
    have ac := bs a am
    have bc := bs b bm
    have cc := bs c cm
    have lim : (bad a∪bad b).card≤3 := by omega
    have up := card_union_le (bad a∪bad b) (bad c)
    have eq : M.biUnion bad=(bad a∪bad b)∪bad c := by
      rw [re]
      simp [union_assoc]
    rw [eq] at major
    omega
  obtain ⟨w,wm,zw⟩ := mem_biUnion.mp (all z (sub zm))
  have wxyz : w=x ∨ w=y ∨ w=z := by simpa [repr] using wm
  rcases wxyz with rfl|rfl|rfl
  · apply no_pair ym zm xm (repr.trans ?_) hxy (sym _ zm _ xm zw)
    ext v; simp; tauto
  · apply no_pair xm zm ym (repr.trans ?_) (sym _ xm _ ym hxy) (sym _ zm _ ym zw)
    ext v; simp; tauto
  · exact diag _ wm zw

/-- One vertex resolves any at-most-three marked vertices of a six-board
when each marked vertex has degree at least three in the board. -/
theorem one_center_of_six (G : SimpleGraph V) [DecidableRel G.Adj]
    (T M : Finset V) (ts : T.card=6) (sub : M⊆T) (ms : M.card≤3)
    (deg : ∀ x∈M,3≤nbr G x T) :
    ∃ b∈T, ∀ x∈M, x=b ∨ G.Adj x b := by
  classical
  let bad (x : V) := (T.erase x).filter (fun y => ¬G.Adj x y)
  have bound (x : V) (xm : x∈M) : (bad x).card≤2 := by
    have same : (T.erase x).filter (G.Adj x)=T.filter (G.Adj x) := by
      ext y
      simp only [mem_filter,mem_erase]
      exact ⟨fun h=>⟨h.1.2,h.2⟩,fun h=>⟨⟨h.2.ne.symm,h.1⟩,h.2⟩⟩
    have c := filter_card_add_filter_neg_card_eq_card (s:=T.erase x) (G.Adj x)
    rw [same,card_erase_of_mem (sub xm),ts] at c
    change _+(bad x).card=6-1 at c
    have d : 3≤(T.filter (G.Adj x)).card := deg x xm
    omega
  obtain ⟨b,bt,bn⟩ := small_symmetric_bad_family T M ts sub ms bad bound
    (fun x _ h => (mem_erase.mp (mem_filter.mp h).1).1 rfl)
    (fun x _ y ym h => mem_filter.mpr ⟨mem_erase.mpr ⟨
      (mem_erase.mp (mem_filter.mp h).1).1.symm,sub ym⟩,
      fun xy => (mem_filter.mp h).2 xy.symm⟩)
  refine ⟨b,bt,fun x xm => ?_⟩
  by_cases eq : x=b
  · exact Or.inl eq
  by_cases xy : G.Adj x b
  · exact Or.inr xy
  exfalso
  exact bn (mem_biUnion.mpr ⟨x,xm,mem_filter.mpr ⟨mem_erase.mpr ⟨Ne.symm eq,bt⟩,xy⟩⟩)

#print axioms small_symmetric_bad_family
#print axioms one_center_of_six
end Graffiti384b.DiversityEleven
