import CliqueMinusEdgeRoute189
import OreClosure189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {J : SimpleGraph V} [DecidableRel J.Adj]
set_option linter.unusedSectionVars false

/-- Rooted Ore with a single protected pair: complete all allowable high
pairs, then use a spanning route in the clique minus that pair. The root
comes from a prescribed class of at least three vertices. -/
theorem rooted_Ore_except_pair
    (hc : J.Connected) (K B : Finset V) (roots : 3≤K.card) (bad : B.card≤2)
    (enough : B.card≤1 ∨ 6≤Fintype.card V)
    (high : V→Prop)
    (oneLow : ∀ u v,u≠v → high u ∨ high v)
    (cap : ∀ u v,high u → high v → u≠v → ¬(u∈B ∧ v∈B) →
      Fintype.card V≤J.degree u+J.degree v) :
    ∃ r∈K,RootedSpan J r := by
  classical
  let A : Finset V := univ.filter high
  have high_iff (v : V) : v∈A ↔ high v := by simp [A]
  let H : SimpleGraph V :=
    ⟨fun u v=>J.Adj u v ∨ (u∈A ∧ v∈A ∧ u≠v ∧ ¬(u∈B ∧ v∈B)),
      by
        intro u v
        rintro (e|⟨ua,va,uv,avoid⟩)
        · exact .inl e.symm
        exact .inr ⟨va,ua,uv.symm,fun h=>avoid ⟨h.2,h.1⟩⟩,
      by intro u; rintro (e|⟨_,_,e,_⟩); exact J.loopless _ e; exact e rfl⟩
  have sub : J≤H := fun _ _ h=>.inl h
  have ok (u v : V) (uv : H.Adj u v) (no : ¬J.Adj u v) :
      Fintype.card V≤J.degree u+J.degree v := by
    change J.Adj u v ∨ _ at uv
    obtain ⟨ua,va,ne,h⟩ := uv.resolve_left no
    exact cap u v ((high_iff u).mp ua) ((high_iff v).mp va) ne h
  have pick (u v : V) : ∃ w∈K,w≠u ∧ w≠v := by
    have n : ¬K⊆({u,v} : Finset V) := by
      intro s
      have c := card_le_card s
      have m := card_insert_le u ({v} : Finset V)
      rw [card_singleton] at m
      omega
    obtain ⟨w,wk,h⟩ := not_subset.mp n
    exact ⟨w,wk,fun e=>h (by simp [e]),fun e=>h (by simp [e])⟩
  have high_path (aBound : B.card≤1 ∨ 5≤A.card) {u v : V} (ua : u∈A) (va : v∈A)
      (uv : u≠v) : RouteOn H A u v := by
    by_cases tiny : B.card≤1
    · have ck : CompleteOn H A := by
        intro w wa z za wz
        apply Or.inr
        refine ⟨wa,za,wz,?_⟩
        intro nz
        have k := one_lt_card.mpr ⟨w,nz.1,z,nz.2,wz⟩
        omega
      obtain ⟨p,pp,ps⟩ := path_between_in_clique A ck ua va uv
      exact ⟨p,pp,ps⟩
    have sz : B.card=2 := by omega
    obtain ⟨e,f,ef,eq⟩ := card_eq_two.mp sz
    apply route_between_in_clique_except_pair A (aBound.resolve_left tiny) (e:=e) (f:=f) _ ua va uv
    intro w wa z za wz n
    apply Or.inr
    refine ⟨wa,za,wz,?_⟩
    intro hz
    have wb : w=e ∨ w=f := by simpa [eq] using hz.1
    have zb : z=e ∨ z=f := by simpa [eq] using hz.2
    rcases wb with rfl|rfl <;> rcases zb with rfl|rfl
    · exact wz rfl
    · exact n (.inl ⟨rfl,rfl⟩)
    · exact n (.inr ⟨rfl,rfl⟩)
    exact wz rfl
  by_cases low : ∃ z,¬high z
  · obtain ⟨z,zlow⟩ := low
    have aEq : A=univ.erase z := by
      ext v
      rw [high_iff]
      by_cases vz : v=z
      · simp [vz,zlow]
      have hv := (oneLow v z vz).resolve_right zlow
      simp [hv,vz]
    have aBound : B.card≤1 ∨ 5≤A.card := by
      rcases enough with h|h
      · exact .inl h
      apply Or.inr
      rw [aEq,card_erase_of_mem (mem_univ _),card_univ]
      omega
    obtain ⟨b,_,bz,_⟩ := pick z z
    obtain ⟨p⟩ := hc.preconnected z b
    have meet : ∃ w,J.Adj z w := by
      cases p with
      | nil => exact (bz rfl).elim
      | @cons _ w _ e p => exact ⟨w,e⟩
    obtain ⟨w,zw⟩ := meet
    obtain ⟨r,rk,rz,rw⟩ := pick z w
    have ra : r∈A := by simp [aEq,rz]
    have wa : w∈A := by simp [aEq,zw.ne.symm]
    have p := high_path aBound ra wa rw
    have eq : insert z A=(univ : Finset V) := by
      rw [aEq,insert_erase (mem_univ _)]
    have full : RouteOn H univ r z :=
      eq ▸ p.suffix (sub zw.symm) (by simp [aEq])
    obtain ⟨q,qp,qs⟩ := full
    refine ⟨r,rk,Graffiti189Ore.rooted_closure sub r ok ?_⟩
    exact ⟨z,q,qp,fun x=>(qs x).mpr (mem_univ _)⟩
  have aEq : A=(univ : Finset V) := by
    ext v
    have vh : high v := Classical.byContradiction (fun n=>low ⟨v,n⟩)
    simp [high_iff,vh]
  have aBound : B.card≤1 ∨ 5≤A.card := by
    rcases enough with h|h
    · exact .inl h
    exact .inr (by rw [aEq,card_univ]; omega)
  obtain ⟨r,rk,s,sk,rs⟩ := one_lt_card.mp (show 1<K.card by omega)
  have p : RouteOn H A r s := high_path aBound (by simp [aEq]) (by simp [aEq]) rs
  have full : RouteOn H univ r s := aEq ▸ p
  obtain ⟨q,qp,qs⟩ := full
  refine ⟨r,rk,Graffiti189Ore.rooted_closure sub r ok ?_⟩
  exact ⟨s,q,qp,fun x=>(qs x).mpr (mem_univ _)⟩

#print axioms rooted_Ore_except_pair
end Graffiti189LongestPath.CrossSaturation
