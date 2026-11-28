import DiversityElevenPendantSix384b
import ThreeUntouched384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
open private Graffiti384b.DiversityEleven.cubic_pair_nonadjacent from ThreeUntouched384b
open private Repair.nbr_add from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The pendant branch closes whenever the eight-vertex board has an
internal degree-two vertex. Its ambient degree is three, and distinct
triangle scores force both its board neighbors to have degree at least four. -/
theorem exact_of_pendant_board_degree_two (select : SixSelector)
    (sup : Supported G) (t : (types G).card=11) (nine : (high G).card=9)
    {e f a q : V} (ah : a∈high G) (low : nonleaves G \ high G={e,f})
    (en : G.neighborFinset e={f,a}) (fn : G.neighborFinset f={e,a})
    (qh : q∈(high G).erase a) (qd : nbr G q ((high G).erase a)=2)
    (scores : Set.InjOn (trianglesAt G) (high G : Set V))
    (mins : ∀ v∈high G, 2≤trianglesAt G v) : gamma G≤bound G := by
  classical
  let B := (high G).erase a
  have loc {v : V} (vB : v∈B) := pendant_board_local G sup ah low en fn vB
  have highD {v : V} (vB : v∈B) : 3≤G.degree v :=
    (mem_filter.mp (mem_erase.mp vB).2).2
  have qa : G.Adj q a := by
    by_contra! na
    have d := (loc qh).2
    rw [qd,if_neg na] at d
    have big := highD qh
    omega
  have q3 : G.degree q=3 := by
    have d := (loc qh).2
    rw [qd,if_pos qa] at d
    omega
  obtain ⟨p,r,_pr,pair⟩ := card_eq_two.mp qd
  have pm : p∈B.filter (G.Adj q) := pair ▸ mem_insert_self _ _
  have ph : p∈B := (mem_filter.mp pm).1
  have qp : G.Adj q p := (mem_filter.mp pm).2
  have out {w : V} (qw : G.Adj q w) : w=a ∨ w=p ∨ w=r := by
    by_cases wa : w=a
    · exact Or.inl wa
    have b : w∈B := mem_erase.mpr ⟨wa,(loc qh).1 w qw⟩
    have m : w∈B.filter (G.Adj q) := mem_filter.mpr ⟨b,qw⟩
    rw [pair,mem_insert,mem_singleton] at m
    exact Or.inr m
  have higher {v : V} (vB : v∈B) (vq : G.Adj v q) : 4≤G.degree v := by
    by_contra! d
    have v3 : G.degree v=3 := by have d' := highD vB; omega
    have vh := (mem_erase.mp vB).2
    have qh' := (mem_erase.mp qh).2
    have diff : trianglesAt G v≠trianglesAt G q := fun eq => vq.ne (scores vh qh' eq)
    exact Graffiti384b.DiversityEleven.cubic_pair_nonadjacent G v3 q3 (mins _ vh) (mins _ qh') diff vq
  let U := (B.erase p).erase q
  have splitd {v : V} (vB : v∈B) :
      G.degree v = nbr G v U + (if G.Adj v q then 1 else 0) +
        (if G.Adj v p then 1 else 0) + (if G.Adj v a then 1 else 0) := by
    have qb : q∈B.erase p := mem_erase.mpr ⟨qp.ne,qh⟩
    have first : U∪{q}=B.erase p := by rw [union_comm,←insert_eq,show U=(B.erase p).erase q from rfl,insert_erase qb]
    have second : B.erase p∪{p}=B := by rw [union_comm,←insert_eq,insert_erase ph]
    have dsq : Disjoint U {q} := disjoint_left.mpr (fun _ h y => (mem_erase.mp h).1 (mem_singleton.mp y))
    have dsp : Disjoint (B.erase p) {p} := disjoint_left.mpr (fun _ h y => (mem_erase.mp h).1 (mem_singleton.mp y))
    have s (x : V) : nbr G v {x}=(if G.Adj v x then 1 else 0) := by
      unfold nbr
      rw [filter_singleton]
      split <;> simp
    have dq := Repair.nbr_add G v dsq
    have dp := Repair.nbr_add G v dsp
    rw [first,s q] at dq
    rw [second,s p,dq] at dp
    exact ((loc vB).2.symm.trans (by rw [show ((high G).erase a)=B from rfl,dp]))
  have el : e∉high G := (mem_sdiff.mp (low ▸ mem_insert_self _ _)).2
  have fl : f∉high G := (mem_sdiff.mp (low ▸ mem_insert_of_mem (mem_singleton_self _))).2
  have ea : G.Adj e a := (G.mem_neighborFinset ..).mp (en ▸ mem_insert_of_mem (mem_singleton_self _))
  have ef : G.Adj e f := (G.mem_neighborFinset ..).mp (en ▸ mem_insert_self _ _)
  apply exact_of_pendant_six G select t nine ea ef ah el fl ph qh qa qp scores mins
  · intro _U v vU va vp
    have vB := (mem_erase.mp (mem_erase.mp vU).2).2
    have ds := splitd vB
    rw [if_neg va,if_neg vp] at ds
    refine ⟨?_,?_⟩
    · change 3≤nbr G v U
      by_cases vq : G.Adj v q
      · rw [if_pos vq] at ds
        have d := higher vB vq
        omega
      · rw [if_neg vq] at ds
        have d := highD vB
        omega
    · have nobody {z w : V} (vz : G.Adj v z) (vw : G.Adj v w) (zw : G.Adj z w) : z≠q := by
        intro eq
        subst z
        have eqv : v=r := (out vz.symm).resolve_left (mem_erase.mp vB).1 |>.resolve_left
          (mem_erase.mp (mem_erase.mp vU).2).1
        rcases out zw with wa|wp|wr
        · exact va (wa ▸ vw)
        · exact vp (wp ▸ vw)
        · exact vw.ne (eqv.trans wr.symm)
      intro x y vx vy xy
      have inside {z : V} (vz : G.Adj v z) (zq : z≠q) : z∈U :=
        mem_erase.mpr ⟨zq,mem_erase.mpr ⟨fun h=>vp (h ▸ vz),
          mem_erase.mpr ⟨fun h=>va (h ▸ vz),(loc vB).1 z vz⟩⟩⟩
      exact ⟨inside vx (nobody vx vy xy),inside vy (nobody vy vx xy.symm)⟩
  · intro _U v vU one
    change 2≤nbr G v U
    have vB := (mem_erase.mp (mem_erase.mp vU).2).2
    have ds := splitd vB
    have c : G.degree v=(nbr G v U)+(if G.Adj v q then 1 else 0)+1 := by
      rcases one with ⟨va,vp⟩|⟨vp,va⟩
      · rw [if_pos va,if_neg vp] at ds
        omega
      · rw [if_pos vp,if_neg va] at ds
        omega
    by_cases vq : G.Adj v q
    · rw [if_pos vq] at c
      have d := higher vB vq
      omega
    · rw [if_neg vq] at c
      have d := highD vB
      omega

#print axioms exact_of_pendant_board_degree_two
end Graffiti384b.DiversityEleven
