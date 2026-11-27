import BicycleRelays133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133 Finset
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} {G : SimpleGraph V}

theorem Relay.empty_separated_left {B : Finset V} {a b c d : V} (P : Relay G B c d) :
    (Relay.empty G B a b).Separated P := fun i => i.elim0

theorem Relay.empty_separated_right {B : Finset V} {a b c d : V} (P : Relay G B a b) :
    P.Separated (Relay.empty G B c d) := fun _ j => j.elim0

structure ThetaRelays (G : SimpleGraph V) (u v : V) where
  rel : Fin 3 → Relay G {u,v} u v
  sep : ∀ i j, i≠j → (rel i).Separated (rel j)
  direct : G.Adj u v ↔ ∃ i,(rel i).n=0
  atMostOneEmpty : ∀ i j,(rel i).n=0 → (rel j).n=0 → i=j

structure DumbRelays (G : SimpleGraph V) (u v : V) where
  first : Relay G {u,v} u u
  mid : Relay G {u,v} u v
  last : Relay G {u,v} v v
  longFirst : 2≤first.n
  longLast : 2≤last.n
  f_m : first.Separated mid
  f_l : first.Separated last
  m_l : mid.Separated last
  direct : G.Adj u v ↔ mid.n=0

private noncomputable def enum {W : Type*} {n : Nat} (S : Finset W) (hc : S.card=n) :
    Fin n ≃ {x // x∈S} :=
  (Fintype.equivFinOfCardEq ((Fintype.card_coe S).trans hc)).symm

private theorem loop_ne_cross {B : Finset V} (F : TaggedFamily G B)
    {z : V} {S T : {S // S∈F.sets}} (l : S∈F.loopsAt z) (r : T∈F.crosses) : S≠T := by
  intro eq
  subst T
  have cc := (Finset.mem_filter.mp r).2
  obtain ⟨a,b⟩ := (Finset.mem_filter.mp l).2
  exact cc (a.trans b.symm)

private theorem loop_ne_loop {B : Finset V} (F : TaggedFamily G B)
    {u v : V} (uv : u≠v) {S T : {S // S∈F.sets}} (l : S∈F.loopsAt u) (r : T∈F.loopsAt v) : S≠T := by
  intro eq
  subst T
  exact uv ((Finset.mem_filter.mp l).2.1.symm.trans (Finset.mem_filter.mp r).2.1)

theorem TaggedFamily.theta_relays_of_counts {u v : V} [DecidableRel G.Adj]
    (F : TaggedFamily G ({u,v} : Finset V))
    (count : F.crosses.card + (if G.Adj u v then 1 else 0) = 3) :
    Nonempty (ThetaRelays G u v) := by
  classical
  by_cases E : G.Adj u v
  · have two : F.crosses.card=2 := by rw [if_pos E] at count; omega
    let e := enum F.crosses two
    let R (i : Fin 2) := F.crossRelay (e i).val (e i).property
    let C : Fin 3 → Relay G ({u,v} : Finset V) u v :=
      Fin.cases (Relay.empty G _ u v) (fun i => (R i).relay)
    have pair : (R 0).relay.Separated (R 1).relay :=
      F.relays_separate (fun eq=> (show (0:Fin 2)≠1 from by decide)
        (e.injective (Subtype.ext eq))) (R 0) (R 1)
    refine ⟨⟨C,?_,⟨fun _=>⟨0,rfl⟩,fun _=>E⟩,?_⟩⟩
    · intro i j eq
      fin_cases i <;> fin_cases j
      all_goals first | contradiction | exact Relay.empty_separated_left _ | exact Relay.empty_separated_right _ | exact pair | exact pair.symm
    · have aux (i : Fin 3) (h : (C i).n=0) : i=0 := by
        revert h
        refine Fin.cases ?_ (fun j => ?_) i
        · intro _
          rfl
        · intro hv
          exact (Nat.ne_of_gt (R j).pos hv).elim
      intro i j hi hj
      exact (aux i hi).trans (aux j hj).symm
  · have three : F.crosses.card=3 := by simpa [E] using count
    let e := enum F.crosses three
    let R (i : Fin 3) := F.crossRelay (e i).val (e i).property
    refine ⟨⟨fun i=>(R i).relay,
      fun i j ne=>F.relays_separate (fun eq=>ne (e.injective (Subtype.ext eq))) (R i) (R j),
      ⟨fun z=>(E z).elim,?_⟩,?_⟩⟩
    · rintro ⟨i,ie⟩
      exact (Nat.ne_of_gt (R i).pos ie).elim
    · intro i _ ie _
      exact (Nat.ne_of_gt (R i).pos ie).elim

theorem TaggedFamily.dumb_relays_of_counts {u v : V} [DecidableRel G.Adj] (uv : u≠v)
    (F : TaggedFamily G ({u,v} : Finset V))
    (left : (F.loopsAt u).card=1) (right : (F.loopsAt v).card=1)
    (count : F.crosses.card + (if G.Adj u v then 1 else 0) = 1) :
    Nonempty (DumbRelays G u v) := by
  classical
  obtain ⟨S,Ss⟩ : (F.loopsAt u).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨T,Ts⟩ : (F.loopsAt v).Nonempty := Finset.card_pos.mp (by omega)
  let L := F.loopRelay u S Ss
  let R := F.loopRelay v T Ts
  have LR := F.relays_separate (loop_ne_loop F uv Ss Ts) L R
  have first := F.loopRelay_long u S Ss
  have last := F.loopRelay_long v T Ts
  by_cases er : G.Adj u v
  · let M : Relay G {u,v} u v := Relay.empty G _ u v
    exact ⟨⟨L.relay,M,R.relay,first,last,
      Relay.empty_separated_right _,LR,Relay.empty_separated_left _,⟨fun _=>rfl,fun _=>er⟩⟩⟩
  · have cross : F.crosses.card=1 := by simpa [er] using count
    obtain ⟨W,Ws⟩ : F.crosses.Nonempty := Finset.card_pos.mp (by omega)
    let M := F.crossRelay W Ws
    have LM := F.relays_separate (loop_ne_cross F Ss Ws) L M
    have MR := (F.relays_separate (loop_ne_cross F Ts Ws) R M).symm
    exact ⟨⟨L.relay,M.relay,R.relay,first,last,LM,LR,MR,
      ⟨fun z=>(er z).elim,fun e=>(Nat.ne_of_gt M.pos e).elim⟩⟩⟩

theorem two_degree_three_has_relay_networks {u v : V} [Fintype V] [DecidableRel G.Adj]
    (hc : G.Connected) (uv : u≠v) (du : G.degree u=3) (dv : G.degree v=3)
    (outside : ∀ x, x≠u → x≠v → G.degree x=2) :
    Nonempty (ThetaRelays G u v) ∨ Nonempty (DumbRelays G u v) := by
  classical
  obtain ⟨F⟩ := tag_all_degree_two_components (G:=G) hc {u,v} (by simp)
    (fun x h => outside x (fun e=>h (by simp [e])) (fun e=>h (by simp [e])))
  rcases F.two_degree_three_partition uv du dv with ⟨_,_,e⟩|⟨l,r,e⟩
  · exact Or.inl (F.theta_relays_of_counts e)
  · exact Or.inr (F.dumb_relays_of_counts uv l r e)

#print axioms two_degree_three_has_relay_networks
end Graffiti133Bicycle
