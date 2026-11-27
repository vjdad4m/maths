import SeamTally180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The protected assertion with an explicit parity set, used to assemble
two restrictions of the same ambient marking. -/
def PinSet (G : SimpleGraph V) (r : V) (P A : Finset V) : Prop :=
  ∃ Z,TwoColor G Z ∧ A∩insert r P⊆Z ∧ 1+A.card+P.card≤weightedLeaves G (eligible A P r)+Z.card

theorem seam_pins {c : V} {S T : Finset V} (s : Split G c S T) (hc : G.Connected)
    (r : ↥S) (P A : Finset V)
    (left : PinSet (side G S) r (pull (fun v : ↥S => v.val) P) (pull (fun v : ↥S => v.val) A))
    (right : PinSet (side G T) ⟨c,s.both.2⟩ (pull (fun v : ↥T => v.val) P) (pull (fun v : ↥T => v.val) A)) :
    PinSet G r.val P A := by
  classical
  obtain ⟨L,lc,lk,lp⟩ := left
  obtain ⟨R,rc,rk,rp⟩ := right
  obtain ⟨Z,col,size,mem⟩ := seam_color s L R lc rc
  refine ⟨Z,col,?_,?_⟩
  · intro x xm
    obtain ⟨xa,sideP⟩ := mem_inter.mp xm
    apply (mem x).mpr
    constructor
    · intro xs
      let l : ↥S := ⟨x,xs⟩
      apply (in_push (F:=L) l).mpr
      refine lk (mem_inter.mpr ⟨mem_pull.mpr xa,?_⟩)
      rcases mem_insert.mp sideP with xr|xp
      · exact mem_insert.mpr (Or.inl (Subtype.ext xr))
      · exact mem_insert_of_mem (mem_pull.mpr xp)
    · intro xt
      let t : ↥T := ⟨x,xt⟩
      apply (in_push (F:=R) t).mpr
      refine rk (mem_inter.mpr ⟨mem_pull.mpr xa,?_⟩)
      rcases mem_insert.mp sideP with xr|xp
      · have seam := s.common (xr ▸ r.property) xt
        exact mem_insert.mpr (Or.inl (Subtype.ext seam))
      · exact mem_insert_of_mem (mem_pull.mpr xp)
  · have ac := s.tally A
    have pc := s.tally P
    have leaves := seam_leaf_tally s hc r P A
    omega

noncomputable def wingParity {c : V} {S T : Finset V} (s : Split G c S T) (r : ↥S) (p : Bool) : Bool :=
  if (side G S).dist ⟨c,s.both.1⟩ r%2=0 then p else !p

theorem seam_parities {c : V} {S T : Finset V} (s : Split G c S T) (hc : G.Connected) (r : ↥S) (p : Bool) :
    pull (fun v : ↥S => v.val) (parity G r.val p) = parity (side G S) r p ∧
    pull (fun v : ↥T => v.val) (parity G r.val p) = parity (side G T) ⟨c,s.both.2⟩ (wingParity s r p) := by
  classical
  have ds := s.distances hc r
  constructor
  · ext v;simp only [mem_pull,mem_parity,ds.1 v]
  · ext v
    simp only [mem_pull,mem_parity,ds.2 v]
    generalize (side G T).dist v ⟨c,s.both.2⟩ = d
    unfold wingParity
    generalize (side G S).dist ⟨c,s.both.1⟩ r = k
    cases p <;> by_cases h : k%2=0 <;> simp [h] <;> omega

/-- Protected witnesses compose at any articulation, including when
the global root is marked outside the chosen parity. -/
theorem protected_join {c : V} {S T : Finset V} (s : Split G c S T) (hc : G.Connected)
    (r : ↥S) (p : Bool) (A : Finset V)
    (left : Protected (side G S) r p (pull (fun v : ↥S => v.val) A))
    (right : Protected (side G T) ⟨c,s.both.2⟩ (wingParity s r p) (pull (fun v : ↥T => v.val) A)) :
    Protected G r.val p A := by
  have eq := seam_parities s hc r p
  apply seam_pins s hc r (parity G r.val p) A
  · rw [eq.1];exact left
  · rw [eq.2];exact right

#print axioms seam_pins
#print axioms seam_parities
#print axioms protected_join
end Minimal180.PairRepair
