import SoloCut180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] in
private theorem pull_ind (G : SimpleGraph V) (S A : Finset V) (ai : Indep G A) :
    Indep (side G S) (pull (fun v : ↥S => v.val) A) := fun x xm y ym ne ed =>
  ai x.val (mem_pull.mp xm) y.val (mem_pull.mp ym) (fun eq => ne (Subtype.ext eq)) ed

/-- The sum of the exact local deletion allowances is no larger than
the global deletion allowance at an articulation. -/
theorem allowance_join {c : V} {S T : Finset V} (s : Split G c S T) (gc : G.Connected)
    (hn : 1<Fintype.card V) (r : ↥S) (p : Bool) (A : Finset V) (ai : Indep G A) :
    allowance (side G S) r p (pull (fun v : ↥S => v.val) A)+
      allowance (side G T) ⟨c,s.both.2⟩ (wingParity s r p) (pull (fun v : ↥T => v.val) A)≤
    allowance G r.val p A := by
  classical
  have big := allowance_eq G gc hn r.val p A ai
  have left := allowance_eq (side G S) (s.connectedL gc) s.largeL r p _ (pull_ind G S A ai)
  have right := allowance_eq (side G T) (s.flip.connectedL gc) s.flip.largeL ⟨c,s.both.2⟩
    (wingParity s r p) _ (pull_ind G T A ai)
  dsimp only at big left right
  have pars := seam_parities s gc r p
  rw [←pars.1] at left
  rw [←pars.2] at right
  have leaves := seam_leaf_tally s gc r (parity G r.val p) A
  have ac := s.tally A
  have pc := s.tally (parity G r.val p)
  have orders := card_union_add_card_inter S T
  rw [s.cover,s.meet,card_univ,card_singleton] at orders
  have leftOrder : Fintype.card ↥(S : Set V)=S.card :=
    (Fintype.card_congr (show ↥(S : Set V)≃↥S from Equiv.refl _)).trans (Fintype.card_coe S)
  have rightOrder : Fintype.card ↥(T : Set V)=T.card :=
    (Fintype.card_congr (show ↥(T : Set V)≃↥T from Equiv.refl _)).trans (Fintype.card_coe T)
  omega

theorem degree_away {c : V} {S T : Finset V} (s : Split G c S T) (a : ↥S) (away : a.val∉T) :
    (side G S).degree a=G.degree a.val := by
  classical
  have eq : push ((side G S).neighborFinset a)=G.neighborFinset a.val := by
    ext x
    constructor
    · intro xm
      obtain ⟨w,wm,rfl⟩ := mem_map.mp xm
      exact (G.mem_neighborFinset _ _).mpr (((side G S).mem_neighborFinset _ _).mp wm)
    · intro xm
      have ed := (G.mem_neighborFinset _ _).mp xm
      have xs := ((s.edges ed).resolve_right (fun h => away h.1)).2
      exact (in_push (F:=(side G S).neighborFinset a) ⟨x,xs⟩).mpr (((side G S).mem_neighborFinset _ _).mpr ed)
  simpa only [card_push,card_neighborFinset_eq_degree] using congrArg card eq

/-- For deficit at most two, saturation of the degree bound at a doubly
marked vertex forces the entire other wing of every cut away from it to
be bipartite, irrespective of which wing contains the root. -/
theorem saturated_wing_bip {c : V} {S T : Finset V} (s : Split G c S T) (gc : G.Connected)
    (hn : 1<Fintype.card V) (rk : Fintype.card V≤bipartiteNum G+2) (r : V) (p : Bool) (A : Finset V)
    (ai : Indep G A) (a : ↥S) (away : a.val∉T) (am : a.val∈A) (pm : a.val∈parity G r p)
    (sat : G.degree a.val=allowance G r p A+2) : TwoColor (side G T) univ := by
  classical
  let L := pull (fun v : ↥S => v.val) A
  let R := pull (fun v : ↥T => v.val) A
  have deg := degree_away s a away
  have high := (side G S).degree_lt_card_verts a
  have close (u : ↥S) (q : Bool) (w : ↥T) (t : Bool)
      (par : pull (fun v : ↥S => v.val) (parity G r p)=parity (side G S) u q)
      (sum : allowance (side G S) u q L + allowance (side G T) w t R≤allowance G r p A) :
      TwoColor (side G T) univ := by
    have pin : a∈L∩insert u (parity (side G S) u q) :=
      mem_inter.mpr ⟨mem_pull.mpr am,mem_insert_of_mem (par ▸ mem_pull.mpr pm)⟩
    have pay := protected_degree (side G S) (s.connectedL gc) (by omega) u a q L (pull_ind G S A ai) pin
    have rank := RootEar.deficit_induced G T 2 rk
    have same : Fintype.card ↥(T : Set V)=Fintype.card ↥T := Fintype.card_congr (Equiv.refl _)
    have rest := rank_allowance (side G T) (s.flip.connectedL gc) s.flip.largeL (by omega) w t R (pull_ind G T A ai)
    by_contra non
    have pos := nonbip_order (side G T) non
    omega
  rcases s.either r with rs|rt
  · let u : ↥S := ⟨r,rs⟩
    exact close u p ⟨c,s.both.2⟩ _ (seam_parities s gc u p).1 (allowance_join s gc hn u p A ai)
  · let w : ↥T := ⟨r,rt⟩
    have cap := allowance_join s.flip gc hn w p A ai
    exact close ⟨c,s.both.1⟩ _ w p (seam_parities s.flip gc w p).2 (Nat.add_comm .. ▸ cap)

#print axioms allowance_join
#print axioms degree_away
#print axioms saturated_wing_bip
end Minimal180.PairRepair
