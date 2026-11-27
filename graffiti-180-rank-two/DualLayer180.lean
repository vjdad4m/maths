import OutsideIndependent180

set_option warningAsError true
namespace Minimal180.RootEar
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain DescentOne
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two disagreements at a common depth exhaust that layer of the whole
graph. All vertices at smaller depths are disagreements as well. -/
theorem dual_layer {G : SimpleGraph V} {r : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) :
    let P := parity G r odd
    let D := (A∪P)\(A∩P)
    ∀ {a b}, a∈D → b∈D → a≠b → G.dist a r=G.dist b r →
      (∀ z, G.dist z r=G.dist a r → z=a ∨ z=b) ∧
      (∀ z, G.dist z r≤G.dist a r → z∈D) := by
  classical
  intro P D
  let d (z : V) := G.dist z r
  have go (k : ℕ) : ∀ a∈D, ∀ b∈D, a≠b → d a=k → d b=k →
      (∀ z,d z=k → z=a ∨ z=b) ∧ (∀ z,d z≤k → z∈D) := by
    induction k with
    | zero =>
      intro a _ b _ ne da db
      exact (ne ((h.connected.dist_eq_zero_iff.mp da).trans (h.connected.dist_eq_zero_iff.mp db).symm)).elim
    | succ k ih =>
      intro a ad b bd ne da db
      have nz {z : V} (dz : d z=k+1) : z≠r := by
        intro eq; have zero : d z=0 := eq ▸ G.dist_self; omega
      obtain ⟨p,ap,stepA⟩ := Graffiti169.exists_predecessor G h.connected r a (nz da)
      obtain ⟨q,bq,stepB⟩ := Graffiti169.exists_predecessor G h.connected r b (nz db)
      have pd := predecessor_closed h ad ap stepA
      have qd := predecessor_closed h bd bq stepB
      change d a=d p+1 at stepA
      change d b=d q+1 at stepB
      by_cases base : k=0
      · have cover : G.neighborFinset r={a,b} := Eq.symm (eq_of_subset_of_card_le (insert_subset
          ((G.mem_neighborFinset ..).mpr (dist_eq_one_iff_adj.mp (by change d a=1; omega)).symm)
          (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr (dist_eq_one_iff_adj.mp (by change d b=1; omega)).symm)))
          (by rw [card_neighborFinset_eq_degree,h.root_degree,card_pair ne]))
        have layer (z : V) (dz : d z=k+1) : z=a ∨ z=b := by
          have m := (G.mem_neighborFinset r z).mpr (dist_eq_one_iff_adj.mp (by change d z=1; omega)).symm
          simpa only [cover,mem_insert,mem_singleton] using m
        refine ⟨layer,fun z dz => ?_⟩
        by_cases zero : d z=0
        · exact (h.connected.dist_eq_zero_iff.mp zero) ▸ (show r∈D from h.root_disagreement)
        · exact (layer z (by omega)).elim (fun eq => eq ▸ ad) (fun eq => eq ▸ bd)
      · have pr : p≠r := by intro eq; have dr : d p=0 := eq ▸ G.dist_self; omega
        have qr : q≠r := by intro eq; have dr : d q=0 := eq ▸ G.dist_self; omega
        have pq : p≠q := fun eq => ne (h.outward (mem_sdiff.mp pd).1 pr ap.symm (eq ▸ bq.symm)
          stepA (by simpa only [eq] using stepB))
        obtain ⟨previous,covered⟩ := ih p pd q qd pq (by omega) (by omega)
        have layer (z : V) (dz : d z=k+1) : z=a ∨ z=b := by
          obtain ⟨v,zv,step⟩ := Graffiti169.exists_predecessor G h.connected r z (nz dz)
          change d z=d v+1 at step
          rcases previous v (by omega) with vp|vq
          · subst v; exact Or.inl (h.outward (mem_sdiff.mp pd).1 pr zv.symm ap.symm step stepA)
          · subst v; exact Or.inr (h.outward (mem_sdiff.mp qd).1 qr zv.symm bq.symm step stepB)
        refine ⟨layer,fun z dz => ?_⟩
        by_cases low : d z≤k
        · exact covered z low
        · exact (layer z (by omega)).elim (fun eq => eq ▸ ad) (fun eq => eq ▸ bd)
  exact fun {a b} ad bd ne eq => go _ a ad b bd ne rfl eq.symm

omit [Fintype V] [DecidableEq V] in
/-- A singleton distance layer of positive depth in a block cannot have
any vertex beyond it. -/
theorem last_singleton {G : SimpleGraph V} (gc : G.Connected) (block : NoCut G)
    {r v : V} (vr : v≠r) (single : ∀ z,G.dist z r=G.dist v r → z=v) :
    ∀ z,G.dist z r≤G.dist v r := by
  classical
  intro z
  by_contra! deeper
  have zv : z≠v := fun eq => (Nat.lt_irrefl _ (eq ▸ deeper))
  let H := G.induce ({v}ᶜ : Set V)
  let X := ↥({v}ᶜ : Set V)
  let start : X := ⟨r,vr.symm⟩
  let finish : X := ⟨z,zv⟩
  obtain ⟨w⟩ := block v start finish
  let low (a : X) := G.dist a.val r<G.dist v r
  have keep {a b : X} (ab : H.Adj a b) (la : low a) : low b := by
    have bound := gc.dist_triangle (u:=b.val) (v:=a.val) (w:=r)
    rw [dist_eq_one_iff_adj.mpr (show G.Adj a.val b.val from ab).symm] at bound
    have diff : G.dist b.val r≠G.dist v r := fun eq => b.property (single _ eq)
    change G.dist a.val r<G.dist v r at la
    change G.dist b.val r<G.dist v r
    omega
  have walk {a b : X} (p : H.Walk a b) : low a → low b := by
    induction p with
    | nil => exact id
    | cons ab _ ih => exact fun la => ih (keep ab la)
  have pos : 0<G.dist v r := Nat.pos_of_ne_zero (fun eq => vr (gc.dist_eq_zero_iff.mp eq))
  have first : low start := by change G.dist r r<G.dist v r; rw [dist_self]; exact pos
  have endLow := walk w first
  change G.dist z r<G.dist v r at endLow
  omega

#print axioms dual_layer
#print axioms last_singleton
end Minimal180.RootEar
