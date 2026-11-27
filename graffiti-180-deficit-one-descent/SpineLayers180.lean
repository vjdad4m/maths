import SpineBridge180

set_option warningAsError true
namespace Minimal180.DescentOne
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem vertical_adj {J : SimpleGraph V} {r u v : V} (uv : J.Adj u v)
    (step : J.dist v r=J.dist u r+1) (odd : Bool) :
    (alternating J (parity J r odd)).Adj u v := by
  refine ⟨uv,?_⟩
  simp only [mem_parity,step]
  cases odd <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega

/-- After cutting the first spine edge in the alternating graph, each
later spine vertex is separated from the root, while every other vertex
at its distance is still reachable. -/
theorem separated_layers {J : SimpleGraph V} (jc : J.Connected) {r t s : V} {D : Finset V}
    (sp : Spine J r D t) (sd : s∈D) (ts : Arc J r t s) (odd : Bool)
    (broken : ¬(carve J (parity J r odd) t s).Reachable t s) :
    let K := carve J (parity J r odd) t s
    ∀ i∈D, i≠t → ¬K.Reachable r i ∧ ∀ z, z≠i → J.dist z r=J.dist i r → K.Reachable r z := by
  classical
  intro K
  let H := alternating J (parity J r odd)
  let d (i : V) := J.dist i r
  have ds : d s=d t+1 := ts.2.1
  have use {a b : V} (ab : H.Adj a b) (avoid : ¬((a=t ∧ b=s) ∨ (a=s ∧ b=t))) : K.Adj a b := by
    apply deleteEdges_adj.mpr
    exact ⟨ab,fun pair => avoid (Sym2.eq_iff.mp (Set.mem_singleton_iff.mp pair))⟩
  have shallow (k : ℕ) : ∀ z, d z=k → k≤d t → K.Reachable r z := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro z zk low
      by_cases zr : z=r
      · exact zr ▸ Reachable.refl _
      obtain ⟨p,pz,step⟩ := Graffiti169.exists_predecessor J jc r z zr
      change d z=d p+1 at step
      have cut : K.Adj p z := use (vertical_adj pz.symm step odd) (by
        rintro (⟨_,zs⟩|⟨ps,_⟩)
        · have := congrArg d zs; omega
        · have := congrArg d ps; omega)
      exact (ih (d p) (by omega) p rfl (by omega)).trans cut.reachable
  have tail (k : ℕ) : ∀ i∈D, i≠t → d i=k → K.Reachable s i := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i id it ik
      by_cases is : i=s
      · exact is ▸ Reachable.refl _
      obtain ⟨p,pd,pi⟩ := sp.prior i id it
      have step : d i=d p+1 := pi.2.1
      have pt : p≠t := by
        intro e
        have eq := congrArg d e
        exact is (sp.single i id s sd (by change d i=d s; omega))
      have edge : K.Adj p i := use (vertical_adj pi.1 step odd)
        (fun v => v.elim (fun h => is h.2) (fun h => it h.2))
      exact (ih (d p) (by omega) p pd pt rfl).trans edge.reachable
  have others (k : ℕ) : ∀ i∈D, d i=k → ∀ z, z≠i → d z=k → K.Reachable r z := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i id ik z zi zk
      by_cases it : i=t
      · exact shallow k z zk (by rw [←it,ik])
      obtain ⟨p,pd,pi⟩ := sp.prior i id it
      have di : d i=d p+1 := pi.2.1
      have zr : z≠r := by intro eq; have e : d z=0 := eq ▸ J.dist_self; omega
      obtain ⟨q,qz,dz⟩ := Graffiti169.exists_predecessor J jc r z zr
      change d z=d q+1 at dz
      have qp : q≠p := by
        intro eq
        have e : J.Adj p z := eq ▸ qz.symm
        have dd : d z=d p+1 := by rw [←eq]; exact dz
        exact zi (sp.onward p pd z i e pi.1 dd di)
      have zd : z∉D := fun v => zi (sp.single z v i id (zk.trans ik.symm))
      have edge : K.Adj q z := use (vertical_adj qz.symm dz odd)
        (fun e => e.elim (fun h => zd (h.2 ▸ sd)) (fun h => zd (h.2 ▸ sp.tip)))
      exact (ih (d p) (by omega) p pd rfl q qp (by omega)).trans edge.reachable
  intro i id it
  refine ⟨fun ri => broken (((shallow _ t rfl le_rfl).symm.trans ri).trans (tail _ i id it rfl).symm),?_⟩
  exact fun z zi same => others _ i id rfl z zi same

#print axioms separated_layers
end Minimal180.DescentOne
