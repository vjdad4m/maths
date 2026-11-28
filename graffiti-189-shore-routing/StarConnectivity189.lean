import ShoreConnectivity189
import SeparatedRootReduction189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.ExactStarShore Graffiti189LongestPath.ShoreConnectivity
open private Graffiti189LongestPath.Rigidity.mem_external Graffiti189LongestPath.Rigidity.mem_omittedStar from Rigidity189
set_option warningAsError true
namespace Graffiti189LongestPath.StarConnectivity
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Actual internal connectivity of a counterexample's normalized exact
separated-double shore, without discarding a possible low-degree vertex. -/
theorem separated_double_star_stays_connected (hc : G.Connected) (k : Nat) (hk : 6≤k)
    (cap : ∀ v,(EvenFrom G v).card≤k+3)
    (conn : ∀ D : Finset V,D.card<k → (G.induce ((↑D : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    (fail : ¬∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ w,w∈q.support)
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p)
    (hx : x∉p.support) (hy : y∉p.support) (xy : G.Adj x y)
    (double : (Pins p x).card=2) (sep : PairedPins p x=∅)
    (X : Finset V) (inside : X⊆OmittedStar p x)
    (small : 3*X.card+4<(OmittedStar p x).card) :
    (G.induce ((↑((OmittedStar p x)\X)):Set V)).Connected := by
  classical
  let A := OmittedStar p x
  let B := External G A
  let U := univ\(A∪B)
  have sat : B.card=k := by
    obtain ⟨_,_,alt⟩ := double_porter_saturated_one_slack hc k hp hx
      double (cap x) conn hy xy
    rcases alt with h|h
    · exact h.2
    · simp [sep] at h
  obtain ⟨i,hi⟩ := card_pos.mp (by omega : 0<(Pins p x).card)
  have large : k≤U.card := opposite_large_of_not_traceable hc k (by omega)
    cap conn deg hp hx (by omega) hi sat fail
  have rA {z : V} (hz : z∈U) : z∉A := fun h =>
    (mem_sdiff.mp hz).2 (mem_union.mpr (Or.inl h))
  have rB {z : V} (hz : z∈U) : z∉B := fun h =>
    (mem_sdiff.mp hz).2 (mem_union.mpr (Or.inr h))
  have ul : ∀ u∈U,∀ v∉U,G.Adj u v → v∈B := by
    intro u hu v hv ed
    have cov : v∈A∪B := Classical.byContradiction
      (fun h => hv (mem_sdiff.mpr ⟨mem_univ _,h⟩))
    exact (mem_union.mp cov).elim (fun h => (rB hu
      (Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨rA hu,v,h,ed.symm⟩)).elim) id
  have ub : Disjoint U B := disjoint_left.mpr (fun _ h h' => rB h h')
  have au : Disjoint A U := disjoint_left.mpr (fun _ h h' => rA h' h)
  have ab : Disjoint A B := disjoint_left.mpr (fun _ h h' =>
    (Graffiti189LongestPath.Rigidity.mem_external.mp h').1 h)
  have cA : ∀ y∈A,∀ z∉A,G.Adj y z → z∈B := fun _ hy _ hz e =>
    Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨hz,_,hy,e⟩
  have r : ∀ z∈A,z=x ∨ G.Adj x z := fun _ h =>
    (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp h).2
  exact universal_shore_stays_connected hc k A B U X x conn sat ab ub au large
    (by omega) cA ul (fun v => distanceTwo_le_of_even (k+2) v (cap v)) r inside small

#print axioms separated_double_star_stays_connected
end Graffiti189LongestPath.StarConnectivity
