import OddMinimum189
import DiracThreshold189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.ActiveStarHeight Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.Normalize Graffiti189LongestPath.OddMinimum Graffiti189LongestPath.DiracThreshold
open Graffiti189LongestPath.StarConnectivity Graffiti189LongestPath.StarCycleClosure Graffiti189LongestPath.ShoreDegrees
open private Graffiti189LongestPath.Rigidity.mem_omittedStar from Rigidity189
set_option warningAsError true
set_option maxHeartbeats 6500000
universe u
namespace Graffiti189LongestPath.SeparatedDirac
variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- All normalized separated-double heights h≥11 close from the ordinary
Dirac-length cycle in the root-deleted shore, including the exact
extremal cycle at the odd minimum height. -/
theorem separated_double_no_dirac_length_cycle (hc : G.Connected) (k : Nat) (hk : 7≤k)
    (cap : ∀ v,(EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V,S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    (fail : ¬∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ z,z∈q.support)
    {a b x y : V} {p : G.Walk a b} (hp : EdgeMinAvoid (k+2) p) (hx : x∉p.support)
    (hy : y∉p.support) (xy : G.Adj x y)
    (double : (Pins p x).card=2) (sep : PairedPins p x=∅)
    (high : k+2≤G.degree x)
    (large : 10<(OmittedStar p x).card)
    (cyc : ∃ a, ∃ c : (G.induce (((OmittedStar p x).erase x : Finset V) : Set V)).Walk a a,
      c.IsCycle ∧ 2*((OmittedStar p x).card/2-1)≤c.length) : False := by
  by_cases h : (OmittedStar p x).card=k+1 ∧ (OmittedStar p x).card%2=1
  · exact odd_minimum_no_dirac_cycle hc k hk cap conn deg fail hp hx hy xy double sep high
      large h.1 h.2 cyc
  exact separated_double_no_dirac_cycle hc k hk cap conn deg fail hp hx hy xy double sep high
    large (fun mn => by have e : (OmittedStar p x).card%2≠1 := fun o => h ⟨mn,o⟩; omega) cyc

/-- The exact missing ordinary circumference interface, on a graph
with at most one low degree and minimum degree at least two. This is
a hypothesis, not an axiom or a claimed Lean theorem. -/
def OneLowCircumference : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (m : Nat), 2≤m → 3≤Fintype.card W →
    (∀ X : Finset W,X.card<2 → (H.induce ((↑X : Set W)ᶜ)).Connected) →
    (∀ v : W,2≤H.degree v) →
    (∀ u v : W,u≠v → m≤H.degree u ∨ m≤H.degree v) →
    ∃ a, ∃ c : H.Walk a a,c.IsCycle ∧ min (Fintype.card W) (2*m)≤c.length

/-- A checked assembly with a named explicit circumference premise.
At d≥12, it leaves no separated-double geometry beyond that premise. -/
theorem separated_double_of_one_low_circumference (pos : OneLowCircumference.{u})
    (hc : G.Connected) (k : Nat) (hk : 10≤k)
    (cap : ∀ v,(EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V,S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    (fail : ¬∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ z,z∈q.support)
    {a b x y : V} {p : G.Walk a b} (hp : EdgeMinAvoid (k+2) p) (hx : x∉p.support)
    (hy : y∉p.support) (xy : G.Adj x y)
    (double : (Pins p x).card=2) (sep : PairedPins p x=∅)
    (high : k+2≤G.degree x) : False := by
  classical
  let A := OmittedStar p x
  let T := A.erase x
  let W := ↥(T : Set V)
  let J := G.induce (T : Set V)
  let m := A.card/2-1
  have xt : x∈A := Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have h : k+1≤A.card := by
    have e := star_card_degree_and_pins hp.1.1 hx
    change A.card+(Pins p x).card=G.degree x+1 at e
    omega
  have wc : Fintype.card W=A.card-1 := by
    change Fintype.card ↥T=A.card-1
    exact (Fintype.card_coe T).trans (card_erase_of_mem xt)
  have del (S : Finset W) (sc : S.card<2) :
      (J.induce ((↑S : Set W)ᶜ)).Connected := by
    let e : W ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
    let X := insert x (S.map e)
    have xs : X⊆A := by
      intro v vx
      rcases mem_insert.mp vx with rfl|h
      · exact xt
      · obtain ⟨w,_,rfl⟩ := mem_map.mp h
        exact (mem_erase.mp w.property).2
    have xl := (card_insert_le x (S.map e)).trans (by rw [card_map])
    change X.card≤S.card+1 at xl
    have sz : 3*X.card+4<(OmittedStar p x).card := by change 3*X.card+4<A.card; omega
    have con := separated_double_star_stays_connected hc k (by omega) cap conn deg fail
      hp.1.1 hx hy xy double sep X xs sz
    exact (erase_root_and_set_iso (G:=G) A x S).connected_iff.mp con
  have low (v : W) : 2≤J.degree v := by
    have dg := (separated_root_deleted_degrees hc k (by omega) cap conn deg fail hp.1.1
      hx hy xy double sep v).1
    change A.card≤2*J.degree v+5 at dg
    omega
  have highJ (v : W) (vh : k+2≤G.degree v.val) : m≤J.degree v := by
    have dg := (separated_root_deleted_degrees hc k (by omega) cap conn deg fail hp.1.1
      hx hy xy double sep v).2 vh
    change A.card≤2*J.degree v+3 at dg
    dsimp [m]
    omega
  have pair (u v : W) (ne : u≠v) : m≤J.degree u ∨ m≤J.degree v :=
    (deg u.val v.val (fun e => ne (Subtype.ext e))).imp (highJ u) (highJ v)
  have mc : 2≤m := by dsimp [m]; omega
  obtain ⟨r,c,cc,cl⟩ := pos W J m mc (by omega) del low pair
  have mm : 2*m≤Fintype.card W := by dsimp [m]; omega
  rw [min_eq_right mm] at cl
  have big : 10<(OmittedStar p x).card := by change 10<A.card; omega
  exact separated_double_no_dirac_length_cycle hc k (by omega) cap conn deg fail
    hp hx hy xy double sep high big ⟨r,c,cc,cl⟩

#print axioms separated_double_no_dirac_length_cycle
#print axioms separated_double_of_one_low_circumference
end Graffiti189LongestPath.SeparatedDirac
