import ThetaSevenFaithfulBoundary
import ThetaSevenFaithfulLocalCut

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaSevenFaithfulCost
open SquareCap (boundary)
open PentagonProfile (Port)
open ThetaSevenFaithfulCap (ambient candidate edges3 edges9 core3 core9 wire3 wire9)
open ThetaSevenFaithfulBoundary (glue_boundary)
open ThetaSevenFaithfulLocalCut (cost capWires oldWires exact_cap_wires exact_old_wires)
noncomputable section

private def orient {W : Type*} (c : W→Bool) (a b : W) : W×W := if c a then (a,b) else (b,a)

private theorem listed_boundary {W : Type*} [Fintype W] [LinearOrder W]
    (G : SimpleGraph W) (E : List (W×W))
    (adj : ∀ x y,G.Adj x y ↔ (x,y)∈E ∨ (y,x)∈E)
    (sorted : ∀ x y : W,(x,y)∈E→x<y) (nodup : E.Nodup) (c : W→Bool) :
    (boundary G c).card = E.countP (fun e=>c e.1 != c e.2) := by
  classical
  let S := E.toFinset.filter (fun e=>c e.1≠c e.2)
  let o (e : W×W) := orient c e.1 e.2
  have shape : boundary G c = S.image o := by
    ext ⟨u,v⟩
    have m : (u,v)∈boundary G c ↔ c u=true ∧ c v=false ∧ G.Adj u v := by
      simp [boundary]
    constructor
    · intro h
      obtain ⟨ho,hc,ed⟩ := m.mp h
      rcases (adj u v).mp ed with a|b
      · exact mem_image.mpr ⟨(u,v),mem_filter.mpr ⟨List.mem_toFinset.mpr a,by simp [ho,hc]⟩,
          by simp [o,orient,ho]⟩
      · exact mem_image.mpr ⟨(v,u),mem_filter.mpr ⟨List.mem_toFinset.mpr b,by simp [ho,hc]⟩,
          by simp [o,orient,hc]⟩
    · intro h
      obtain ⟨⟨u',v'⟩,hs,eq⟩ := mem_image.mp h
      obtain ⟨he,nd⟩ := mem_filter.mp hs
      have connected : G.Adj u' v' := (adj _ _).mpr (Or.inl (List.mem_toFinset.mp he))
      change c u' ≠ c v' at nd
      have mm (x y : W) : (x,y)∈boundary G c ↔ c x=true ∧ c y=false ∧ G.Adj x y := by
        simp [boundary]
      have useful : o (u',v') ∈ boundary G c := by
        cases eu : c u' <;> cases ev : c v'
        · exact (nd (eu.trans ev.symm)).elim
        · exact (mm v' u').mpr ⟨ev,eu,connected.symm⟩ |> fun hh => by simpa [o,orient,eu] using hh
        · exact (mm u' v').mpr ⟨eu,ev,connected⟩ |> fun hh => by simpa [o,orient,eu] using hh
        · exact (nd (eu.trans ev.symm)).elim
      exact eq ▸ useful
  have used (e : W×W) (h : e∈S) : e.1<e.2 :=
    sorted e.1 e.2 (List.mem_toFinset.mp (mem_filter.mp h).1)
  have inj : Set.InjOn o (↑S : Set (W×W)) := by
    intro a ha b hb eq
    have na : a.1<a.2 := used a ha
    have nb : b.1<b.2 := used b hb
    have cancel (h : a = b.swap) : False := by
      rw [h] at na
      exact (not_lt_of_ge (le_of_lt nb)) na
    have ca : o a=a ∨ o a=a.swap := by
      rcases a with ⟨x,y⟩
      cases z : c x <;> simp [o,orient,z]
    have cb : o b=b ∨ o b=b.swap := by
      rcases b with ⟨x,y⟩
      cases z : c x <;> simp [o,orient,z]
    rcases ca with p|p <;> rcases cb with q|q <;> rw [p,q] at eq
    · exact eq
    · exact (cancel eq).elim
    · exact (cancel (by simpa only [Prod.swap_swap] using congrArg Prod.swap eq)).elim
    · simpa only [Prod.swap_swap] using congrArg Prod.swap eq
  rw [shape,card_image_of_injOn inj,List.countP_eq_length_filter]
  have same : S = (E.filter (fun e=>c e.1 != c e.2)).toFinset := by
    ext z
    simp [S,and_comm]
  rw [same]
  exact List.toFinset_card_of_nodup (nodup.filter _)


private theorem list_wire_count {T : Type*} [Fintype T]
    (W : List (Port × T)) (nd : W.Nodup) (wire : Port→T→Bool)
    (exactWire : ∀ i j,wire i j=true ↔ (i,j)∈W) (c : Port→Bool) (s : T→Bool) :
    ((univ : Finset (Port × T)).filter (fun e=>wire e.1 e.2=true ∧ c e.1≠s e.2)).card =
    W.countP (fun e=>c e.1 != s e.2) := by
  classical
  let z : Port×T→Bool := fun e=>c e.1 != s e.2
  have same : ((univ : Finset (Port × T)).filter (fun e=>wire e.1 e.2=true ∧ c e.1≠s e.2))=
      (W.filter z).toFinset := by
    ext ⟨i,j⟩
    simp [z,exactWire,and_comm]
  rw [same,List.toFinset_card_of_nodup (nd.filter _),List.countP_eq_length_filter]

variable {V : Type*} [Fintype V]
theorem ambient_boundary (B : SimpleGraph V) (p : Port↪V) (c : V→Bool) (s : Fin 9→Bool) :
    (boundary (ambient B p) (Sum.elim c s)).card =
      (boundary B c).card+cost edges9 oldWires (c ∘ p) s := by
  unfold ambient
  rw [glue_boundary,
    listed_boundary core9 edges9 (fun _ _=>Iff.rfl) (by decide) (by decide)]
  have ww := list_wire_count oldWires (by decide) wire9 exact_old_wires (fun i=>c (p i)) s
  rw [ww]
  simp [cost,Nat.add_assoc,Function.comp_def]

theorem candidate_boundary (B : SimpleGraph V) (p : Port↪V) (c : V→Bool) (s : Fin 3→Bool) :
    (boundary (candidate B p) (Sum.elim c s)).card =
      (boundary B c).card+cost edges3 capWires (c ∘ p) s := by
  unfold candidate
  rw [glue_boundary,
    listed_boundary core3 edges3 (fun _ _=>Iff.rfl) (by decide) (by decide)]
  have ww := list_wire_count capWires (by decide) wire3 exact_cap_wires (fun i=>c (p i)) s
  rw [ww]
  simp [cost,Nat.add_assoc,Function.comp_def]

#print axioms ambient_boundary
#print axioms candidate_boundary
end
end KelmansCactus.AtomicBridge.ThetaSevenFaithfulCost
