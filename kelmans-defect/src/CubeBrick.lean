import Substitute
import Mathlib.Data.Fintype.Powerset
namespace KelmansCactus.CubeBrick
open Finset ThreePort Substitute

private def CubeAdj (u v : Fin 8) : Prop :=
  u.val ^^^ v.val = 1 ∨ u.val ^^^ v.val = 2 ∨ u.val ^^^ v.val = 4
private instance (u v : Fin 8) : Decidable (CubeAdj u v) := by unfold CubeAdj; infer_instance

private theorem sym : ∀ u v, CubeAdj u v → CubeAdj v u := by decide
private theorem noLoop : ∀ u, ¬ CubeAdj u u := by decide

def cube : SimpleGraph (Fin 8) :=
  ⟨CubeAdj,fun {u v} => sym u v,noLoop⟩
private instance (u v : Fin 8) : Decidable (cube.Adj u v) := by unfold cube; infer_instance

def W : Finset (Fin 8) := {1,2,3,4,5,6,7}
def ports : Fin 3 → Fin 8 := ![1,2,4]

private def leafF (i j : Fin 3) : Finset (Fin 8) := if i=j then {ports i} else ∅
private def leafP (i : Fin 3) : Finset (Finset (Fin 8)) :=
  if i=0 then {{3,2,6},{4,5,7}} else if i=1 then {{3,1,5},{4,6,7}} else {{3,1,5},{2,6,7}}

private def spare (i j k : Fin 3) : Fin 8 :=
  if k=0 then 3
  else if k=1 then if i=0 ∨ j=0 then 6 else 3
  else if i=0 ∨ j=0 then 5 else 6
private def centerF (i j k : Fin 3) : Finset (Fin 8) :=
  if k=i ∨ k=j then {ports k,spare i j k} else ∅
private def centerP (i j : Fin 3) : Finset (Finset (Fin 8)) :=
  if ¬(i=0 ∨ j=0) then {{1,5,7}}
  else if ¬(i=1 ∨ j=1) then {{2,6,7}} else {{4,5,7}}

private def Raw (w : Fin 3 → Nat) (F : Fin 3 → Finset (Fin 8))
    (P : Finset (Finset (Fin 8))) : Prop :=
  (∀ i, (F i).card = w i ∧ F i ⊆ W ∧ ((F i).Nonempty → ports i ∈ F i) ∧
    ∀ v ∈ F i, v ≠ ports i → cube.Adj (ports i) v) ∧
  ((∀ i j, i≠j → Disjoint (F i) (F j)) ∧
    (∀ t ∈ P, t.card=3 ∧ ∃ c ∈ t, ∀ v ∈ t, v≠c → cube.Adj c v) ∧
    (∀ s ∈ P, ∀ t ∈ P, s≠t → Disjoint s t) ∧
    P.biUnion id = W \ univ.biUnion F)

private instance (w : Fin 3 → Nat) (F : Fin 3 → Finset (Fin 8)) (P : Finset (Finset (Fin 8))) :
    Decidable (Raw w F P) := by
  unfold Raw
  letI first (i : Fin 3) : Decidable ((F i).card = w i ∧ F i ⊆ W ∧
    ((F i).Nonempty → ports i ∈ F i) ∧ ∀ v ∈ F i, v ≠ ports i → cube.Adj (ports i) v) := by
    infer_instance
  letI one (s : Finset (Fin 8)) : Decidable (s.card=3 ∧ ∃ c ∈ s, ∀ v ∈ s, v≠c → cube.Adj c v) := by
    infer_instance
  letI two (s : Finset (Fin 8)) : Decidable (∀ t ∈ P, s ≠ t → Disjoint s t) := by
    exact Finset.decidableDforallFinset
  infer_instance

private theorem ofRaw {w F P} (witness : Raw w F P) :
    Signature (G:=cube) W ports w := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := witness
  refine ⟨F,fun i => ?_,h1,P,⟨h2,h3,h4⟩⟩
  obtain ⟨a,b,c,d⟩ := h0 i
  exact ⟨a,⟨b,c,d⟩⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem cube_mimic : Mimic cube W ports := by
  constructor
  · have a : ∀ i : Fin 3, Raw (fun j => if j=i then 1 else 0) (leafF i) (leafP i) := by decide
    intro i
    exact ofRaw (a i)
  · have a : ∀ i j : Fin 3, i ≠ j →
      Raw (fun k => if k=i ∨ k=j then 2 else 0) (centerF i j) (centerP i j) := by decide
    intro i j ne
    exact ofRaw (a i j ne)

#print axioms cube_mimic
end KelmansCactus.CubeBrick
