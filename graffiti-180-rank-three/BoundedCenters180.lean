import AdmissibleLayers180
import SmallCover180

set_option warningAsError true
namespace Minimal180.HigherRank
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def baseScore (G : SimpleGraph V) [DecidableRel G.Adj] (r : V) (D X : Finset V) : ℕ :=
  (if r∈D then 1 else 0)+(if r∈X then G.degree r-2 else 0)+(entries G r D).card

theorem children_biUnion (G : SimpleGraph V) (r : V) (D B : Finset V) :
    B.biUnion (fun v => children G r D {v})=children G r D B := by
  classical
  ext x
  simp only [mem_biUnion,children,mem_filter,mem_erase,mem_univ,and_true,mem_singleton,
    exists_eq_left]
  constructor
  · rintro ⟨v,vb,xr,ok⟩; exact ⟨xr,v,vb,ok⟩
  · rintro ⟨xr,v,vb,ok⟩; exact ⟨v,vb,xr,ok⟩

/-- If D is nonempty it contributes at least one entry or the root itself. -/
theorem base_pos (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (r : V) (D X : Finset V) (nz : D.Nonempty) : 1≤baseScore G r D X := by
  classical
  by_cases rd : r∈D
  · simp only [baseScore,if_pos rd]; omega
  obtain ⟨x,xd,near⟩ := exists_min_image D (fun z => G.dist z r) nz
  have xr : x≠r := fun eq => rd (eq ▸ xd)
  obtain ⟨y,xy,d⟩ := Graffiti169.exists_predecessor G hc r x xr
  have yd : y∉D := by
    intro hy
    have := near y hy
    change G.dist x r≤G.dist y r at this
    omega
  have entry : x∈entries G r D := mem_filter.mpr ⟨mem_erase.mpr ⟨xr,mem_univ _⟩,xd,y,⟨xy,d⟩,yd⟩
  have pos := card_pos.mpr (show (entries G r D).Nonempty from ⟨x,entry⟩)
  unfold baseScore
  omega

/-- An exact test using at most the outstanding deficit many centers.
All tests quantify only over vertices and their original predecessor edges. -/
theorem small_layer_iff (G : SimpleGraph V) [DecidableRel G.Adj] (r : V) (A P : Finset V) :
    let X := A∪P
    let D := X\(A∩P)
    let m := bipartiteNum G+baseScore G r D X
    LayerTest G r A P ↔ ∃ B⊆X.erase r,B.card≤Fintype.card V-m ∧
      Fintype.card V+B.card≤m+(children G r D B).card := by
  classical
  intro X D m
  have raw : LayerTest G r A P ↔ ∃ B⊆X.erase r,
      Fintype.card V+B.card≤m+(children G r D B).card := by
    unfold LayerTest
    change (∃ B⊆X.erase r,Fintype.card V+B.card≤bipartiteNum G+
      (if r∈D then 1 else 0)+(if r∈X then G.degree r-2 else 0)+score G r D B) ↔ _
    simp only [score_formula,m,baseScore,Nat.add_assoc]
  rw [raw]
  constructor
  · rintro ⟨B,bx,hb⟩
    by_cases done : Fintype.card V≤m
    · exact ⟨∅,empty_subset _,by simp,by simp; omega⟩
    let t := Fintype.card V-m
    have ht : t+m=Fintype.card V := by unfold t; omega
    have target : t+B.card≤(B.biUnion (fun v => children G r D {v})).card := by
      rw [children_biUnion]; omega
    obtain ⟨C,cb,small,budget⟩ := small_surplus B (fun v => children G r D {v}) t target
    rw [children_biUnion] at budget
    exact ⟨C,cb.trans bx,small,by omega⟩
  · rintro ⟨B,bx,_,paid⟩; exact ⟨B,bx,paid⟩

#print axioms children_biUnion
#print axioms base_pos
#print axioms small_layer_iff
end Minimal180.HigherRank
