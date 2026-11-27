import DefectOneGain180

set_option warningAsError true
namespace Minimal180.CutGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Pendant decoration converts #177 into a bound for any prescribed
set of eligible leaves and any independent subset of that set. -/
theorem weighted177 (G : SimpleGraph V) (con : G.Connected) (n : 1<Fintype.card V)
    (U Q : Finset V) (ind : Indep G Q) (inc : Q⊆U) :
    2*Q.card+1≤weightedLeaves G U+bipartiteNum G := by
  classical
  obtain ⟨r,_,_⟩ := Fintype.one_lt_card_iff.mp n
  let D := univ\U
  let H := decorate G D
  have cardH : Fintype.card (Deco D)=Fintype.card V+D.card := by simp [Deco]
  have high : 1<Fintype.card (Deco D) := by omega
  have hc := (deco_layers G con r D).1
  have dis : Disjoint Q D := disjoint_left.mpr fun _ h d => (mem_sdiff.mp d).2 (inc h)
  have a := indep_card_le H (deco_indep G D Q ind dis)
  rw [card_disjSum,card_univ,Fintype.card_coe] at a
  have bound := Graffiti177.conjecture177 H hc high
  have degree := (secondDegree_properties H hc high).1
  have b := deco_bip G D
  have ell := deco_leaves G n D univ
  have all : (univ : Finset V).disjSum (univ : Finset ↥D)=univ := by ext v; cases v <;> simp
  have mask : univ\D=U := by ext x; simp [D]
  rw [all,weighted_all,mask] at ell
  change maxLeaves H≤weightedLeaves G U+D.card at ell
  change bipartiteNum H≤bipartiteNum G+D.card at b
  omega

/-- A no-gain tight transition rules out every independent witness
on the eligible vertices having at least half the total mark count. -/
theorem TightCut.independent_obstruction {J : SimpleGraph V} {S T : Finset V} {x y w : V}
    {r : ↥S} {odd : Bool} {A : Finset V} (h : TightCut J S T x y w r odd A) :
    let G := J⊔edge x y
    let P := parity G r.val odd
    let U := eligible A P r.val
    ¬weightedLeaves J U<weightedLeaves G U →
      ∀ Q⊆U, Indep G Q → 2*Q.card<A.card+P.card := by
  intro G P U ng Q inc ind
  have old := h.tight
  change weightedLeaves J U+bipartiteNum J=1+A.card+P.card at old
  have rank : bipartiteNum J=bipartiteNum G+1 := h.rank
  have bound := weighted177 G (h.connected.mono le_sup_left) (by have := h.order; omega) U Q ind inc
  omega

#print axioms weighted177
#print axioms TightCut.independent_obstruction
end Minimal180.CutGain
