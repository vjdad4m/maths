import PinnedDelete180
import ModuleShape180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def SmallerPinned (H : SimpleGraph V) : Prop := ∀ S : Finset V,S.card<Fintype.card V → 1<S.card →
  (side H S).Connected → ∀ r p A,Indep (side H S) A → Pinned (side H S) r p A (A∩parity (side H S) r p)

/-- Every proper nontrivial module consists of the chosen root and
one further vertex. A prime graph satisfies this automatically. -/
def RootPairsOnly (H : SimpleGraph V) (r : V) : Prop := ∀ M : Finset V,Homogeneous H M → 1<M.card →
  M≠univ → r∈M ∧ M.card=2

theorem pin_minimal_module (H : SimpleGraph V) (hc : H.Connected) (high : 2<Fintype.card V)
    (min : SmallerPinned H) (r : V) (p : Bool) (A : Finset V) (ai : Indep H A)
    (bad : ¬Pinned H r p A (A∩parity H r p)) : RootPairsOnly H r := by
  classical
  intro M hom fat proper
  obtain ⟨a,am⟩ := card_pos.mp (show 0<M.card by omega)
  let J := side H (reps M a)
  let f := collapse M a
  let D := A∩parity H r p
  have h := module_bags H M hom a am
  have jc := quotient_connected H hc M hom a am
  have ord := (quotient_order M a am fat proper).1
  have stuck {x y : V} (xm : x∈M) (ym : y∈M) (xr : x≠r) (xy : x≠y)
      (step : x∈D → ∃ t∈D,FalseTwins H x t) : False := by
    obtain ⟨con,large,small,ind,no⟩ := h.pinDelete jc ord high A ai r x y xr xy (members_same M a x y xm ym) p step bad
    exact no (min _ small large con _ p _ ind)
  have marked (x : V) (xm : x∈M) (xr : x≠r) : x∈D := by
    by_contra no
    obtain ⟨y,ym,yx⟩ := exists_ne_of_one_lt_card fat x
    exact stuck xm ym xr yx.symm (fun hit => (no hit).elim)
  have root_edge (rm : r∈M) (x : V) (xm : x∈M) (xr : x≠r) : H.Adj x r ↔ p=true := by
    have m := (mem_parity H r x p).mp (mem_inter.mp (marked x xm xr)).2
    have eq := members_same M a x r xm rm
    constructor
    · intro e
      rw [dist_eq_one_iff_adj.mpr e] at m
      cases p <;> simp_all
    · rintro rfl
      by_contra ne
      have two : H.dist x r=2 := by simpa [eq,xr,ne] using h.metric jc ord x r
      simp [two] at m
  have little : (M.erase r).card≤1 := by
    by_contra! big
    obtain ⟨x,xs,y,ys,xy⟩ := one_lt_card.mp big
    obtain ⟨xr,xm⟩ := mem_erase.mp xs
    obtain ⟨yr,ym⟩ := mem_erase.mp ys
    have xd := marked x xm xr
    have yd := marked y ym yr
    apply stuck xm ym xr xy
    intro _
    refine ⟨y,yd,xy,fun z => ?_⟩
    by_cases zm : z∈M
    · by_cases zr : z=r
      · subst z
        exact (root_edge zm x xm xr).trans (root_edge zm y ym yr).symm
      · have za := (mem_inter.mp (marked z zm zr)).1
        exact iff_of_false (fun e => ai x (mem_inter.mp xd).1 z za e.ne e)
          (fun e => ai y (mem_inter.mp yd).1 z za e.ne e)
    · exact ⟨fun e => ((hom z zm x xm y ym).mp e.symm).symm,fun e => ((hom z zm x xm y ym).mpr e.symm).symm⟩
  by_cases rm : r∈M
  · have ct := card_erase_add_one rm
    exact ⟨rm,by omega⟩
  · rw [erase_eq_of_not_mem rm] at little
    omega

theorem small_pinned (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V) (small : Fintype.card V≤2)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) : Pinned G r p A (A∩parity G r p) := by
  classical
  obtain ⟨x,y,ne⟩ := Fintype.one_lt_card_iff.mp hn
  have un : ({x,y}:Finset V)=univ := eq_univ_of_card _ (by rw [card_pair ne]; omega)
  have bi : TwoColor G univ := ⟨{x},{y},by simp [ne,ne.symm],by simpa using un,by simp [Indep],by simp [Indep]⟩
  have pay := weighted_order G gc hn r p.toNat A ai
  change A.card+(parity G r p).card+1≤Fintype.card V+weightedLeaves G (eligible A (parity G r p) r) at pay
  exact ⟨univ,bi,subset_univ _,by rw [card_univ]; omega⟩

/-- Exact universal reduction. Only roots with no incident dominating
edge and no proper nontrivial module other than a pair containing that
root need be tested, using a witness containing the double marking. -/
theorem universal_iff_root_pairs : Assembly180.Universal.{u} ↔
    ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W),G.Connected →
      2<Fintype.card W → ∀ r,RootPairsOnly G r → (∀ y,¬DomEdge G r y) → ∀ p A,Indep G A →
        Pinned G r p A (A∩parity G r p) := by
  constructor
  · intro all W _ _ G gc hn r _ _ p A ai
    exact universal_pins all G gc hn r p A _ ai Subset.rfl
  · intro test
    have prove (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W) (gc : G.Connected)
        (hn : 1<Fintype.card W) : ∀ r p A,Indep G A → Pinned G r p A (A∩parity G r p) := by
      generalize eq : Fintype.card W=n at *
      induction n using Nat.strong_induction_on generalizing W with
      | h n ih =>
        intro r p A ai
        have ord : 1<Fintype.card W := by omega
        by_cases enough : 2<Fintype.card W
        · by_contra bad
          have min : SmallerPinned G := by
            intro S small order con
            exact ih (Fintype.card ↥S) (by rw [Fintype.card_coe,←eq]; exact small) ↥S (side G S) con rfl
              (by simpa only [Fintype.card_coe] using order)
          have form := pin_minimal_module G gc enough min r p A ai bad
          have no (y : W) (e : DomEdge G r y) := bad (dominating_pins G gc enough e p A ai)
          exact bad (test W G gc enough r form no p A ai)
        · exact small_pinned G gc ord (by omega) r p A ai
    apply universal_iff_pinned_blocks.mpr
    intro W _ _ G gc hn _ r _ p A ai
    exact prove W G gc (by omega) r p A ai

#print axioms pin_minimal_module
#print axioms small_pinned
#print axioms universal_iff_root_pairs
end Minimal180.Substitution
