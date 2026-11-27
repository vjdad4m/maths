import P5CliqueMixedPairOptional133
import P5CliqueMixedFivePairFrame133
import P5CliqueFiveMixedOmit0
import P5CliqueFiveMixedOmit1
import P5CliqueFiveMixedOmit2
import P5CliqueFiveMixedOmit3
import P5CliqueFiveMixedOmit4

namespace Graffiti133P5CliqueArms.FivePairFrame
open SimpleGraph Finset Graffiti133 Graffiti133Camby MixedPairCertificate
open scoped Classical
set_option maxHeartbeats 7000000
set_option maxRecDepth 140000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def annotatedModel : Fin 5→Model 17 := ![fivePairOmitModel0,fivePairOmitModel1,fivePairOmitModel2,fivePairOmitModel3,fivePairOmitModel4]

def tableAgreement (b : Fin 5) (x y : Fin 17) : Prop :=
  optionalCode (annotatedModel b) x y=none →
  fixed b (decode x) (decode y)=some (((annotatedModel b).forced x).testBit y.val)

instance (b : Fin 5) (x y : Fin 17) : Decidable (tableAgreement b x y) := by
  unfold tableAgreement
  infer_instance

private theorem agree0 : ∀ x y : Fin 17, tableAgreement 0 x y := by decide
private theorem agree1 : ∀ x y : Fin 17, tableAgreement 1 x y := by decide
private theorem agree2 : ∀ x y : Fin 17, tableAgreement 2 x y := by decide
private theorem agree3 : ∀ x y : Fin 17, tableAgreement 3 x y := by decide
private theorem agree4 : ∀ x y : Fin 17, tableAgreement 4 x y := by decide

private theorem agree (b : Fin 5) (x y : Fin 17) : tableAgreement b x y := by
  fin_cases b
  · exact agree0 x y
  · exact agree1 x y
  · exact agree2 x y
  · exact agree3 x y
  · exact agree4 x y

private theorem annotated_forbidden (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (b : Fin 5) (m : Nat) (e : Fin 17→V) (ei : Function.Injective e)
    (fit : ∀ x y,G.Adj (e x) (e y)↔edge (annotatedModel b) m x y=true) : False := by
  fin_cases b
  · exact five_pair_omit_0_forbidden h4 h9 m e ei fit
  · exact five_pair_omit_1_forbidden h4 h9 m e ei fit
  · exact five_pair_omit_2_forbidden h4 h9 m e ei fit
  · exact five_pair_omit_3_forbidden h4 h9 m e ei fit
  · exact five_pair_omit_4_forbidden h4 h9 m e ei fit

theorem five_pair_host_forbidden (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (p : Fin 4→V) (q : Fin 5→V) (L : Fin 8→V) (b : Fin 5)
    (H : Host G D p q L b) : False := by
  let e := value p q L ∘ decode
  have ei := (value_injective h4 H).comp decode_inj
  have fit0 (x y : Fin 17) (none : optionalCode (annotatedModel b) x y=none) :
      (G.Adj (e x) (e y)↔((annotatedModel b).forced x).testBit y.val=true) :=
    fixed_sound h4 H (decode x) (decode y) _ (agree b x y none)
  obtain ⟨m,fit⟩ := optional_edges_fill (annotatedModel b) e fit0
  exact annotated_forbidden h4 h9 b m e ei fit

private theorem parent_not_omitted (b : Fin 5) (a : Fin 8) : parentSite b a≠b := by
  have cert : ∀ b : Fin 5,∀ a : Fin 8,parentSite b a≠b := by decide
  exact cert b a

/-- In the exact two-contact five-site pattern, four sites cannot be high.
The foreign leaves are chosen in the actual graph, not assumed. -/
theorem five_pair_four_high_forbidden (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (p : Fin 4→V) (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (ind : ∀ i j,¬G.Adj (p i) (p j))
    (attach : ∀ x∉D,∃ i,G.Adj x (p i))
    (palette : ∀ x∉D,∀ w∈D,G.Adj x w→∃ i,w=p i)
    (q : Fin 5→V) (out : ∀ i,q i∉D)
    (contact : ∀ i j,G.Adj (q i) (p j)↔j∈siteMask i)
    (b : Fin 5) (high : ∀ i≠b,3<localIndependence G (q i)) : False := by
  classical
  have stars (i : Fin 5) (ih : i≠b) :
      ∃ S : Finset V, (∀ v∈S,G.Adj (q i) v) ∧ (∀ v∈S,∀ w∈S,¬G.Adj v w) ∧
        ∀ j, j∉siteMask i→∃ v∈S,v∉D ∧ ∀ x∈D,G.Adj v x↔x=p j := by
    obtain ⟨S,adj,ind,h⟩ := mixed_high_has_joint_pure_foreign_representatives
      h4 D p pm pi attach palette _ (out i) (high i ih)
    refine ⟨S,adj,ind,?_⟩
    intro j miss
    exact h j (fun e=>miss ((contact i j).mp e))
  choose S sa si sr using stars
  let W (i : Fin 5) := if h : i≠b then S i h else ∅
  have member (a : Fin 8) : ∃ v∈W (parentSite b a),v∉D ∧
      ∀ w∈D,G.Adj v w↔w=p (leafColor b a) := by
    simp only [W,dif_pos (parent_not_omitted b a)]
    exact sr _ _ _ (foreign_leaf_color b a)
  choose L lm lout lpure using member
  have arm (a : Fin 8) : G.Adj (q (parentSite b a)) (L a) := by
    have x := lm a
    simp only [W,dif_pos (parent_not_omitted b a)] at x
    exact sa _ _ _ x
  have siblings (a c : Fin 8) (_ : a≠c) (eq : parentSite b a=parentSite b c) :
      ¬G.Adj (L a) (L c) := by
    have xa := lm a
    have xc := lm c
    rw [←eq] at xc
    simp only [W,dif_pos (parent_not_omitted b a)] at xa xc
    exact si _ _ _ xa _ xc
  exact five_pair_host_forbidden h4 h9 D p q L b
    ⟨pm,pi,ind,out,contact,lout,lpure,arm,siblings⟩

#print axioms five_pair_host_forbidden
#print axioms five_pair_four_high_forbidden
end Graffiti133P5CliqueArms.FivePairFrame
