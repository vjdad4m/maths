import SignalSemantics
import LocalTable

namespace Graffiti384b.Four29.LocalTest
open Finset SimpleGraph Words LowSample
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Restricted count of unordered triangles at a label in the induced
nine-vertex graph. This count can be checked on any chosen three extra vertices. -/
def localCount (f : Label ↪ V) (i : Label) := (pairs.filter (fun z =>
  decide (G.Adj (f i) (f z.1) ∧ G.Adj (f i) (f z.2) ∧ G.Adj (f z.1) (f z.2)))).length

omit [Fintype V] [DecidableEq V] in
private theorem actual (f : Label ↪ V) (p : ℕ)
    (edges : ∀i j:Label,(edge i j).testBit p=true ↔ G.Adj (f i) (f j)) (i : Label) :
    number p (score i)=localCount G f i := by
  rw [score,binary_at,triangles,List.filter_map,List.length_map,localCount]
  congr 1
  apply List.filter_congr
  intro z _
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply,Nat.testBit_and,Bool.and_eq_true,edges,decide_eq_true_eq,and_assoc]
/-- A tested arrangement pins both ears and leaves every unpinned nonleaf
with degree at least three, so the pinned maximum-cut theorem applies. -/
theorem nine_induced (f : Label ↪ V) (quota : (types G).card≤(nonleaves G).card)
    (ears : ∀z∈twos G,z=f 7 ∨ z=f 8)
    (shape : ∀i j:Label, (7 ≤ i.val ∨ 7 ≤ j.val) → (preset i j=true ↔ G.Adj (f i) (f j)))
    (positive : ∀i∈anchors,2≤localCount G f i)
    (distinctScores : ∀a∈anchors,∀b∈anchors,a≠b → localCount G f a≠localCount G f b) :
    gamma G≤bound G := by
  classical
  obtain ⟨p,small,edges⟩ := represents G f shape
  have pt : (ones 21).testBit p=true := by rw [ones,Nat.testBit_two_pow_sub_one,decide_eq_true_eq]; exact small
  have eq := actual G f p edges
  have rt : rich.testBit p=true := by
    apply (all_at pt _).mpr
    intro w wm
    obtain ⟨i,im,rfl⟩ := List.mem_map.mp wm
    apply at_least_two
    rw [eq i]
    exact positive i im
  have dt : distinct.testBit p=true := by
    apply (all_at pt _).mpr
    intro w wm
    obtain ⟨⟨a,b⟩,ab,rfl⟩ := List.mem_map.mp wm
    obtain ⟨prod,lt⟩ := List.mem_filter.mp ab
    obtain ⟨am,bm⟩ := List.mem_product.mp prod
    apply differ_at
    rw [eq a,eq b]
    exact distinctScores a am b bm (ne_of_lt (of_decide_eq_true lt))
  have bit := congrArg (fun z : ℕ => z.testBit p) table
  simp only [Nat.testBit_and,rt,dt,Bool.true_and] at bit
  obtain ⟨w,wm,yes⟩ := (any_at p _).mp bit
  obtain ⟨⟨P,Q⟩,placement,rfl⟩ := List.mem_map.mp wm
  obtain ⟨no,pd,qd,e7,e8⟩ := pattern_data _ placement
  have split := Bool.and_eq_true_iff.mp (show ((supported P Q).testBit p && (supported Q P).testBit p) = true by
    simpa only [works,Nat.testBit_and] using yes)
  let L := P.toFinset.map f
  let R := Q.toFinset.map f
  have either {z : Label} (m : z∈P ∨ z∈Q) : f z∈L ∨ f z∈R :=
    m.imp (fun h => mem_map.mpr ⟨z,List.mem_toFinset.mpr h,rfl⟩)
      (fun h => mem_map.mpr ⟨z,List.mem_toFinset.mpr h,rfl⟩)
  have lp := support_lift G f pt edges qd split.1
  have rq := support_lift G f pt edges pd split.2
  apply PinnedColor34.complete G (P:=L) (Q:=R) ?_ quota ?_ lp rq
  · apply disjoint_left.mpr
    intro z zl zr
    obtain ⟨i,im,rfl⟩ := mem_map.mp zl
    obtain ⟨j,jm,eq'⟩ := mem_map.mp zr
    exact no i (List.mem_toFinset.mp im) (f.injective eq' ▸ List.mem_toFinset.mp jm)
  · intro z zn zl zr
    by_contra! smallD
    have low : z∈twos G := mem_sdiff.mpr ⟨zn,fun h => (not_le_of_gt smallD) (mem_filter.mp h).2⟩
    rcases ears z low with rfl|rfl
    · exact (either e7).elim zl zr
    · exact (either e8).elim zl zr

/-- Anchor scores agree with the induced counts if the nine labels contain every triangle partner of each anchor. -/
theorem nine_labels (f : Label ↪ V) (quota : (types G).card≤(nonleaves G).card)
    (ears : ∀z∈twos G,z=f 7 ∨ z=f 8)
    (shape : ∀i j:Label, (7 ≤ i.val ∨ 7 ≤ j.val) → (preset i j=true ↔ G.Adj (f i) (f j)))
    (locality : ∀i∈anchors,∀z∈Repair.linkSupport G (f i),z∈Set.range f)
    (positive : ∀i∈anchors,2≤trianglesAt G (f i))
    (distinctScores : ∀a∈anchors,∀b∈anchors,a≠b → trianglesAt G (f a)≠trianglesAt G (f b)) :
    gamma G≤bound G := by
  obtain ⟨p,_,edges⟩ := represents G f shape
  have agrees (i : Label) (ia : i∈anchors) : localCount G f i=trianglesAt G (f i) :=
    (actual G f p edges i).symm.trans (counts G f p edges i (locality i ia))
  apply nine_induced G f quota ears shape
  · intro i ia; rw [agrees i ia]; exact positive i ia
  · intro a am b bm ne; rw [agrees a am,agrees b bm]; exact distinctScores a am b bm ne

end Graffiti384b.Four29.LocalTest
#print axioms Graffiti384b.Four29.LocalTest.nine_induced
#print axioms Graffiti384b.Four29.LocalTest.nine_labels
