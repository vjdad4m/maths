import Seam180

set_option warningAsError true
namespace Minimal180.OddBlock
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Both attachments are compulsory in every largest bipartite induced
subgraph of the individual wing. -/
def PinnedWing (J : SimpleGraph V) (S : Finset V) (a b : ↥S) : Prop :=
  ∀ B, MaxSet (side J S) B → a∈B ∧ b∈B

omit [Fintype V] in
private theorem restrict_bip {J : SimpleGraph V} (S : Finset V) {B : Finset V} (hb : TwoColor J B) :
    TwoColor (side J S) (pull (fun v : ↥S => v.val) B) :=
  restrict_color _ _ _ Subtype.val_injective (fun h => h) hb

private theorem wing_scores {J : SimpleGraph V} {S T B : Finset V} {w : V}
    (s : Split J w S T) (tb : MaxSet J B) :
    let l := pull (fun v : ↥S => v.val) B
    let r := pull (fun v : ↥T => v.val) B
    l.card≤bipartiteNum (side J S) ∧ r.card≤bipartiteNum (side J T) ∧
    l.card+r.card=bipartiteNum J+weight w B ∧
    bipartiteNum (side J S)+bipartiteNum (side J T)≤bipartiteNum J+1 := by
  exact ⟨size_bip _ (restrict_bip S tb.1),size_bip _ (restrict_bip T tb.1),
    tb.2 ▸ s.tally B,s.bip_join⟩

/-- Any maximum global witness containing the seam is optimal on both
wings and gives the exact additive rank formula. -/
theorem exact_wing_scores {J : SimpleGraph V} {S T B : Finset V} {w : V}
    (s : Split J w S T) (tb : MaxSet J B) (wb : w∈B) :
    MaxSet (side J S) (pull (fun v : ↥S => v.val) B) ∧
    MaxSet (side J T) (pull (fun v : ↥T => v.val) B) ∧
    bipartiteNum (side J S)+bipartiteNum (side J T)=bipartiteNum J+1 := by
  obtain ⟨l,r,eq,h⟩ := wing_scores s tb
  rw [weight,if_pos wb] at eq
  exact ⟨⟨restrict_bip S tb.1,by omega⟩,⟨restrict_bip T tb.1,by omega⟩,by omega⟩

private theorem replace_wing {J : SimpleGraph V} {S T B : Finset V} {w : V} (s : Split J w S T)
    (tb : MaxSet J B) (wb : w∈B) (A : Finset ↥S) (ta : MaxSet (side J S) A) :
    MaxSet J (push A ∪ (B\S)) := by
  classical
  let Z := push A ∪ (B\S)
  obtain ⟨f,hf⟩ := (color_function J B).mp tb.1
  obtain ⟨c,hc⟩ := (color_function (side J S) A).mp ta.1
  let d (v : ↥S) := if c ⟨w,s.both.1⟩=f w then c v else !(c v)
  have dw : d ⟨w,s.both.1⟩=f w := by dsimp [d]; cases c ⟨w,s.both.1⟩ <;> cases f w <;> decide
  let F (v : V) := if h : v∈S then d ⟨v,h⟩ else f v
  have left {v : V} (vz : v∈Z) (vs : v∈S) : (⟨v,vs⟩ : ↥S)∈A :=
    (in_push ⟨v,vs⟩).mp ((mem_union.mp vz).resolve_right (fun h => (mem_sdiff.mp h).2 vs))
  have right {v : V} (vz : v∈Z) (vt : v∈T) : F v=f v ∧ v∈B := by
    by_cases vs : v∈S
    · obtain rfl := s.common vs vt
      exact ⟨by simpa [F,vs] using dw,wb⟩
    · exact ⟨dif_neg vs,(mem_sdiff.mp ((mem_union.mp vz).resolve_left
        (fun h => vs (push_sub _ h)))).1⟩
  have col : TwoColor J Z := by
    apply (color_function J Z).mpr
    refine ⟨F,?_⟩
    intro a az b bz e
    rcases s.edges e with k|k
    · have ne := hc ⟨a,k.1⟩ (left az k.1) ⟨b,k.2⟩ (left bz k.2) e
      simp only [F,dif_pos k.1,dif_pos k.2]
      by_cases h : c ⟨w,s.both.1⟩=f w <;> simp [d,h,ne]
    · obtain ⟨af,ab⟩ := right az k.1
      obtain ⟨bf,bb⟩ := right bz k.2
      rw [af,bf]
      exact hf a ab b bb e
  have d1 : Disjoint (push A) (B\S) := disjoint_left.mpr (fun _ h k => (mem_sdiff.mp k).2 (push_sub _ h))
  have eq := (exact_wing_scores s tb wb).1.2
  rw [←card_push,push_pull] at eq
  have count := card_sdiff_add_card_inter B S
  refine ⟨col,?_⟩
  rw [card_union_of_disjoint d1,card_push,ta.2,←eq,←tb.2]
  omega

private theorem local_pins {J : SimpleGraph V} {x w : V} {S T : Finset V} (s : Split J w S T)
    (xs : x∈S) (pin : ∀ B,MaxSet J B → x∈B ∧ w∈B) :
    PinnedWing J S ⟨x,xs⟩ ⟨w,s.both.1⟩ := by
  obtain ⟨B,col,top⟩ := optB J
  have wb := (pin B ⟨col,top⟩).2
  intro A ta
  obtain ⟨xa,wa⟩ := pin _ (replace_wing s ⟨col,top⟩ wb A ta)
  have mem {z : V} (zs : z∈S) (hz : z∈push A ∪ (B\S)) : (⟨z,zs⟩ : ↥S)∈A :=
    (in_push ⟨z,zs⟩).mp ((mem_union.mp hz).resolve_right (fun h => (mem_sdiff.mp h).2 zs))
  exact ⟨mem xs xa,mem s.both.1 wa⟩

/-- Exact local factorization of the rank-drop test at a triangle seam. -/
theorem seam_rank_iff {J : SimpleGraph V} {x y w : V} {S T : Finset V} (s : Split J w S T)
    (xs : x∈S) (yt : y∈T) (ys : y∉S) (xy : x≠y) (xw : J.Adj x w) (wy : J.Adj w y) :
    bipartiteNum (J⊔edge x y)<bipartiteNum J ↔
    PinnedWing J S ⟨x,xs⟩ ⟨w,s.both.1⟩ ∧ PinnedWing J T ⟨y,yt⟩ ⟨w,s.both.2⟩ := by
  classical
  constructor
  · intro drop
    have pin := fun B (t : MaxSet J B) => locked_seam s xs ys xy drop t
    exact ⟨local_pins s xs (fun B t => ⟨(pin B t).1,(pin B t).2.1⟩),
      local_pins s.flip yt (fun B t => ⟨(pin B t).2.2,(pin B t).2.1⟩)⟩
  · rintro ⟨left,right⟩
    apply (rank_lock_iff J x y xy).mpr
    intro B tb f hf
    have wb : w∈B := by
      by_contra no
      obtain ⟨l,r,eq,cap⟩ := wing_scores s tb
      rw [weight,if_neg no] at eq
      have nl : (pull (fun a : ↥S => a.val) B).card≠bipartiteNum (side J S) :=
        fun h => no (mem_pull.mp (left _ ⟨restrict_bip S tb.1,h⟩).2)
      have nr : (pull (fun a : ↥T => a.val) B).card≠bipartiteNum (side J T) :=
        fun h => no (mem_pull.mp (right _ ⟨restrict_bip T tb.1,h⟩).2)
      omega
    obtain ⟨bl,br,_⟩ := exact_wing_scores s tb wb
    have xb : x∈B := mem_pull.mp (left _ bl).1
    have yb : y∈B := mem_pull.mp (right _ br).1
    refine ⟨xb,yb,?_⟩
    have n := hf x xb w wb xw
    have m := hf w wb y yb wy
    revert n m
    cases f x <;> cases f y <;> cases f w <;> decide

#print axioms exact_wing_scores
#print axioms seam_rank_iff
end Minimal180.OddBlock
