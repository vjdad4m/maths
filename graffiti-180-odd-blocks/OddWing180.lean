import Seam180
import BipartiteSparse180

set_option warningAsError true
namespace Minimal180.OddBlock
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In a nonbipartite wing, deleting any vertex compulsory in all maximum
global bipartite sets leaves a nonbipartite wing. -/
theorem mandatory_survives {J : SimpleGraph V} {w z : V} {S T : Finset V}
    (s : Split J w S T) (odd : ¬TwoColor J S)
    (seam : ∀ B, MaxSet J B → w∈B) (forced : ∀ B, MaxSet J B → z∈B) : ¬TwoColor J (S.erase z) := by
  classical
  intro small
  obtain ⟨B,bip,size⟩ := optB J
  have zb := forced B ⟨bip,size⟩
  obtain ⟨f,hf⟩ := (color_function J B).mp bip
  obtain ⟨c,hc⟩ := (color_function J _).mp small
  have missing : ¬S⊆B := fun inc => odd ((color_function J S).mpr
    ⟨f,fun i hi j hj e => hf i (inc hi) j (inc hj) e⟩)
  obtain ⟨q,qs,qb⟩ := Finset.not_subset.mp missing
  have qz : q≠z := fun h => qb (h ▸ zb)
  let L := insert q (B.erase z)
  have zL : z∉L := by simp [L,qz.symm]
  have old {v : V} (vl : v∈L) (vs : v∉S) : v∈B := mem_of_mem_erase
    ((mem_insert.mp vl).resolve_left (fun h => vs (h ▸ qs)))
  let d (v : V) := if c w=f w then c v else !(c v)
  have dw : d w=f w := by dsimp [d]; cases c w <;> cases f w <;> decide
  have pd {a b : V} (al : a∈L) (bl : b∈L) (aS : a∈S) (bS : b∈S) (e : J.Adj a b) : d a≠d b := by
    have k := hc a (mem_erase.mpr ⟨fun h => zL (h ▸ al),aS⟩) b
      (mem_erase.mpr ⟨fun h => zL (h ▸ bl),bS⟩) e
    by_cases h : c w=f w <;> simp [d,h,k]
  have bridge {a b : V} (bl : b∈L) (aS : a∈S) (bo : b∉S) (e : J.Adj a b) :
      d a≠f b := by
    have aw : a=w := by
      rcases s.edges e with k|k
      · exact (bo k.2).elim
      · exact s.common aS k.1
    have ab : a∈B := aw ▸ seam B ⟨bip,size⟩
    have eq : d a=f a := aw ▸ dw
    rw [eq]
    exact hf a ab b (old bl bo) e
  have col : TwoColor J L := by
    apply (color_function J L).mpr
    refine ⟨fun v => if v∈S then d v else f v,?_⟩
    intro a al b bl e
    by_cases aS : a∈S <;> by_cases bS : b∈S
    · simpa only [if_pos aS,if_pos bS] using pd al bl aS bS e
    · simpa only [if_pos aS,if_neg bS] using bridge bl aS bS e
    · simpa only [if_neg aS,if_pos bS] using (bridge al bS aS e.symm).symm
    · simpa only [if_neg aS,if_neg bS] using hf a (old al aS) b (old bl bS) e
  have card : L.card=B.card := by
    change (insert q (B.erase z)).card=B.card
    rw [card_insert_of_not_mem (fun h => qb (mem_of_mem_erase h)),card_erase_add_one zb]
  exact zL (forced L ⟨col,card.trans size⟩)

/-- A proper nontrivial wing has odd obstructions avoiding either attachment
vertex individually. The two surviving sets need not be the same. -/
def OddWing (J : SimpleGraph V) (S : Finset V) (x w : V) : Prop :=
  (side J S).Connected ∧ NoCut (side J S) ∧
  (S={x,w} ∨ (¬TwoColor J (S.erase w) ∧ ¬TwoColor J (S.erase x)))

private theorem strong_wing {J : SimpleGraph V} (jc : J.Connected) {x y w r : V} {S T : Finset V}
    (s : Split J w S T) (xs : x∈S) (ys : y∉S) (xy : x≠y) (xw : J.Adj x w)
    (block : NoCut (J⊔edge x y)) (sp : SparseAt (J⊔edge x y) r)
    (drop : bipartiteNum (J⊔edge x y)<bipartiteNum J) : OddWing J S x w := by
  obtain ⟨noc,h⟩ := wing_odd jc s xs ys xw block sp
  refine ⟨s.connectedL jc,noc,?_⟩
  rcases h with h|h
  · exact Or.inl h
  · right
    have pin := fun B (top : MaxSet J B) => locked_seam s xs ys xy drop top
    exact ⟨mandatory_survives s h (fun B t => (pin B t).2.1) (fun B t => (pin B t).2.1),
      mandatory_survives s h (fun B t => (pin B t).2.1) (fun B t => (pin B t).1)⟩

/-- Structural alternative for the lower graph of the horizontal triangle
branch of order at least four. Neither lower tightness nor the horizontal
distance hypothesis is needed for the stronger conclusion stated here. -/
theorem odd_block_alternative (J : SimpleGraph V) (jc : J.Connected) (hn : 3<Fintype.card V)
    (x y w r : V) (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (block : NoCut (J⊔edge x y)) (sp : SparseAt (J⊔edge x y) r)
    (drop : bipartiteNum J=bipartiteNum (J⊔edge x y)+1) :
    ¬TwoColor J univ ∧
      (NoCut J ∨ ∃ S T, Split J w S T ∧ x∈S ∧ x∉T ∧ y∈T ∧ y∉S ∧
        OddWing J S x w ∧ OddWing J T y w ∧
        (∀ B, MaxSet J B → x∈B ∧ w∈B ∧ y∈B) ∧ (S≠{x,w} ∨ T≠{y,w})) := by
  classical
  constructor
  · intro bip
    have eq : bipartiteNum J=Fintype.card V := le_antisymm (by
      obtain ⟨B,_,h⟩ := optB J
      rw [←h]
      exact B.card_le_univ) (by simpa only [card_univ] using size_bip J bip)
    have size := (PrivateCore.bipartite_lower_triangle_order J jc (by omega) x y w r xy old xw wy block sp eq drop).2
    omega
  by_cases noc : NoCut J
  · exact Or.inl noc
  right
  obtain ⟨c,S,T,s⟩ := split_of_cut noc
  obtain ⟨eq,ends⟩ := chord_seam s block xw wy
  subst c
  have orient : ∃ S T,Split J w S T ∧ x∈S ∧ x∉T ∧ y∈T ∧ y∉S := by
    rcases ends with ⟨a,b,c,d⟩|⟨a,b,c,d⟩
    · exact ⟨S,T,s,a,b,c,d⟩
    · exact ⟨T,S,s.flip,a,b,c,d⟩
  obtain ⟨L,R,p,xL,xR,yR,yL⟩ := orient
  have d : bipartiteNum (J⊔edge x y)<bipartiteNum J := by omega
  have left := strong_wing jc p xL yL xy xw block sp d
  have flip : J⊔edge y x=J⊔edge x y := by rw [edge_comm y x]
  have right := strong_wing jc p.flip yR xR xy.symm wy.symm (flip ▸ block) (flip ▸ sp) (flip ▸ d)
  refine ⟨L,R,p,xL,xR,yR,yL,left,right,fun _ => locked_seam p xL yL xy d,?_⟩
  by_contra! both
  have cap := card_union_add_card_inter L R
  rw [p.cover,p.meet,card_univ,card_singleton,both.1,both.2,card_pair xw.ne,card_pair wy.ne.symm] at cap
  omega

#print axioms mandatory_survives
#print axioms odd_block_alternative
end Minimal180.OddBlock
