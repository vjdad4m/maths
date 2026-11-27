import Pool26
import OuterScore
import OuterSeparation

namespace Graffiti384b.AnchorPairs
open Finset SimpleGraph
open private LowSample.two_degree from LowSample384b
open private Squares29.pair_at from SquareTriple29
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Fix both ears' common neighbor and the two remaining anchors. -/
theorem three_anchors (t : (types G).card=31) (q : (nonleaves G).card=31)
    {e f a b z : V} (ef : e≠f) (ab : a≠b) (az : a≠z) (bz : b≠z)
    (en : G.neighborFinset e={z,a}) (fn' : G.neighborFinset f={z,b}) : gamma G≤bound G := by
  classical
  by_contra! bad
  obtain ⟨hs,es⟩ := TwoEars.profile G t q bad
  obtain ⟨inj,floor,_,_⟩ := Repair.maximal_diversity G (by omega)
  let J : Finset V := {a,b,z}
  let X := high G\J
  let E := LowSample.twos G
  let O : Finset V := {e,f}
  have de : G.degree e=2 := by rw [←card_neighborFinset_eq_degree,en,card_pair az.symm]
  have df : G.degree f=2 := by rw [←card_neighborFinset_eq_degree,fn',card_pair bz.symm]
  have ah := TwoEars.high_anchors G t q bad de
  have bh := TwoEars.high_anchors G t q bad df
  rw [en] at ah; rw [fn'] at bh
  have pins : J⊆high G := insert_subset (ah (by simp)) (insert_subset (bh (by simp)) (singleton_subset_iff.mpr (ah (by simp))))
  have mE {v : V} (d : G.degree v=2) : v∈E := mem_sdiff.mpr
    ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,fun h => by have := (mem_filter.mp h).2; omega⟩
  have oe : O⊆E := insert_subset (mE de) (singleton_subset_iff.mpr (mE df))
  have os : O.card=2 := card_pair ef
  have oeEq : O=E := eq_of_subset_of_card_le oe (by change (LowSample.twos G).card≤O.card; omega)
  have jo : Disjoint J E := disjoint_left.mpr (fun _ jm em => (mem_sdiff.mp em).2 (pins jm))
  have xo : Disjoint X O := disjoint_left.mpr (fun _ m em => (mem_sdiff.mp (oe em)).2 (mem_sdiff.mp m).1)
  have xj : Disjoint X J := disjoint_left.mpr (fun _ m => (mem_sdiff.mp m).2)
  have xs : X.card=26 := by dsimp only [X]; rw [card_sdiff pins,hs]; simp [J,ab,az,bz]
  have inJ (w : V) (wo : w∈O) : G.neighborFinset w⊆J := by
    rcases mem_insert.mp wo with rfl|eq
    · rw [en]; exact insert_subset (by simp [J]) (singleton_subset_iff.mpr (by simp [J]))
    · rw [mem_singleton.mp eq,fn']; exact insert_subset (by simp [J]) (singleton_subset_iff.mpr (by simp [J]))
  have safe (w : V) (wo : w∈O) : 2≤nbr G w (X∪O)ᶜ := by
    have inc : G.neighborFinset w⊆(X∪O)ᶜ.filter (G.Adj w) := by
      intro i m; have jm := inJ w wo m
      exact mem_filter.mpr ⟨mem_compl.mpr (fun p => (mem_union.mp p).elim
        (fun ix => disjoint_left.mp xj ix jm) (fun io => disjoint_left.mp jo jm (oe io))),(G.mem_neighborFinset ..).mp m⟩
    have h := card_le_card inc
    rwa [card_neighborFinset_eq_degree,LowSample.two_degree G (oe wo)] at h
  have away (i : V) (ix : i∈X) (w : V) (wo : w∈O) (iw : G.Adj i w) : False :=
    disjoint_left.mp xj ix (inJ w wo ((G.mem_neighborFinset ..).mpr iw.symm))
  have sj : ({z,a,b}:Finset V)=J := by ext i; simp [J]; tauto
  have sep := TwoEars.outer_separation G ef az.symm bz.symm ab en fn' (sj ▸ (jo.mono_right oe).symm) bad
  have common {i : V} (ai : G.Adj a i) (bi : G.Adj b i) : i=z :=
    mem_singleton.mp (sep (mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr ai,(G.mem_neighborFinset ..).mpr bi⟩))
  let hits := X.filter (fun w => 0<nbr G w J)
  let m := hits.card
  have plus {k : V} (kj : k∈J) : X.filter (G.Adj k)⊆hits := by
    intro i im; exact mem_filter.mpr ⟨(mem_filter.mp im).1,card_pos.mpr ⟨k,mem_filter.mpr ⟨kj,(mem_filter.mp im).2.symm⟩⟩⟩
  have dis : Disjoint (X.filter (G.Adj a)) (X.filter (G.Adj b)) := disjoint_left.mpr (by
    intro i am bm
    have eq := common (mem_filter.mp am).2 (mem_filter.mp bm).2
    exact disjoint_left.mp xj (mem_filter.mp am).1 (eq ▸ (by simp [J])))
  have xy : nbr G a X+nbr G b X≤m := by
    have h := card_le_card (union_subset (plus (show a∈J by simp [J])) (plus (show b∈J by simp [J])))
    rwa [card_union_of_disjoint dis] at h
  have part {i : V} (h : i∈high G) : i∈X ∨ i=a ∨ i=b ∨ i=z := by
    by_cases ij : i∈J
    · exact Or.inr (by simpa [J] using ij)
    · exact Or.inl (mem_sdiff.mpr ⟨h,ij⟩)
  have anchor (p r w : V) (order : (p=a ∧ r=b ∧ w=f) ∨ (p=b ∧ r=a ∧ w=e)) :
      trianglesAt G p≤2+(nbr G p X+1).choose 2 := by
    have size : nbr G p (X∪{z})≤nbr G p X+1 := by
      unfold nbr; rw [filter_union]
      exact (card_union_le ..).trans (Nat.add_le_add_left ((card_le_card (filter_subset ..)).trans_eq (card_singleton z)) _)
    have off : ¬G.Adj p w := by
      intro pw; have pn := (G.mem_neighborFinset ..).mpr pw.symm
      rcases order with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
      · simp [fn',az,ab] at pn
      · simp [en,bz,ab.symm] at pn
    have wem : w∈E := order.elim (fun h => h.2.2 ▸ mE df) (fun h => h.2.2 ▸ mE de)
    have cardBound := card_le_card (show E.filter (G.Adj p)⊆E.erase w from fun i im =>
      mem_erase.mpr ⟨fun h => off (h ▸ (mem_filter.mp im).2),(mem_filter.mp im).1⟩)
    rw [card_erase_of_mem wem] at cardBound
    have small : nbr G p (LowSample.twos G)≤1 := by change nbr G p E≤1; change nbr G p E≤E.card-1 at cardBound; change E.card=2 at es; omega
    have cap := score_cap G p (X∪{z}) {r,z} _ size (by
      intro i j pi pj ij ih _
      rcases part ih with ix|ia|ib|iz
      · exact Or.inl (mem_union_left _ ix)
      · subst i; rcases order with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
        · exact False.elim (pi.ne rfl)
        · exact Or.inr (by rw [common ij pj])
      · subst i; rcases order with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
        · exact Or.inr (by rw [common pj ij])
        · exact False.elim (pi.ne rfl)
      · exact Or.inl (mem_union_right _ (mem_singleton.mpr iz)))
    omega
  have zcount : nbr G z X≤m := card_le_card (plus (show z∈J by simp [J]))
  have size : nbr G z (X∪{a,b})≤m+2 := by
    unfold nbr; rw [filter_union]
    exact (card_union_le ..).trans (Nat.add_le_add zcount ((card_le_card (filter_subset ..)).trans_eq (card_pair ab)))
  have hub := Shared.score_cap G z (X∪{a,b}) _ size (by
    intro i _ zi _ _ ih _
    rcases part ih with ix|rfl|rfl|iz
    · exact mem_union_left _ ix
    · exact mem_union_right _ (mem_insert_self ..)
    · exact mem_union_right _ (mem_insert_of_mem (mem_singleton_self _))
    · exact False.elim (zi.ne iz.symm))
  rw [es] at hub
  have hx : insert a (insert b (insert z X))⊆high G := insert_subset (pins (by simp [J])) (insert_subset
    (pins (by simp [J])) (insert_subset (pins (by simp [J])) sdiff_subset))
  have cap := exact_pool G X O ab az bz xs os xo safe away sdiff_subset xj
    (inj.mono (show ((insert a (insert b (insert z X)):Finset V):Set V)⊆high G from hx))
    (fun i im => floor i (hx im)) _ _ m xy rfl (anchor a b f (Or.inl ⟨rfl,rfl,rfl⟩))
    (anchor b a e (Or.inr ⟨rfl,rfl,rfl⟩)) hub
  rw [bound,t] at bad; omega

theorem disjoint_anchors (t : (types G).card=31) (q : (nonleaves G).card=31)
    (bad : bound G<gamma G) {e f : V} (ef : e≠f) (de : G.degree e=2) (df : G.degree f=2) :
    Disjoint (G.neighborFinset e) (G.neighborFinset f) := by
  classical
  apply disjoint_left.mpr; intro z ze zf
  obtain ⟨a,za,en⟩ := Squares29.pair_at ((card_neighborFinset_eq_degree ..).trans de) ze
  obtain ⟨b,zb,fn'⟩ := Squares29.pair_at ((card_neighborFinset_eq_degree ..).trans df) zf
  by_cases eq : a=b
  · exact (not_lt_of_ge (Repair.exact_of_twin_degree_two G ef de (en.trans (eq ▸ fn'.symm)))) bad
  exact (not_lt_of_ge (three_anchors G t q ef eq za.symm zb.symm en fn')) bad
end Graffiti384b.AnchorPairs
#print axioms Graffiti384b.AnchorPairs.three_anchors
#print axioms Graffiti384b.AnchorPairs.disjoint_anchors
