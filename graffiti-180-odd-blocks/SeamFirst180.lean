import WingCertificate180
import OddWing180

set_option warningAsError true
namespace Minimal180.OddBlock
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem flip_first {J : SimpleGraph V} {U : Finset V} {x y w : V}
    (h : FirstForm J U x y w) : FirstForm J U y x w := by
  obtain ⟨C,cu,wc,ct,⟨xd,yd,nc,on⟩,dom⟩ := h
  exact ⟨C,cu,wc,ct,⟨yd,xd,nc,fun f hf eq => on f hf eq.symm⟩,dom⟩

private theorem pendant_of_edge {J : SimpleGraph V} {S T : Finset V} {x w : V}
    (s : Split J w S T) (xt : x∉T) (wing : S={x,w}) : ∀ j, J.Adj x j → j=w := by
  intro j e
  rcases s.edges e with k|k
  · have h : j∈({x,w}:Finset V) := wing ▸ k.2
    exact mem_singleton.mp ((mem_insert.mp h).resolve_left e.ne.symm)
  · exact (xt k.1).elim

/-- On a split lower graph, first form is precisely unrestricted gain with
both eligible pendant-tip obstructions absent. -/
theorem seam_first_iff {J : SimpleGraph V} (jc : J.Connected) (hn : 2<Fintype.card V)
    {x y w : V} {S T : Finset V} (s : Split J w S T)
    (xs : x∈S) (xt : x∉T) (yt : y∈T) (ys : y∉S) (xy : x≠y) (old : ¬J.Adj x y)
    (xw : J.Adj x w) (wy : J.Adj w y) (U : Finset V) :
    FirstForm J U x y w ↔ weightedLeaves J U<weightedLeaves (J⊔edge x y) U ∧
      ¬(x∈U ∧ S={x,w}) ∧ ¬(y∈U ∧ T={y,w}) := by
  have test := triangle_gain_iff_core J jc hn x y w xy old xw wy U
  constructor
  · intro h
    obtain ⟨C,cu,wc,ct,win⟩ := h
    have first : FirstForm J U x y w := ⟨C,cu,wc,ct,win⟩
    exact ⟨test.mpr ⟨C,cu,wc,ct,Or.inl win⟩,
      fun ⟨xu,ed⟩ => pendant_excludes_first jc hn xy xw wy (pendant_of_edge s xt ed) U xu first,
      fun ⟨yu,ed⟩ => pendant_excludes_first jc hn xy.symm wy.symm xw.symm
        (pendant_of_edge s.flip ys ed) U yu (flip_first first)⟩
  · rintro ⟨gain,l,r⟩
    obtain ⟨C,cu,wc,ct,h⟩ := test.mp gain
    rcases h with win|tip|tip
    · exact ⟨C,cu,wc,ct,win⟩
    · exact (l ⟨cu tip.1,second_wing_edge s xs ys xw tip⟩).elim
    · exact (r ⟨cu tip.1,second_wing_edge s.flip yt xt wy.symm tip⟩).elim

/-- A second-form certificate with a nonpendant tip already puts the
whole lower graph in the biconnected branch. -/
theorem second_nonpendant_block {J : SimpleGraph V} {x y w z : V} {C : Finset V}
    (block : NoCut (J⊔edge x y)) (xw : J.Adj x w) (wy : J.Adj w y) (xz : J.Adj x z)
    (zw : z≠w) (tip : NeedsTip J C (univ\C) x y) : NoCut J := by
  by_contra no
  obtain ⟨c,S,T,s⟩ := split_of_cut no
  obtain ⟨eq,h⟩ := chord_seam s block xw wy
  subst c
  rcases h with ⟨xs,xt,_,ys⟩|⟨xt,xs,_,yt⟩
  · exact zw (pendant_of_edge s xt (second_wing_edge s xs ys xw tip) z xz)
  · exact zw (pendant_of_edge s.flip xs (second_wing_edge s.flip xt yt xw tip) z xz)

#print axioms seam_first_iff
#print axioms second_nonpendant_block
end Minimal180.OddBlock
