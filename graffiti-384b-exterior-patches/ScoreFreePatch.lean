import UnconditionalPorts
import SharpPortRank
namespace Graffiti384b.Exterior
open Finset SimpleGraph Four29 LowSample FiveChoice
open private Exterior.profile_data Exterior.outside_in_pool from UnconditionalPorts
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem cut_in_profile {e f : V} (D : Data G e f) (P Q : Finset V) {a x y : V} (xy : x≠y)
    (xp : x∈pool G e f) (yp : y∈pool G e f) (ar : a∈roots G e f)
    (H : Ports G P Q {x,y} (pool G e f\{x,y}) a)
    (rootOnly : ∀p∈({x,y}:Finset V),∀r∈roots G e f,G.Adj p r → r=a)
    (privatePort : ∀p∈({x,y}:Finset V),∀r∈triangleContacts G e f,G.Adj p r → r∈({x,y}:Finset V)) :
    ∃L R : Finset V,P⊆L ∧ Q⊆R ∧ Protected G L R ∧ ((L∪R)\(roots G e f∪{e,f}∪{x,y})).card≤3 := by
  let S : Finset V := {x,y}
  let W := pool G e f\S
  let U := boundary G S W
  have sp : S⊆pool G e f := insert_subset xp (singleton_subset_iff.mpr yp)
  have up : U⊆pool G e f := (filter_subset ..).trans (sdiff_subset (t:=S))
  have all : S∪W=pool G e f := union_sdiff_of_subset sp
  have highAll : S∪U⊆high G := (union_subset sp up).trans sdiff_subset
  have card : W.card=21 := by change (pool G e f\S).card=21; rw [card_sdiff sp,D.poolSize,show S.card=2 from card_pair xy]
  obtain ⟨loss,off⟩ := local_conditions G D xp yp ar rootOnly privatePort
  have localLoss : ∀p∈S,trianglesAt G p≤(kept (link G p) (S∪W)).card+1 := by rw [all]; exact loss
  have support : ∀u∈U,Repair.linkSupport G u⊆S∪W := by
    rw [all]; exact fun u m => noncontact_support G D (up m) (fun hc => disjoint_left.mp off m hc)
  have ports : Ports G P Q S W a := H
  obtain ⟨L,R,pl,qr,good,n⟩ := score_free_cut G ports rfl xy card.le localLoss
    (fun u m => D.rich u (highAll m)) (D.scoreInj.mono highAll) support
  exact ⟨L,R,pl,qr,good,(card_le_card (Exterior.outside_in_pool G D L R S good)).trans n⟩

/-- The four specified distinct high roots guarantee a protected cut with at
most three further pins, with unrestricted scores at all anchors. -/
theorem three_pin_private_cut (t : (types G).card=29) (q : (nonleaves G).card=29) (h : (high G).card=27)
    {e f : V} (de : G.degree e=2) (df : G.degree f=2) (ef : e≠f)
    (rh : roots G e f⊆high G) (rs : (roots G e f).card=4)
    (P Q : Finset V) {a x y : V} (xy : x≠y) (xp : x∈pool G e f) (yp : y∈pool G e f)
    (ar : a∈roots G e f) (H : Ports G P Q {x,y} (pool G e f\{x,y}) a)
    (rootOnly : ∀p∈({x,y}:Finset V),∀r∈roots G e f,G.Adj p r → r=a)
    (privatePort : ∀p∈({x,y}:Finset V),∀r∈triangleContacts G e f,G.Adj p r → r∈({x,y}:Finset V)) :
    ∃L R : Finset V,P⊆L ∧ Q⊆R ∧ Protected G L R ∧ ((L∪R)\(roots G e f∪{e,f}∪{x,y})).card≤3 :=
  cut_in_profile G (Exterior.profile_data G t q h de df ef rh rs) P Q xy xp yp ar H rootOnly privatePort

theorem score_free_solution (t : (types G).card=29) (q : (nonleaves G).card=29) (h : (high G).card=27)
    {e f : V} (de : G.degree e=2) (df : G.degree f=2) (ef : e≠f)
    (P Q : Finset V) {a x y : V} (xy : x≠y) (xp : x∈pool G e f) (yp : y∈pool G e f)
    (ar : a∈roots G e f) (H : Ports G P Q {x,y} (pool G e f\{x,y}) a) (ep : e∈P∪Q) (fp : f∈P∪Q)
    (rootOnly : ∀p∈({x,y}:Finset V),∀r∈roots G e f,G.Adj p r → r=a)
    (privatePort : ∀p∈({x,y}:Finset V),∀r∈triangleContacts G e f,G.Adj p r → r∈({x,y}:Finset V)) :
    gamma G≤bound G := by
  apply Nat.le_of_not_gt
  intro bad
  have D := data_of_failure G t h q bad de df ef
  obtain ⟨L,R,pl,qr,good,_⟩ := cut_in_profile G D P Q xy xp yp ar H rootOnly privatePort
  have deg (v : V) (vn : v∈nonleaves G) (vl : v∉L) (vr : v∉R) : 3≤G.degree v := by
    by_contra! small
    have tv : v∈twos G := mem_sdiff.mpr ⟨vn,fun hi => (not_le_of_gt small) (mem_filter.mp hi).2⟩
    rw [D.earSet] at tv
    have cover : v∈P∪Q := (mem_insert.mp tv).elim (fun eq => eq ▸ ep) (fun eq => mem_singleton.mp eq ▸ fp)
    exact (mem_union.mp cover).elim (fun z => vl (pl z)) (fun z => vr (qr z))
  exact (not_lt_of_ge (PinnedColor34.complete G good.1 (by omega) deg good.2.1 good.2.2)) bad
end Graffiti384b.Exterior
#print axioms Graffiti384b.Exterior.three_pin_private_cut
#print axioms Graffiti384b.Exterior.score_free_solution
