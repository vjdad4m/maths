import RetainBags180
import PrimeCubic180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

theorem induced_bip_le (H : SimpleGraph V) (S : Finset V) : bipartiteNum (side H S)≤bipartiteNum H := by
  classical
  obtain ⟨Z,c,opt⟩ := optB (side H S)
  obtain ⟨col,good⟩ := (color_function ..).mp c
  have proper : TwoColor H (push Z) := by
    apply (color_function ..).mpr
    let color (x : V) := if m : x∈S then col ⟨x,m⟩ else false
    refine ⟨color,fun x xm y ym edge => ?_⟩
    have xs := push_sub Z xm
    have ys := push_sub Z ym
    simpa [color,xs,ys] using good ⟨x,xs⟩ ((in_push _).mp xm) ⟨y,ys⟩ ((in_push _).mp ym) edge
  simpa only [card_push,opt] using size_bip H proper

omit [Fintype V] in
theorem pull_card_kept (S X : Finset V) : (pull (fun x : ↥S => x.val) X).card+(X\S).card=X.card := by
  rw [←card_push,push_pull]
  have := card_sdiff_add_card_inter X S
  omega

omit [Fintype V] in
theorem keep_sections (S A P : Finset V) (r : ↥S) (both : A∩P⊆S) :
    let C := pull (fun x : ↥S => x.val)
    (C A).card+(C P).card+(eligible A P r.val).card=A.card+P.card+(C (eligible A P r.val)).card := by
  classical
  intro C
  let U := eligible A P r.val
  have eq : U\S=(A\S)∪(P\S) := by
    ext x
    by_cases xs : x∈S
    · simp [xs]
    · have xr : x≠r.val := fun e => xs (e ▸ r.property)
      simp [U,eligible_iff,xr,xs]
  have dis : Disjoint (A\S) (P\S) := disjoint_left.mpr (fun x xa xp =>
    (mem_sdiff.mp xa).2 (both (mem_inter.mpr ⟨(mem_sdiff.mp xa).1,(mem_sdiff.mp xp).1⟩)))
  have ac := pull_card_kept S A
  have pc := pull_card_kept S P
  have uc := pull_card_kept S U
  rw [eq,card_union_of_disjoint dis] at uc
  change (pull _ A).card+(pull _ P).card+U.card=A.card+P.card+(pull _ U).card
  omega

/-- Keep at least one member of each bag, the root, and every vertex
in both markings. Failure descends with the very same root, parity,
and restricted independent marking. -/
theorem Bags.prune (H : SimpleGraph V) (G : SimpleGraph B) (f : V→B) (h : Bags H G f)
    (gc : G.Connected) (ord : 1<Fintype.card B) (S : Finset V) (keep : ∀ i,∃ x∈S,f x=i)
    (r : ↥S) (p : Bool) (A : Finset V) (ai : Indep H A) (both : A∩parity H r.val p⊆S)
    (bad : weightedLeaves H (eligible A (parity H r.val p) r.val)+bipartiteNum H<1+A.card+(parity H r.val p).card) :
    let J := side H S
    let B' := pull (fun x : ↥S => x.val) A
    let Q := parity J r p
    Indep J B' ∧ weightedLeaves J (eligible B' Q r)+bipartiteNum J<1+B'.card+Q.card := by
  classical
  intro J B' Q
  let P := parity H r.val p
  let U := eligible A P r.val
  let C := pull (fun x : ↥S => x.val)
  have nh (i : B) : ¬Universal G i := by
    intro u
    obtain ⟨_,edge⟩ := h.hubEdge gc ord u r.val
    have upper := Fintype.card_le_of_surjective f h.onto
    have ok := dom_edge_rooted H (h.connected gc ord) (by omega) edge p A ai
    omega
  have pp : Q=C P := by
    ext x
    simp only [Q,C,P,mem_pull,mem_parity,h.retainedDist gc ord S keep x r,J]
  have ue : eligible B' Q r=C U := by
    rw [pp]
    ext x
    simp only [B',C,U,mem_pull,eligible_iff]
    simp [Subtype.ext_iff]
  have score := h.retainedLoss gc (three_of_nohub G gc ord nh) nh S keep U
  have sz := keep_sections S A P r both
  have b := induced_bip_le H S
  change (C A).card+(C P).card+U.card=A.card+P.card+(C U).card at sz
  change weightedLeaves J (C U)+U.card≤weightedLeaves H U+(C U).card at score
  change weightedLeaves H U+bipartiteNum H<1+A.card+P.card at bad
  refine ⟨fun x xm y ym ne e => ai _ (mem_pull.mp xm) _ (mem_pull.mp ym) (fun eq => ne (Subtype.ext eq)) e,?_⟩
  rw [ue,pp]
  change weightedLeaves (side H S) (C U)+bipartiteNum (side H S)<1+(C A).card+(C P).card
  change weightedLeaves (side H S) (C U)+U.card≤_ at score
  omega

#print axioms keep_sections
#print axioms Bags.prune
end Minimal180.Substitution
