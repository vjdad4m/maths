import CoverDense31
import CreditFinish31

namespace Graffiti384b.ThirtyCore
open Finset SimpleGraph
open private EarAnchor.sees_in_clique from CubicAnchor33
open private CliquePivot33.full_cubic from CliquePivot33
open private TrianglePrune.triangle_iff from TrianglePrune384b
open private HighEar.nonEar from HighEarBypass33
open private Repair.full_nbr from Repair384b
open private Prune.outside_zero from Prune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A single uncredited cubic of score three hits any given five-clique by
its neighborhood. Injectivity then gives the same cubic for every clique. -/
theorem cubic_hits {e a b : V} (de : G.degree e=2) (ea : G.Adj e a)
    (eb : G.Adj e b) (ab : G.Adj a b) (pos : ∀ v,0<trianglesAt G v)
    (inj : Function.Injective (trianglesAt G)) {R C : Finset V}
    (tight : CliquePivot33.Tight G R) (cl : G.IsNClique 5 C) :
    ∃ s,s∉R ∧ G.degree s=3 ∧ trianglesAt G s=3 ∧ ∃ x∈C,G.Adj s x := by
  classical
  by_contra! missing
  let M := C.filter (RootCut.Safe G R)
  have safe := ForcedCubics.safe_cap G de ea eb ab pos inj tight cl (show M⊆C from filter_subset ..)
    (fun _ m => (mem_filter.mp m).2)
  have lower : 3≤(C\M).card := by
    rw [card_sdiff (show M⊆C from filter_subset ..),cl.2]; omega
  have blocked {x : V} (xm : x∈C\M) : ∃ u,G.degree u=3 ∧ trianglesAt G u=2 ∧ G.Adj u x := by
    obtain ⟨xc,off⟩ := mem_sdiff.mp xm
    have no : ¬RootCut.Safe G R x := fun h => off (mem_filter.mpr ⟨xc,h⟩)
    unfold RootCut.Safe at no
    push_neg at no
    obtain ⟨u,du,ur,ux⟩ := no
    refine ⟨u,du,(HighEar.cubic_scores G de du pos inj).resolve_right ?_,ux⟩
    exact fun s => missing u ur du s x xc ux
  obtain ⟨x,xm⟩ := card_pos.mp (show 0<(C\M).card by omega)
  obtain ⟨u,du,score,_⟩ := blocked xm
  have sub : C\M⊆C.filter (G.Adj u) := by
    intro v vm
    obtain ⟨w,_,sw,wv⟩ := blocked vm
    exact mem_filter.mpr ⟨(mem_sdiff.mp vm).1,inj (sw.trans score.symm) ▸ wv⟩
  have many : 3≤nbr G u C := lower.trans (card_le_card sub)
  have other := (CliquePivot33.full_cubic G cl du many).2
  omega

/-- A transfer of the cardinality-independent ear and clique obstruction
to the thirty-vertex core, with simultaneous leaf credits. -/
theorem failure (conn : G.Connected) (t : (types G).card=31) (q : (nonleaves G).card=30)
    (bad : bound G<gamma G) :
    let P := nonleaves G
    let H := G.induce (P:Set V)
    let R := univ.filter (fun w : P => ∃ z,z∉P ∧ G.Adj w.val z)
    (∃ C,H.IsNClique 5 C) ∧ (∃ e,H.degree e=2) ∧ (∀ w∈R,4≤H.degree w) ∧
    ∃ s : P,s∉R ∧ H.degree s=3 ∧ trianglesAt H s=3 ∧
      ∀ C,H.IsNClique 5 C → ∃ x∈C,H.Adj s x := by
  classical
  let P := nonleaves G
  let H := G.induce (P:Set V)
  let R := univ.filter (fun w : P => ∃ z,z∉P ∧ G.Adj w.val z)
  change (∃ C,H.IsNClique 5 C) ∧ (∃ e,H.degree e=2) ∧ (∀ w∈R,4≤H.degree w) ∧ _
  obtain ⟨_,_,floor,_,one⟩ := Cover31.failure_profile G conn t bad
  obtain ⟨y,_,ys⟩ := mem_image.mp one
  have ym : y∈P := by
    by_contra outside
    have zero := Prune.outside_zero G outside
    omega
  have dy : G.degree y=2 := by
    have dl := (mem_filter.mp ym).2
    by_contra! ne
    have h := floor y (mem_filter.mpr ⟨mem_univ y,by omega⟩)
    omega
  let e : P := ⟨y,ym⟩
  obtain ⟨size,_,sc,fi,pos,g⟩ := Frontier31.positive_core G conn t q bad
  obtain ⟨a,b,ea,eb,ab⟩ := (TrianglePrune.triangle_iff H e).mp (pos e)
  have partition := Repair.full_nbr G y P
  have dh := EarAnchor.induced_degree G (W:=P) e
  change H.degree e=nbr G y P at dh
  have dl : 2≤H.degree e := by
    exact (show 1<(H.neighborFinset e).card from one_lt_card.mpr
      ⟨a,(H.mem_neighborFinset ..).mpr ea,b,(H.mem_neighborFinset ..).mpr eb,ab.ne⟩)
  have de : H.degree e=2 := by omega
  have er : e∉R := by
    intro m
    obtain ⟨z,off,yz⟩ := (mem_filter.mp m).2
    have h : 0<nbr G y Pᶜ := card_pos.mpr ⟨z,mem_filter.mpr ⟨mem_compl.mpr off,yz⟩⟩
    omega
  have five : ∃ C,H.IsNClique 5 C := by
    have big : ¬G.CliqueFree 5 := fun f => (not_lt_of_ge (EarCredit.exact_five_free G conn t f)) bad
    simp only [CliqueFree,not_forall,Classical.not_not] at big
    obtain ⟨C,cl⟩ := big
    have inP (v : V) (vm : v∈C) : v∈P := by
      have d := EarAnchor.sees_in_clique G cl vm
      exact mem_filter.mpr ⟨mem_univ _,by omega⟩
    let K := C.subtype (fun v => v∈P)
    have eq : K.map (Function.Embedding.subtype _)=C := subtype_map_of_mem inP
    exact ⟨K,fun i im j jm ne => cl.1 (mem_subtype.mp im) (mem_subtype.mp jm)
      (fun eq => ne (Subtype.ext eq)),(card_map ..).symm.trans ((congrArg card eq).trans cl.2)⟩
  have tight : CliquePivot33.Tight H R := Frontier31.rooted_tight G t q bad
  obtain ⟨C,cl⟩ := five
  have half : Fintype.card P≤2*gamma H := by rw [size,show gamma H=15 from g]
  have large (w : P) (wm : w∈R) : 4≤H.degree w := by
    have lo := HighEar.nonEar H de (show w≠e from fun eq => er (eq ▸ wm)) pos fi
    change 3≤H.degree w at lo
    change 4≤H.degree w
    by_contra! low
    have oneT : CliquePivot33.Tight H {w} := by
      intro D cover
      apply tight D
      intro v off
      have z := cover v off
      by_cases vw : v=w
      · subst v; simpa [wm] using z
      · simp [vw] at z; exact Nat.le_add_right_of_le z
    exact RootCut.cubic_root H (by omega : H.degree w=3) de ea eb ab pos fi half cl oneT
  obtain ⟨s,sr,ds,ss,_⟩ := cubic_hits H de ea eb ab pos fi tight cl
  refine ⟨⟨C,cl⟩,⟨e,de⟩,large,s,sr,ds,ss,?_⟩
  intro K kc
  obtain ⟨u,_,_,us,x,xm,ux⟩ := cubic_hits H de ea eb ab pos fi tight kc
  exact ⟨x,xm,fi (us.trans ss.symm) ▸ ux⟩

end Graffiti384b.ThirtyCore
#print axioms Graffiti384b.ThirtyCore.cubic_hits
#print axioms Graffiti384b.ThirtyCore.failure
