import CorePalette28
import ShoreFinish28

namespace Graffiti384b.Core28
open Finset SimpleGraph
open private OneEar.trim OneEar.trim_scores from OneEarFinish384b
open private PositiveCore33.gamma_mono from LeafReduction33
open private OddQuota.positive_half from OddQuota384b
open private Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- For positive scores this spanning graph consists precisely of edges belonging to triangles. -/
abbrev triangleEdges := OneEar.trim G

theorem connected_edges (n : Fintype.card V=28) (pos : ∀ v,0<trianglesAt G v)
    (fi : Function.Injective (trianglesAt G)) (hf : Fintype.card V≤2*gamma G) :
    (triangleEdges G).Connected := by
  classical
  let J := triangleEdges G
  have non : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  letI := non
  constructor
  intro u w
  let S := univ.filter (fun v => J.Reachable u v)
  have home : u∈S := mem_filter.mpr ⟨mem_univ _,SimpleGraph.Reachable.refl _⟩
  have closed : OddQuota.TriangleClosed G S := by
    intro v vm x z vx vz xz
    have edge : J.Adj v x := ⟨vx,Or.inl ⟨z,vz,xz⟩⟩
    exact mem_filter.mpr ⟨mem_univ _,((mem_filter.mp vm).2).trans edge.reachable⟩
  have full := (no_proper_shore G n pos fi hf S closed).resolve_left (nonempty_iff_ne_empty.mp ⟨u,home⟩)
  exact (mem_filter.mp (show w∈S from full ▸ mem_univ w)).2

theorem profile (n : Fintype.card V=28) (pos : ∀ v,0<trianglesAt G v)
    (fi : Function.Injective (trianglesAt G)) (hf : Fintype.card V≤2*gamma G) :
    let J := triangleEdges G
    J.Connected ∧ gamma J=14 ∧ (∃ C,J.IsNClique 4 C) ∧
    (∃ e a b,trianglesAt G e=1 ∧ J.Adj a b ∧ J.neighborFinset e={a,b} ∧
      ∀ v,J.degree v=2 ↔ v=e) ∧
    (J.CliqueFree 5 → 5≤(lowPalette J).card) := by
  classical
  let J := triangleEdges G
  have sc (v : V) : trianglesAt J v=trianglesAt G v := OneEar.trim_scores G v
  have jp (v : V) : 0<trianglesAt J v := (sc v) ▸ pos v
  have ji : Function.Injective (trianglesAt J) := fun v w eq => fi ((sc v).symm.trans (eq.trans (sc w)))
  have half : Fintype.card V≤2*gamma J := hf.trans (Nat.mul_le_mul_left 2 (PositiveCore33.gamma_mono G J (fun _ _ e => e.1)))
  have high := OddQuota.positive_half J jp ji
  have c4 : ∃ C,J.IsNClique 4 C := by
    by_contra! no
    have f : J.CliqueFree (2+2) := no
    have e := (density_profile J jp ji n half (r:=2) (by decide) f).1
    contradiction
  have one : 1∈types J := by
    by_cases cf : J.CliqueFree 5
    · exact (mem_inter.mp (density_profile J jp ji n half (r:=3) (by decide) cf).2.1).1
    · unfold SimpleGraph.CliqueFree at cf
      push_neg at cf
      obtain ⟨C,cl⟩ := cf
      exact clique_scores J jp ji half cl (by decide)
  obtain ⟨e,_,se⟩ := mem_image.mp one
  have norm : TrianglePrune.Normal J := by
    refine ⟨fun v _ h _ => ((jp v).ne' h).elim,fun v h => ((jp v).ne' h).elim,?_⟩
    intro u v edge _ _
    obtain ⟨uv,z⟩ := edge
    rcases z with ⟨w,uw,vw⟩|z|z
    · exact ⟨w,⟨uw,Or.inl ⟨v,uv,vw.symm⟩⟩,⟨vw,Or.inl ⟨u,uv.symm,uw.symm⟩⟩⟩
    · exact ((pos u).ne' z).elim
    · exact ((pos v).ne' z).elim
  obtain ⟨a,b,ab,nb⟩ := Minimal.score_one_ear J norm e se (fun w _ => jp w)
  have de : J.degree e=2 := by rw [←card_neighborFinset_eq_degree,nb,card_pair ab.ne]
  refine ⟨connected_edges G n pos fi hf,by change gamma J=14; omega,c4,⟨e,a,b,(sc e).symm.trans se,ab,nb,?_⟩,?_⟩
  · intro v
    constructor
    · intro dv
      have cap := Repair.triangles_le_choose J v
      rw [dv,Nat.choose_self] at cap
      exact ji (by have := jp v; omega)
    · rintro rfl; exact de
  · intro cf; exact (density_profile J jp ji n half (r:=3) (by decide) cf).2.2

/-- When the connected triangle-edge graph contains a five-clique, the same
two cubic vertices cover at least three vertices of every five-clique. -/
theorem clique_contacts (n : Fintype.card V=28) (pos : ∀ v,0<trianglesAt G v)
    (fi : Function.Injective (trianglesAt G)) (hf : Fintype.card V≤2*gamma G)
    (five : ∃ C,(triangleEdges G).IsNClique 5 C) :
    let J := triangleEdges G
    ∃ u s,J.degree u=3 ∧ trianglesAt J u=2 ∧ J.degree s=3 ∧ trianglesAt J s=3 ∧
      ∀ C,J.IsNClique 5 C → 3≤(C∩(J.neighborFinset u∪J.neighborFinset s)).card ∧
        ∃ x∈C,J.Adj s x := by
  classical
  let J := triangleEdges G
  obtain ⟨_,eq,_,⟨e,a,b,_,ab,nb,unique⟩,_⟩ := profile G n pos fi hf
  have jp (v : V) : 0<trianglesAt J v := (OneEar.trim_scores G v) ▸ pos v
  have ji : Function.Injective (trianglesAt J) := fun v w vs => fi
    ((OneEar.trim_scores G v).symm.trans (vs.trans (OneEar.trim_scores G w)))
  have half : Fintype.card V≤2*gamma J := by change gamma J=14 at eq; omega
  have tight : CliquePivot33.Tight J ∅ := by
    intro D rel
    have dd : TwoDominates J D := fun v out => by simpa using rel v out
    have up : gamma J≤D.card := Nat.sInf_le ⟨D,dd,rfl⟩
    omega
  have ea : J.Adj e a := (J.mem_neighborFinset ..).mp (nb ▸ mem_insert_self _ _)
  have eb : J.Adj e b := (J.mem_neighborFinset ..).mp (nb ▸ mem_insert_of_mem (mem_singleton_self _))
  have de := (unique e).mpr rfl
  obtain ⟨C,cl⟩ := five
  obtain ⟨u,s,du,su,_,ds,ss,_⟩ := ThirtyCore.both_required J de ea eb ab jp ji cl half tight
  refine ⟨u,s,du,su,ds,ss,?_⟩
  intro K kc
  have lim := ForcedCubics.clique_remainder J du su ds ss jp ji tight kc
  have total := (card_sdiff_add_card_inter K (J.neighborFinset u∪J.neighborFinset s)).trans kc.2
  obtain ⟨z,_,_,sz,hits⟩ := ThirtyCore.cubic_hits J de ea eb ab jp ji tight kc
  exact ⟨by change 3≤(K∩(J.neighborFinset u∪J.neighborFinset s)).card; omega,ji (sz.trans ss.symm) ▸ hits⟩

/-- Original-graph statement. No connectivity premise is needed for the 28-nonleaf reduction. -/
theorem original (t : (types G).card=29) (q : (nonleaves G).card=28) (bad : bound G<gamma G) :
    let P := nonleaves G
    let H := G.induce (P:Set V)
    let J := triangleEdges H
    J.Connected ∧ gamma J=14 ∧ (∃ C,J.IsNClique 4 C) ∧
    (∃ e a b,trianglesAt H e=1 ∧ J.Adj a b ∧ J.neighborFinset e={a,b} ∧
      ∀ v,J.degree v=2 ↔ v=e) ∧
    (J.CliqueFree 5 → 5≤(lowPalette J).card) := by
  let P := nonleaves G
  let H := G.induce (P:Set V)
  have nc : Fintype.card P=28 := (Fintype.card_coe _).trans q
  obtain ⟨pos,fi,eq,_⟩ := Quota29.minimum G t q bad
  exact profile H nc pos fi (by change Fintype.card P≤2*gamma H; change gamma H=14 at eq; omega)

/-- Two nonempty parts of the nonleaf core with no crossing triangle supply
the fifteenth omission in the original graph. -/
theorem exact_of_split (t : (types G).card=29) (q : (nonleaves G).card=28)
    (S : Finset (nonleaves G)) (cl : OddQuota.TriangleClosed (G.induce (nonleaves G:Set V)) S)
    (occupied : S.Nonempty) (outside : Sᶜ.Nonempty) : gamma G≤bound G := by
  by_contra! bad
  let P := nonleaves G
  let H := G.induce (P:Set V)
  obtain ⟨pos,fi,eq,_⟩ := Quota29.minimum G t q bad
  have nc : Fintype.card P=28 := (Fintype.card_coe _).trans q
  have tight : Fintype.card P≤2*gamma H := by change gamma H=14 at eq; omega
  rcases no_proper_shore H nc pos fi tight S cl with empty|full
  · exact occupied.ne_empty empty
  · exact outside.ne_empty (by rw [full,compl_univ])

end Graffiti384b.Core28
#print axioms Graffiti384b.Core28.connected_edges
#print axioms Graffiti384b.Core28.profile
#print axioms Graffiti384b.Core28.original
#print axioms Graffiti384b.Core28.exact_of_split

#print axioms Graffiti384b.Core28.clique_contacts

