import DefectOneGain180

set_option warningAsError true
namespace Minimal180.CutGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A tight tree edge count on a nonempty marked set missing the seam
forces all marked vertices to lie on a single side. -/
theorem forest_one_side {J M : SimpleGraph V} {w : V} {S T D : Finset V}
    (cut : Split J w S T) (sub : M≤J) (tr : M.IsTree) (wm : w∉D)
    (eq : (M.edgeFinset∩D.sym2).card+1=D.card) : D⊆S ∨ D⊆T := by
  classical
  by_contra! neither
  obtain ⟨l,ld,lt⟩ := Finset.not_subset.mp neither.2
  obtain ⟨r,rd,rs⟩ := Finset.not_subset.mp neither.1
  have gl := forest_strict M tr (D∩S) ⟨l,mem_inter.mpr ⟨ld,(cut.either l).resolve_right lt⟩⟩
  have gr := forest_strict M tr (D∩T) ⟨r,mem_inter.mpr ⟨rd,(cut.either r).resolve_left rs⟩⟩
  have cover : M.edgeFinset∩D.sym2 ⊆ (M.edgeFinset∩(D∩S).sym2)∪(M.edgeFinset∩(D∩T).sym2) := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      obtain ⟨adj,ab⟩ := mem_inter.mp he
      obtain ⟨ad,bd⟩ := mk_mem_sym2_iff.mp ab
      rcases cut.edges (sub (mem_edgeFinset.mp adj)) with k|k
      · exact mem_union_left _ (mem_inter.mpr ⟨adj,mk_mem_sym2_iff.mpr ⟨mem_inter.mpr ⟨ad,k.1⟩,mem_inter.mpr ⟨bd,k.2⟩⟩⟩)
      · exact mem_union_right _ (mem_inter.mpr ⟨adj,mk_mem_sym2_iff.mpr ⟨mem_inter.mpr ⟨ad,k.1⟩,mem_inter.mpr ⟨bd,k.2⟩⟩⟩)
  have e := (card_le_card cover).trans (card_union_le ..)
  have dis : Disjoint (D∩S) (D∩T) := by
    apply disjoint_left.mpr
    intro i il ir
    exact wm (cut.common (mem_inter.mp il).2 (mem_inter.mp ir).2 ▸ (mem_inter.mp il).1)
  have un : (D∩S)∪(D∩T)=D := by rw [←inter_union_distrib_left,cut.cover,inter_univ]
  have c := card_union_of_disjoint dis
  rw [un] at c
  omega

namespace TightCut
variable {J : SimpleGraph V} {S T : Finset V} {x y w : V} {r : ↥S} {odd : Bool} {A : Finset V}
variable (h : TightCut J S T x y w r odd A)
include h

/-- In a no-gain lower-deficit-one transition, exactly one tip is doubly
marked. The two marks agree everywhere on that tip's wing. -/
theorem defect_one_support (rank1 : bipartiteNum J+1=Fintype.card V) :
    let G := J⊔edge x y
    let P := parity G r.val odd
    let U := eligible A P r.val
    let D := (A∪P)\(A∩P)
    ¬weightedLeaves J U<weightedLeaves G U →
      w∉A∪P ∧ x∈P ∧ y∈P ∧ ¬A⊆P ∧
      ((x∈A ∧ y∉A ∧ D⊆T) ∨ (y∈A ∧ x∉A ∧ D⊆S)) := by
  classical
  dsimp only
  let G := J⊔edge x y
  let P := parity G r.val odd
  let D := (A∪P)\(A∩P)
  intro ng
  have lack : ¬A⊆P := fun s => ng (h.confined_gain s)
  obtain ⟨wm,M,mj,tree,_,_,edges⟩ := h.defect_one_forest rank1 (fun e => lack e.le)
  have nw : w∉D := fun d => wm (mem_sdiff.mp d).1
  have sideD := forest_one_side h.split mj tree nw edges
  obtain ⟨ds,l,rp⟩ := seam_layers h.connected h.split h.farTip h.rightSpoke h.absent r h.horizontal
  have wp : w∉P := fun p => wm (mem_union_right _ p)
  have tip {a : V} (eq : J.dist a r.val=J.dist w r.val+1) : a∈P := by
    apply (mem_parity ..).mpr
    have k : ¬G.dist w r.val%2=odd.toNat := fun v => wp ((mem_parity ..).mpr v)
    change G.dist a r.val%2=odd.toNat
    rw [ds,eq]
    rw [ds] at k
    cases odd <;> simp_all only [Bool.toNat_true,Bool.toNat_false] <;> omega
  have xp := tip l
  have yp := tip rp
  have inside {a : V} (p : a∈P) (out : a∉D) : a∈A := by
    by_contra z
    exact out (mem_sdiff.mpr ⟨mem_union_right _ p,fun c => z (mem_inter.mp c).1⟩)
  have adj : G.Adj x y := Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,h.distinct⟩)
  refine ⟨wm,xp,yp,lack,?_⟩
  rcases sideD with s|t
  · have ya := inside yp (fun a => h.outsideNear (s a))
    exact Or.inr ⟨ya,fun a => h.independent _ a _ ya h.distinct adj,s⟩
  · have xa := inside xp (fun a => h.outsideFar (t a))
    exact Or.inl ⟨xa,fun a => h.independent _ xa _ a h.distinct adj,t⟩

/-- Any pendant tip in a failed deficit-one cut is the doubly marked tip.
The support of the disagreement is in its nonpendant opposite wing. -/
theorem pendant_mark (rank1 : bipartiteNum J+1=Fintype.card V) :
    let G := J⊔edge x y
    let P := parity G r.val odd
    let U := eligible A P r.val
    ¬weightedLeaves J U<weightedLeaves G U →
      (S={x,w} → x∈A ∧ y∉A) ∧ (T={y,w} → y∈A ∧ x∉A) := by
  classical
  intro G P U bad
  obtain ⟨nw,xp,yp,miss,d⟩ := h.defect_one_support rank1 bad
  obtain ⟨a,aa,ap⟩ := Finset.not_subset.mp miss
  have ad : a∈(A∪P)\(A∩P) := mem_sdiff.mpr ⟨mem_union_left _ aa,fun e => ap (mem_inter.mp e).2⟩
  have aw : a≠w := fun eq => nw (mem_union_left _ (eq ▸ aa))
  have exclude {Q : Finset V} {t : V} (eq : Q={t,w}) (tp : t∈P) (aq : a∈Q) : False := by
    rw [eq] at aq
    rcases mem_insert.mp aq with atip|same
    · exact ap (atip ▸ tp)
    · exact aw (mem_singleton.mp same)
  constructor
  · intro left
    rcases d with q|q
    · exact ⟨q.1,q.2.1⟩
    · exact (exclude left xp (q.2.2 ad)).elim
  · intro right
    rcases d with q|q
    · exact (exclude right yp (q.2.2 ad)).elim
    · exact ⟨q.1,q.2.1⟩

#print axioms pendant_mark
#print axioms forest_one_side
#print axioms defect_one_support
end TightCut
end Minimal180.CutGain
