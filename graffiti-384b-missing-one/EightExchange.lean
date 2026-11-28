import UpperThirteen
namespace Graffiti384b.OddStars.EightExchange
open Finset SimpleGraph ShorePairs
open private Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In the eight-high configuration, retain the score-two cubic and the
other cubic's two opposite neighbors. -/
theorem three (A B : Finset V) (a4 : A.card=4) (b4 : B.card=4) (dis : Disjoint A B)
    {u v : V} (ua : u∈A) (va : v∈A) (apart : ¬G.Adj u v)
    (su : trianglesAt G u=2) (thin : nbr G u A=1)
    (crossU : nbr G u B=2) (crossV : nbr G v B=2)
    (cover : ∀w,G.neighborFinset w⊆A∪B)
    (hit : ∀b∈B,G.Adj u b ∨ G.Adj v b) (big : ∀b∈B,3≤nbr G b A)
    (degree : ∀b∈B,4≤G.degree b) :
    ∃D : Finset V,D⊆A∪B ∧ D.card=3 ∧ ∀w∈(A∪B)\D,2≤nbr G w D := by
  classical
  let P := B.filter (G.Adj u)
  let Q := B.filter (G.Adj v)
  have p2 : P.card=2 := crossU
  have q2 : Q.card=2 := crossV
  have union : P∪Q=B := by
    apply Subset.antisymm (union_subset (filter_subset ..) (filter_subset ..))
    intro b bm
    exact (hit b bm).elim (fun h => mem_union_left _ (mem_filter.mpr ⟨bm,h⟩))
      (fun h => mem_union_right _ (mem_filter.mpr ⟨bm,h⟩))
  have split : Disjoint P Q := by
    apply disjoint_iff_inter_eq_empty.mpr
    apply card_eq_zero.mp
    have e := card_union_add_card_inter P Q
    rw [union,p2,q2,b4] at e; omega
  have sees {x : V} (xm : x∈A) (xu : x≠u) (xv : x≠v) {b : V} (bm : b∈B) : G.Adj x b := by
    have miss (c : V) (cm : c∈A) (cb : ¬G.Adj b c) (xc : x≠c) : G.Adj x b := by
      by_contra no
      have sub : A.filter (G.Adj b)⊆(A.erase c).erase x := fun w wm =>
        let k := mem_filter.mp wm
        mem_erase.mpr ⟨fun e => no (e ▸ k.2.symm),mem_erase.mpr ⟨fun e => cb (e ▸ k.2),k.1⟩⟩
      have h := card_le_card sub
      rw [card_erase_of_mem (mem_erase.mpr ⟨xc,xm⟩),card_erase_of_mem cm,a4] at h
      have g := big b bm
      change nbr G b A≤_ at h
      omega
    rcases hit b bm with ub|vb
    · exact miss v va (fun vb => disjoint_left.mp split (mem_filter.mpr ⟨bm,ub⟩) (mem_filter.mpr ⟨bm,vb.symm⟩)) xv
    · exact miss u ua (fun ub => disjoint_left.mp split (mem_filter.mpr ⟨bm,ub.symm⟩) (mem_filter.mpr ⟨bm,vb⟩)) xu
  obtain ⟨p,eq⟩ := card_eq_one.mp (show (A.filter (G.Adj u)).card=1 from thin)
  have up := mem_filter.mp (show p∈A.filter (G.Adj u) from eq ▸ mem_singleton_self _)
  have n : G.neighborFinset u=insert p P := by
    ext w
    constructor
    · intro wm; have e := (G.mem_neighborFinset ..).mp wm
      rcases mem_union.mp (cover u wm) with wa|wb
      · exact mem_insert.mpr (Or.inl (mem_singleton.mp (eq ▸ mem_filter.mpr ⟨wa,e⟩)))
      · exact mem_insert_of_mem (mem_filter.mpr ⟨wb,e⟩)
    · intro h
      exact (G.mem_neighborFinset ..).mpr ((mem_insert.mp h).elim (fun e => e ▸ up.2) (fun m => (mem_filter.mp m).2))
  have pP : p∉P := fun h => disjoint_left.mp dis up.1 (mem_filter.mp h).1
  have pAll {b : V} (bp : b∈P) := sees up.1 up.2.ne.symm (fun e => apart (e ▸ up.2)) (mem_filter.mp bp).1
  have d : nbr G p P=2 := by unfold nbr; rw [filter_eq_self.mpr (fun b h => pAll h),p2]
  have score : trianglesAt G u=(pairs G (G.neighborFinset u)).card := rfl
  rw [n,pairs_insert G pP,d] at score
  have empty : pairs G P=∅ := card_eq_zero.mp (by omega)
  have independent {x y : V} (xp : x∈P) (yp : y∈P) : ¬G.Adj x y := fun e =>
    not_mem_empty _ (empty ▸ ((pair_mem G).mpr ⟨x,xp,y,yp,e,rfl⟩))
  let D := insert u Q
  have uo : u∉Q := fun m => disjoint_left.mp dis ua (mem_filter.mp m).1
  refine ⟨D,insert_subset (mem_union_left _ ua) ((filter_subset ..).trans subset_union_right),by rw [show D=insert u Q from rfl,card_insert_of_not_mem uo,q2],?_⟩
  intro x xm
  obtain ⟨xh,xd⟩ := mem_sdiff.mp xm
  rcases mem_union.mp xh with xa|xb
  · have xu : x≠u := fun e => xd (e ▸ mem_insert_self ..)
    have sub : Q⊆D.filter (G.Adj x) := by
      intro y ym
      by_cases xv : x=v
      · exact mem_filter.mpr ⟨mem_insert_of_mem ym,xv ▸ (mem_filter.mp ym).2⟩
      · exact mem_filter.mpr ⟨mem_insert_of_mem ym,sees xa xu xv (mem_filter.mp ym).1⟩
    exact q2 ▸ card_le_card sub
  · have xo : x∉Q := fun m => xd (mem_insert_of_mem m)
    have xp : x∈P := (mem_union.mp (union.symm ▸ xb)).resolve_right xo
    have xq : ∃y∈Q,G.Adj x y := by
      apply Classical.byContradiction
      intro no
      push_neg at no
      have sub : G.neighborFinset x⊆A.erase v := by
        intro y ym
        have e := (G.mem_neighborFinset ..).mp ym
        refine mem_erase.mpr ⟨fun yv => xo (mem_filter.mpr ⟨xb,yv ▸ e.symm⟩),?_⟩
        rcases mem_union.mp (cover _ ym) with ya|yb
        · exact ya
        · rcases mem_union.mp (union.symm ▸ yb) with yp|yq
          · exact (independent xp yp e).elim
          · exact (no y yq e).elim
      have low := card_le_card sub
      rw [card_neighborFinset_eq_degree,card_erase_of_mem va,a4] at low
      have hi := degree x xb; omega
    obtain ⟨y,yq,xy⟩ := xq
    have sub : {u,y}⊆D.filter (G.Adj x) := insert_subset
      (mem_filter.mpr ⟨mem_insert_self ..,(mem_filter.mp xp).2.symm⟩)
      (singleton_subset_iff.mpr (mem_filter.mpr ⟨mem_insert_of_mem yq,xy⟩))
    have h := card_le_card sub
    rwa [card_pair (show u≠y from fun e => uo (e.symm ▸ yq))] at h
end Graffiti384b.OddStars.EightExchange
#print axioms Graffiti384b.OddStars.EightExchange.three
