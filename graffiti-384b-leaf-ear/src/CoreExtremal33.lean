import LeafReduction33

namespace Graffiti384b.PositiveCore33
open Finset SimpleGraph
open private TrianglePrune.triangle_iff TrianglePrune.induced_cost from TrianglePrune384b
open private EarPrune.score_congr from EarPrune384b
open private OneEar.deg2 from OneEarFinish384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Removing the zero vertex leaves a connected 32-vertex graph of exact
2-domination number 16. The remaining vertex scores are preserved individually. -/
theorem extremal_core (n : Fintype.card V=33) (t : (types G).card=33) (conn : G.Connected)
    (fail : bound G<gamma G) (inj : Function.Injective (trianglesAt G))
    {z a : V} (zz : trianglesAt G z=0) (za : G.Adj z a) :
    let P := ({z} : Finset V)ᶜ
    let H := G.induce (P : Set V)
    P.card=32 ∧ H.Connected ∧ (∀ v : P,trianglesAt H v=trianglesAt G v.val) ∧
      (∀ v,0<trianglesAt H v) ∧ Function.Injective (trianglesAt H) ∧ gamma H=16 := by
  classical
  let P := ({z} : Finset V)ᶜ
  let F := leafAt G z a
  let H := G.induce (P : Set V)
  have nonzero (v : P) : v.val≠z := fun eq => (mem_compl.mp v.property) (mem_singleton.mpr eq)
  have sz : P.card=32 := by simp only [P,card_compl,card_singleton,n]
  have instSize : Fintype.card P=32 := (Fintype.card_coe P).trans sz
  obtain ⟨fc,neigh,fsc,_⟩ := leaf_reduction G n t conn fail inj zz za
  have keep : nonleaves F⊆P := by
    intro v vm
    apply mem_compl.mpr
    intro m
    obtain rfl := mem_singleton.mp m
    have dz : F.degree v=1 := by rw [← card_neighborFinset_eq_degree,neigh,card_singleton]
    have := (mem_filter.mp vm).2
    omega
  have eq : F.induce (P : Set V)=H := by
    ext u v
    change (G.Adj u.val v.val ∧ (u.val=z → v.val=a) ∧ (v.val=z → u.val=a)) ↔ G.Adj u.val v.val
    simp [nonzero u,nonzero v]
  have hcon : H.Connected := eq ▸ Prune.connected_core F fc keep (card_pos.mp (by omega : 0<P.card))
  have sc (v : P) : trianglesAt H v=trianglesAt G v.val := (EarPrune.score_congr _ _ eq v).symm.trans
    ((Prune.counts_preserved F P keep v).trans (fsc v.val))
  have pos (v : P) : 0<trianglesAt H v := Nat.pos_of_ne_zero
    (fun zero => nonzero v (inj ((sc v).symm.trans (zero.trans zz.symm))))
  have distinct : Function.Injective (trianglesAt H) := fun u v h =>
    Subtype.ext (inj ((sc u).symm.trans (h.trans (sc v))))
  have allNon : nonleaves H=univ := eq_univ_of_forall (fun v => by
    obtain ⟨x,y,vx,vy,xy⟩ := (TrianglePrune.triangle_iff H v).mp (pos v)
    exact mem_filter.mpr ⟨mem_univ _,OneEar.deg2 H xy.ne vx vy⟩)
  have exactH := OneEar.unique_one H (by rw [allNon]; exact card_image_le) (fun v _ => pos v)
    (fun u v _ _ hu hv => distinct (hu.trans hv.symm)) (fun u v hu hv => distinct (hu.trans hv.symm))
  have typesH : (types H).card=32 := by
    change (univ.image (trianglesAt H)).card=_
    rw [card_image_of_injective _ distinct,card_univ]
    exact instSize
  unfold bound at exactH fail
  change gamma H≤Fintype.card P-((types H).card+1)/2 at exactH
  rw [instSize,typesH] at exactH
  rw [n,t] at fail
  have up := Capacity.seeded_value G ∅ P ∅ (by simp) (by simp) (by simp) (by simp)
  have cost := TrianglePrune.induced_cost G P
  simp only [card_empty,zero_add,n] at up
  change P.card≤gamma H + _ at cost
  exact ⟨sz,hcon,sc,pos,distinct,by change gamma H=16; omega⟩

/-- Every union of entire triangle components has equally many positive vertices
of either color. In particular each positive triangle component has even order. -/
theorem balanced_region (n : Fintype.card V=33) (t : (types G).card=33) (fail : bound G<gamma G)
    {z : V} {A R : Finset V} (zr : z∉R) (colors : Colors (backbone G z) z A)
    (closed : ∀ u v,(backbone G z).Adj u v → (u∈R ↔ v∈R)) :
    (R∩A).card=(R\A).card ∧ R.card%2=0 := by
  have left := (balanced G n t fail (lift_colors G colors)).1
  have flipped := (balanced G n t fail (lift_colors G (flip_colors (backbone G z) colors closed))).1
  let outside := (A.erase z)\R
  have dis1 : Disjoint outside (R∩A) := disjoint_left.mpr (fun v vo vi => (mem_sdiff.mp vo).2 (mem_inter.mp vi).1)
  have dis2 : Disjoint outside (R\A) := disjoint_left.mpr (fun v vo vi => (mem_sdiff.mp vo).2 (mem_sdiff.mp vi).1)
  have eq1 : outside ∪ (R∩A)=A.erase z := by
    ext v
    by_cases vz : v=z
    · subst v; simp [outside,zr]
    · simp [outside,vz]; tauto
  have eq2 : outside ∪ (R\A)=(flip A R).erase z := by
    ext v
    by_cases vz : v=z
    · subst v; simp [outside,zr]
    · simp [outside,flip,vz]; tauto
  rw [← eq1,card_union_of_disjoint dis1] at left
  rw [← eq2,card_union_of_disjoint dis2] at flipped
  have parts := card_sdiff_add_card_inter R A
  omega

end Graffiti384b.PositiveCore33
#print axioms Graffiti384b.PositiveCore33.extremal_core
#print axioms Graffiti384b.PositiveCore33.balanced_region
