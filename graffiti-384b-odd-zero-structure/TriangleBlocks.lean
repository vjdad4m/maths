import CutAtVertex

namespace Graffiti384b.OddStars
open Finset SimpleGraph PositivePalette
open private TrianglePrune.triangle_iff from TrianglePrune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- If two degree-two vertices are separated by deleting c, their
protections can be combined. Unsupported edges may all meet a fixed vertex s. -/
theorem separated_pair {e f c : V} (ec : e≠c) (fc : f≠c) (de : G.degree e=2) (df : G.degree f=2)
    (apart : ¬(inside G ({c}ᶜ)).Reachable e f) (s : V)
    (sup : ∀{u v},u≠s → v≠s → G.Adj u v → ∃w,G.Adj u w ∧ G.Adj v w) :
    Covered G (({e}∪{f})∪high G) := by
  classical
  let D := inside G ({c}ᶜ)
  let M := univ.filter (fun v => D.Reachable e v)
  let X := insert c M
  let Y := insert c Mᶜ
  have em : e∈M := mem_filter.mpr ⟨mem_univ _,Reachable.refl _⟩
  have fm : f∉M := fun m => apart (mem_filter.mp m).2
  have only : X∩Y={c} := by ext v; by_cases eq : v=c <;> simp [X,Y,eq]
  have only' : Y∩X={c} := (inter_comm ..).trans only
  have edges {u v : V} (uv : G.Adj u v) : (u∈X ∧ v∈X) ∨ (u∈Y ∧ v∈Y) := by
    by_cases uc : u=c
    · subst u; by_cases m : v∈M <;> simp [X,Y,m]
    by_cases vc : v=c
    · subst v; by_cases m : u∈M <;> simp [X,Y,m]
    have edge : D.Adj u v := ⟨uv,by simpa using uc,by simpa using vc⟩
    have eq : u∈M ↔ v∈M := by
      simp only [M,mem_filter,mem_univ,true_and]
      exact ⟨fun p => p.trans edge.reachable,fun p => p.trans edge.symm.reachable⟩
    by_cases m : u∈M
    · exact Or.inl ⟨mem_insert_of_mem m,mem_insert_of_mem (eq.mp m)⟩
    · exact Or.inr ⟨mem_insert_of_mem (mem_compl.mpr m),mem_insert_of_mem (mem_compl.mpr (fun h => m (eq.mpr h)))⟩
  have side {U T : Finset V} {v : V} (over : U∩T={c}) (vm : v∈U) (vc : v≠c)
      (deg : G.degree v=2) (split : ∀{x y},G.Adj x y → (x∈U ∧ y∈U) ∨ (x∈T ∧ y∈T)) :
      Covered (inside G U) ({v}∪high (inside G U)) := by
    have keep {x y : V} (xu : x∈U) (xc : x≠c) (xy : G.Adj x y) : y∈U :=
      ((split xy).resolve_right (fun p => xc (mem_singleton.mp (over ▸ mem_inter.mpr ⟨xu,p.1⟩)))).2
    have N : (inside G U).neighborFinset v=G.neighborFinset v := by
      ext y; rw [mem_neighborFinset,mem_neighborFinset]
      exact ⟨fun h => h.1,fun h => ⟨h,vm,keep vm vc h⟩⟩
    have d : (inside G U).degree v=2 := by rw [←card_neighborFinset_eq_degree,N,card_neighborFinset_eq_degree,deg]
    rw [show {v}∪high (inside G U)=insert v (high (inside G U)) by ext; simp]
    apply protect_two_stars _ d s
    intro x y _ _ xs ys xy
    obtain ⟨w,xw,yw⟩ := sup xs ys xy.1
    have wu : w∈U := by
      by_cases xc : x=c
      · have yc : y≠c := fun eq => xy.1.ne (xc.trans eq.symm)
        exact keep xy.2.2 yc yw
      · exact keep xy.2.1 xc xw
    exact ⟨w,⟨xw,xy.2.1,wu⟩,⟨yw,xy.2.2,wu⟩⟩
  exact glue G only (fun h => edges h)
    (side only (mem_insert_of_mem em) ec de (fun h => edges h))
    (side only' (mem_insert_of_mem (mem_compl.mpr fm)) fc df (fun h => (edges h).symm))

private theorem true_ear {v : V} (sv : trianglesAt G v=1) (dv : G.degree v=2) (S : Finset V) :
    (patch G S).degree v=2 := by
  have pos : 0<trianglesAt (patch G S) v := by rw [patch_scores,sv]; decide
  obtain ⟨a,b,va,vb,ab⟩ := (TrianglePrune.triangle_iff _ _).mp pos
  have low := Prerequisites.deg2 _ ab.ne va vb
  have sub : (patch G S).neighborFinset v ⊆ G.neighborFinset v :=
    fun _ m => (G.mem_neighborFinset ..).mpr (((patch G S).mem_neighborFinset ..).mp m).1
  have up := card_le_card sub
  simp only [card_neighborFinset_eq_degree] at up
  omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem supported_away {S : Finset V} {s : V} (sub : S⊆{s}) {x y : V} (xs : x≠s) (ys : y≠s)
    (edge : (patch G S).Adj x y) : ∃z,(patch G S).Adj x z ∧ (patch G S).Adj y z := by
  have both := edge.2.resolve_right (fun m => m.elim (fun h => xs (mem_singleton.mp (sub h)))
      (fun h => ys (mem_singleton.mp (sub h))))
  obtain ⟨w,xw,yw⟩ := both
  exact ⟨w,⟨xw,Or.inl ⟨y,edge.1,yw.symm⟩⟩,⟨yw,Or.inl ⟨x,edge.1.symm,xw.symm⟩⟩⟩

/-- In every failure, deleting any third vertex leaves two distinct count-one
vertices joined using only triangle edges. -/
theorem one_ears_in_block (bad : bound G<gamma G) {e f c : V} (ef : e≠f)
    (se : trianglesAt G e=1) (sf : trianglesAt G f=1) (ec : e≠c) (fc : f≠c) :
    (inside (patch G ∅) ({c}ᶜ)).Reachable e f := by
  classical
  have deg {x y : V} (xy : x≠y) (sx : trianglesAt G x=1) (sy : trianglesAt G y=1) :
      G.degree x=2 := by
    have pos : 0<trianglesAt G x := by omega
    obtain ⟨a,b,xa,xb,ab⟩ := (TrianglePrune.triangle_iff _ _).mp pos
    have lo := Prerequisites.deg2 _ ab.ne xa xb
    by_contra! ne
    exact xy (rich_one_unique G bad (by omega) sx sy)
  by_contra apart
  let J := patch G ∅
  have cut := separated_pair J ec fc (true_ear G se (deg ef se sf) ∅)
    (true_ear G sf (deg ef.symm sf se) ∅) apart c (fun xs ys h => supported_away G (empty_subset _) xs ys h)
  let W : Finset V := ({e}∪{f})∪high J
  have ew : e∈W := by simp [W]
  have fw : f∈W := by simp [W]
  have rep := represents_of_high G (S:=∅) (W:=W) subset_union_right (fun _ => ⟨e,ew,se⟩)
  have inj := (rigid G (J:=J) (fun _ _ h => h.1) rep cut bad).2.1
  exact ef (inj ew fw (se.trans sf.symm))

/-- Restore the two edges at a degree-two zero. Deleting any third vertex
still leaves the zero joined to every vertex of count one. -/
theorem zero_ear_in_block (bad : bound G<gamma G) {z e c : V} (zz : trianglesAt G z=0)
    (dz : G.degree z=2) (one : trianglesAt G e=1) (zc : z≠c) (ec : e≠c) :
    (inside (patch G {z}) ({c}ᶜ)).Reachable z e := by
  classical
  by_contra apart
  let J := patch G {z}
  have zdeg : J.degree z=2 := (center_degree G (mem_singleton_self z)).trans dz
  have edeg := true_ear G one ((zero_two_forces_ears G bad zz dz).2 e one) {z}
  have cut := separated_pair J zc ec zdeg edeg apart z (fun xs ys h => supported_away G Subset.rfl xs ys h)
  let W : Finset V := ({z}∪{e})∪high J
  have zw : z∈W := by simp [W]
  have ew : e∈W := by simp [W]
  have rep := represents_of_high G (S:={z}) (W:=W) subset_union_right (fun _ => ⟨e,ew,one⟩)
  have img := (rigid G (J:=J) (fun _ _ h => h.1) rep cut bad).1
  have inside := mem_image_of_mem (trianglesAt G) zw
  rw [img,zz] at inside
  exact not_mem_erase _ _ inside

end Graffiti384b.OddStars
#print axioms Graffiti384b.OddStars.separated_pair
#print axioms Graffiti384b.OddStars.one_ears_in_block
#print axioms Graffiti384b.OddStars.zero_ear_in_block