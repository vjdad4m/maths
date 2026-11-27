import CliquePivot33

namespace Graffiti384b.PositiveCore33
open Finset SimpleGraph CliquePivot33
open private Repair.augment Repair.full_nbr Repair.sparse_triangle_bound from Repair384b
open private Repair.triangles_le_choose from Repair384b
open private TrianglePrune.Closed TrianglePrune.scores_closed TrianglePrune.induced_cost TrianglePrune.triangle_iff from TrianglePrune384b
open private OneEar.deg2 from OneEarFinish384b
open private PositiveCore33.gamma_mono from LeafReduction33
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In the equality case a component of minimum degree four would have a
balanced maximum cut inducing matchings on both sides. The resulting score
range is too short for its distinct positive triangle counts. -/
theorem low_in_tight (hn : 0<Fintype.card V) (pos : ∀ v,0<trianglesAt G v)
    (inj : Function.Injective (trianglesAt G)) (tight : Tight G ∅) :
    ∃ v,trianglesAt G v≤3 := by
  classical
  apply Classical.byContradiction; intro none
  have min4 (v : V) : 4≤G.degree v := by
    have up := Repair.triangles_le_choose G v
    by_contra! low
    have c := Nat.choose_le_choose 2 (by omega : G.degree v≤3)
    exact none ⟨v,up.trans c⟩
  have limit (o : Finset V) (good : ∀ v∈o,2≤nbr G v oᶜ) : 2*o.card≤Fintype.card V := by
    have h := tight oᶜ (fun v out => by
      have m : v∈o := by simpa using out
      simpa only [not_mem_empty,if_false,Nat.add_zero] using good v m)
    rw [card_compl] at h
    have := card_le_univ o; omega
  obtain ⟨A,_,_,left,right⟩ := PinnedColor34.cut G ∅ ∅ (by simp)
  have crossA (v : V) (m : v∈A) : 2≤nbr G v Aᶜ := by
    have := left v m (by simp)
    have := Repair.full_nbr G v A; have := min4 v; omega
  have crossB (v : V) (m : v∈Aᶜ) : 3≤nbr G v (Aᶜ)ᶜ := by
    rw [compl_compl]
    have := right v m (by simp)
    have := Repair.full_nbr G v A; have := min4 v; omega
  have sizeA := limit A crossA
  have sizeB := limit Aᶜ (fun v m => (by have := crossB v m; omega))
  have parts : Aᶜ.card=Fintype.card V-A.card := card_compl _
  have lim := card_le_univ A
  have thinA (v : V) (m : v∈A) : nbr G v A≤1 := by
    apply Nat.le_of_not_gt; intro two
    have extra := limit _ (Repair.augment G crossB (by simpa only [compl_compl] using two))
    rw [card_insert_of_not_mem (fun bm => mem_compl.mp bm m)] at extra
    omega
  have strongA (v : V) (m : v∈A) : 3≤nbr G v Aᶜ := by
    have := Repair.full_nbr G v A; have := min4 v; have := thinA v m; omega
  have thinB (v : V) (m : v∈Aᶜ) : nbr G v Aᶜ≤1 := by
    apply Nat.le_of_not_gt; intro two
    have extra := limit _ (Repair.augment G strongA two)
    rw [card_insert_of_not_mem (mem_compl.mp m)] at extra
    omega
  have ub (v : V) : trianglesAt G v<Fintype.card V := by
    by_cases va : v∈A
    · have := Repair.sparse_triangle_bound G v Aᶜ (by simpa only [compl_compl] using thinA v va) thinB
      omega
    · have := Repair.sparse_triangle_bound G v A (thinB v (mem_compl.mpr va)) thinA
      omega
  have sub : types G⊆Ico 1 (Fintype.card V) := by
    intro j m; obtain ⟨v,_,rfl⟩ := mem_image.mp m; exact mem_Ico.mpr ⟨pos v,ub v⟩
  have cap := card_le_card sub
  change (univ.image (trianglesAt G)).card≤_ at cap
  rw [card_image_of_injective _ inj,card_univ,Nat.card_Ico] at cap; omega

private theorem local_bound {z : V} (zz : trianglesAt G z=0) (inj : Function.Injective (trianglesAt G))
    {S : Finset V} (zs : z∉S) (cl : TrianglePrune.Closed (backbone G z) S) :
    let H := (backbone G z).induce (S : Set V)
    (∀ v : S,trianglesAt H v=trianglesAt G v.val) ∧
      (∀ v,0<trianglesAt H v) ∧ Function.Injective (trianglesAt H) ∧ 2*gamma H≤S.card := by
  let J := backbone G z
  let H := J.induce (S : Set V)
  have sc (v : S) : trianglesAt H v=trianglesAt G v.val :=
    (TrianglePrune.scores_closed J S cl v).trans (backbone_scores G z v.val)
  have pos (v : S) : 0<trianglesAt H v := Nat.pos_of_ne_zero (fun h =>
    zs ((inj ((sc v).symm.trans (h.trans zz.symm))) ▸ v.property))
  have distinct : Function.Injective (trianglesAt H) := fun u v h =>
    Subtype.ext (inj ((sc u).symm.trans (h.trans (sc v))))
  have non : nonleaves H=univ := eq_univ_of_forall (fun v => by
    obtain ⟨u,w,vu,vw,uw⟩ := (TrianglePrune.triangle_iff H v).mp (pos v)
    exact mem_filter.mpr ⟨mem_univ _,OneEar.deg2 H uw.ne vu vw⟩)
  have hh := OneEar.unique_one H (by rw [non]; exact card_image_le) (fun v _ => pos v)
    (fun u v _ _ hu hv => distinct (hu.trans hv.symm)) (fun u v hu hv => distinct (hu.trans hv.symm))
  have card : (types H).card=S.card := (card_image_of_injective _ distinct).trans (card_univ.trans (Fintype.card_coe S))
  unfold bound at hh
  change gamma H≤Fintype.card S-((types H).card+1)/2 at hh
  rw [Fintype.card_coe,card] at hh
  exact ⟨sc,pos,distinct,by change 2*gamma H≤S.card; omega⟩

/-- Every nonempty union of positive triangle components attains equality
at half its own order and contains a score at most three. -/
theorem region_extremal (n : Fintype.card V=33) (t : (types G).card=33) (bad : bound G<gamma G)
    (inj : Function.Injective (trianglesAt G)) {z : V} (zz : trianglesAt G z=0)
    {S : Finset V} (zs : z∉S) (ne : S.Nonempty)
    (closed : ∀ u∈S,∀ v,(backbone G z).Adj u v → v∈S) :
    let H := (backbone G z).induce (S : Set V)
    2*gamma H=S.card ∧ Tight H ∅ ∧ ∃ v∈S,trianglesAt G v≤3 := by
  classical
  let J := backbone G z
  let H := J.induce (S : Set V)
  let P := ({z} : Finset V)ᶜ
  let T := P\S
  have sz : P.card=32 := by simp only [P,card_compl,card_singleton,n]
  have sp : S⊆P := fun v vm => mem_compl.mpr (fun m => zs ((mem_singleton.mp m) ▸ vm))
  have zt : z∉T := fun m => mem_compl.mp (mem_sdiff.mp m).1 (mem_singleton_self _)
  have tc : TrianglePrune.Closed J T := by
    intro u um v uv
    have vp : v∈P := by
      obtain ⟨edge,w,uw,vw⟩ := (backbone_adj G).mp uv
      have := (TrianglePrune.triangle_iff G v).mpr ⟨u,w,edge.symm,vw,uw⟩
      exact mem_compl.mpr (fun m => (Nat.ne_of_gt this) ((mem_singleton.mp m) ▸ zz))
    exact mem_sdiff.mpr ⟨vp,fun vs => (mem_sdiff.mp um).2 (closed v vs u uv.symm)⟩
  obtain ⟨sc,pos,distinct,lo⟩ := local_bound G zz inj zs closed
  have other := (local_bound G zz inj zt tc).2.2.2
  change 2*gamma (J.induce (T : Set V))≤T.card at other
  have combined := Capacity.separated_add J T S ∅ (disjoint_left.mpr (fun _ h m => (mem_sdiff.mp h).2 m))
    (fun _ ut _ vs uv => (mem_sdiff.mp ut).2 (closed _ vs _ uv.symm))
  rw [show T∪S=P from sdiff_union_of_subset sp] at combined
  have cost := TrianglePrune.induced_cost J S
  have rest := TrianglePrune.induced_cost J T
  have up := Capacity.seeded_value J ∅ P ∅ (by simp) (by simp) (by simp) (by simp)
  simp only [card_empty,zero_add,n] at up
  have sub : J≤G := fun _ _ edge => ((backbone_adj G).mp edge).1
  have trans := PositiveCore33.gamma_mono G J sub
  unfold bound at bad; rw [n,t] at bad
  have split : T.card+S.card=P.card := card_sdiff_add_card_eq_card sp
  change S.card≤gamma H+_ at cost
  change 2*gamma H≤S.card at lo
  have eq : 2*gamma H=S.card := by omega
  have tight : Tight H ∅ := by
    intro D good
    have dom : TwoDominates H D := fun v vm => by simpa only [not_mem_empty,if_false,Nat.add_zero] using good v vm
    have h : gamma H≤D.card := Nat.sInf_le ⟨D,dom,rfl⟩
    change Fintype.card S≤2*D.card; rw [Fintype.card_coe]; omega
  obtain ⟨w,score⟩ := low_in_tight H (by change 0<Fintype.card S; rw [Fintype.card_coe]; exact card_pos.mpr ne) pos distinct tight
  exact ⟨eq,tight,w,w.property,(sc w) ▸ score⟩

/-- A region containing a five-clique must contain the unique score-one
vertex. This applies even when edges outside triangles connected the original
positive core. -/
theorem region_one (n : Fintype.card V=33) (t : (types G).card=33) (bad : bound G<gamma G)
    (inj : Function.Injective (trianglesAt G)) {z : V} (zz : trianglesAt G z=0)
    {S : Finset V} (zs : z∉S) (ne : S.Nonempty)
    (closed : ∀ u∈S,∀ v,(backbone G z).Adj u v → v∈S)
    {C : Finset V} (cl : G.IsNClique 5 C) (cs : C⊆S) : ∃ v∈S,trianglesAt G v=1 := by
  classical
  let J := backbone G z
  let H := J.induce (S : Set V)
  obtain ⟨sc,pos,distinct,_⟩ := local_bound G zz inj zs closed
  have tight := (region_extremal G n t bad inj zz zs ne closed).2.1
  let K := C.subtype (fun v => v∈S)
  have map : K.map (Function.Embedding.subtype _)=C := subtype_map_of_mem cs
  have kc : H.IsNClique 5 K := by
    refine ⟨?_,(card_map ..).symm.trans ((congrArg card map).trans cl.2)⟩
    intro u um v vm neq
    have uc := mem_subtype.mp um; have vc := mem_subtype.mp vm
    have uv : u.val≠v.val := fun eq => neq (Subtype.ext eq)
    have num : 1<(C.erase u.val).card := by rw [card_erase_of_mem uc,cl.2]; decide
    obtain ⟨w,wm,wv⟩ := exists_ne_of_one_lt_card num v.val
    exact (backbone_adj G).mpr ⟨cl.1 uc vc uv,w,cl.1 uc (mem_erase.mp wm).2 (mem_erase.mp wm).1.symm,
      cl.1 vc (mem_erase.mp wm).2 wv.symm⟩
  by_cases one : ∃ v : S,H.degree v=2
  · obtain ⟨v,vd⟩ := one
    have cap := Repair.triangles_le_choose H v; rw [vd,Nat.choose_self] at cap
    have p : 0<trianglesAt H v := pos v
    exact ⟨v,v.property,(sc v).symm.trans (show trianglesAt H v=1 by omega)⟩
  have minimum (v : S) : 2≤H.degree v ∧ (v∉(∅ : Finset S) → 3≤H.degree v) := by
    obtain ⟨u,w,vu,vw,uw⟩ := (TrianglePrune.triangle_iff H v).mp (pos v)
    have d := OneEar.deg2 H uw.ne vu vw
    exact ⟨d,fun _ => by have excl : H.degree v≠2 := fun e => one ⟨v,e⟩; omega⟩
  have img := (three_cubics H ∅ minimum pos distinct tight kc).2.1
  have mem : 1∈(univ.filter (fun v : S => H.degree v=3)).image (trianglesAt H) := img.symm ▸ (by decide : 1∈Icc 1 3)
  obtain ⟨v,_,one⟩ := mem_image.mp mem
  exact ⟨v,v.property,(sc v).symm.trans one⟩

end Graffiti384b.PositiveCore33
#print axioms Graffiti384b.PositiveCore33.low_in_tight
#print axioms Graffiti384b.PositiveCore33.region_extremal
#print axioms Graffiti384b.PositiveCore33.region_one
