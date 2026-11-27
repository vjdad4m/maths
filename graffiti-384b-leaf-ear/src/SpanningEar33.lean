import SupportComponent33

namespace Graffiti384b.PositiveCore33
open Finset SimpleGraph CliquePivot33
open private Prune.links from Prune384b
open private TrianglePrune.skeleton TrianglePrune.scores TrianglePrune.triangle_iff TrianglePrune.reach_closed from TrianglePrune384b
open private PositiveCore33.positive_clique from CliquePivot33
open private PositiveCore33.gamma_mono from LeafReduction33
open private Repair.triangles_le_choose from Repair384b

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A cubic vertex of score at least two has triangle support on every edge. -/
theorem cubic_supported {v w : V} (d : G.degree v=3) (s : 2≤trianglesAt G v) (vw : G.Adj v w) :
    ∃ u,G.Adj v u ∧ G.Adj w u := by
  apply Classical.byContradiction; intro no
  have sub : Prune.links G v⊆((G.neighborFinset v).erase w).powersetCard 2 := by
    intro p pm; obtain ⟨nc,edges⟩ := mem_filter.mp pm
    obtain ⟨np,sz⟩ := mem_powersetCard.mp nc
    refine mem_powersetCard.mpr ⟨fun a am => mem_erase.mpr ⟨?_,np am⟩,sz⟩
    intro eq; subst a
    obtain ⟨u,um,uw⟩ := exists_ne_of_one_lt_card (by omega : 1<p.card) w
    exact no ⟨u,(G.mem_neighborFinset _ _).mp (np um),edges w am u um uw.symm⟩
  have bd := card_le_card sub
  rw [card_powersetCard,card_erase_of_mem ((G.mem_neighborFinset _ _).mpr vw),card_neighborFinset_eq_degree,d] at bd
  change (Prune.links G v).card≤1 at bd
  change 2≤(Prune.links G v).card at s
  omega

omit [Fintype V] in
private theorem each_hits {H : SimpleGraph V} [DecidableRel H.Adj] {B C : Finset V} (bs : B.card=3)
    (cs : C.card=5) (cover : C⊆B.biUnion (fun v => C.filter (H.Adj v)))
    (two : ∀ v∈B,nbr H v C≤2) {u : V} (um : u∈B) : ∃ k∈C,H.Adj u k := by
  classical
  apply Classical.byContradiction; intro no
  have sub : C⊆(B.erase u).biUnion (fun v => C.filter (H.Adj v)) := by
    intro k km
    obtain ⟨v,vm,vk⟩ := mem_biUnion.mp (cover km)
    exact mem_biUnion.mpr ⟨v,mem_erase.mpr ⟨fun eq => no ⟨k,km,eq ▸ (mem_filter.mp vk).2⟩,vm⟩,vk⟩
  have count : C.card≤(B.erase u).card*2 := calc
    _ ≤ _ := card_le_card sub
    _ ≤ ∑ v ∈ B.erase u,(C.filter (H.Adj v)).card := card_biUnion_le
    _ ≤ ∑ _v ∈ B.erase u,2 := sum_le_sum (fun v vm => two v (mem_erase.mp vm).2)
    _ = _ := by simp
  rw [card_erase_of_mem um,bs,cs] at count
  omega

/-- In the cubic alternative all positive vertices belong to a single triangle
component. Scores 1, 2 and 3 are all in the component of a five-clique, and
a different component would also need one of those scores. -/
theorem cubic_core_routes (n : Fintype.card V=33) (t : (types G).card=33) (conn : G.Connected)
    (bad : bound G<gamma G) (inj : Function.Injective (trianglesAt G)) {z a : V}
    (zz : trianglesAt G z=0) (za : G.Adj z a)
    (minimum : let P := ({z} : Finset V)ᶜ; ∀ v : P,3≤(G.induce (P : Set V)).degree v) :
    ∀ u v,u≠z → v≠z → (backbone G z).Reachable u v := by
  classical
  let P := ({z} : Finset V)ᶜ
  let H := G.induce (P : Set V)
  let J := backbone G z
  let R := univ.filter (fun v : P => G.Adj v.val z)
  let B := univ.filter (fun v : P => H.degree v=3)
  obtain ⟨_,_,sc,pos,distinct,_⟩ := extremal_core G n t conn bad inj zz za
  have five : ¬G.CliqueFree 5 := fun f => (not_lt_of_ge (CliqueFrontier34.exact_of_five_clique_free G conn (by omega) t.ge f)) bad
  simp only [CliqueFree,not_forall,Classical.not_not] at five
  obtain ⟨C,cl⟩ := five
  obtain ⟨K,kc⟩ := PositiveCore33.positive_clique G zz cl
  let C' := K.map (Function.Embedding.subtype _)
  have cc : G.IsNClique 5 C' := by
    refine ⟨?_,(card_map ..).trans kc.2⟩
    intro u um v vm ne
    obtain ⟨w,wm,rfl⟩ := mem_map.mp um; obtain ⟨j,jm,rfl⟩ := mem_map.mp vm
    exact kc.1 wm jm (fun eq => ne (congrArg Subtype.val eq))
  have cne : C'.Nonempty := card_pos.mp (by rw [cc.2]; decide)
  obtain ⟨c,cm⟩ := cne
  let S := univ.filter (fun v => J.Reachable c v)
  have cS : c∈S := mem_filter.mpr ⟨mem_univ _,Reachable.refl _⟩
  have cp : c∈P := by obtain ⟨w,_,rfl⟩ := mem_map.mp cm; exact w.property
  have cclosed (u : V) (us : u∈S) (v : V) (uv : J.Adj u v) : v∈S :=
    mem_filter.mpr ⟨mem_univ _,(mem_filter.mp us).2.trans uv.reachable⟩
  have pclosed (u : V) (_um : u∈P) (v : V) (uv : J.Adj u v) : v∈P := by
    obtain ⟨edge,w,uw,vw⟩ := (backbone_adj G).mp uv
    have vp := (TrianglePrune.triangle_iff G v).mpr ⟨u,w,edge.symm,vw,uw⟩
    exact mem_compl.mpr (fun m => (Nat.ne_of_gt vp) ((mem_singleton.mp m) ▸ zz))
  have zs : z∉S := fun h => mem_compl.mp (TrianglePrune.reach_closed J P pclosed cp (mem_filter.mp h).2) (mem_singleton_self _)
  have inS : C'⊆S := by
    intro v vm
    by_cases eq : c=v
    · exact eq ▸ cS
    have many : 1<(C'.erase c).card := by rw [card_erase_of_mem cm,cc.2]; decide
    obtain ⟨w,wm,wv⟩ := exists_ne_of_one_lt_card many v
    exact cclosed c cS v ((backbone_adj G).mpr ⟨cc.1 cm vm eq,w,cc.1 cm (mem_erase.mp wm).2 (mem_erase.mp wm).1.symm,
      cc.1 vm (mem_erase.mp wm).2 wv.symm⟩)
  have min {v : P} : 3≤H.degree v := minimum v
  have cubic := three_cubics H R (fun v => ⟨by have := @min v; omega,fun _ => @min v⟩) pos distinct (rooted_tight G n t bad z) kc
  obtain ⟨size,image,light,cover⟩ := cubic
  have allLow (v : V) (vp : v∈P) (low : trianglesAt G v≤3) : v∈S := by
    by_cases vs : trianglesAt G v=1
    · obtain ⟨w,ws,one⟩ := region_one G n t bad inj zz zs ⟨c,cS⟩ cclosed cc inS
      exact (inj (one.trans vs.symm)) ▸ ws
    let i : P := ⟨v,vp⟩
    have hpos : 0<trianglesAt G v := (sc i) ▸ (pos i)
    have sm : trianglesAt H i∈Icc 1 3 := by rw [show trianglesAt H i=trianglesAt G v from sc i]; exact mem_Icc.mpr ⟨hpos,low⟩
    have im : trianglesAt H i∈B.image (trianglesAt H) := (show B.image (trianglesAt H)=Icc 1 3 from image) ▸ sm
    obtain ⟨j,jm,eq⟩ := mem_image.mp im
    have ib : i∈B := (distinct eq) ▸ jm
    obtain ⟨k,km,ik⟩ := each_hits size kc.2 cover (fun w wm => (light w wm).2.2) ib
    have ki : k.val∈S := inS (mem_map.mpr ⟨k,km,rfl⟩)
    have hi : 2≤trianglesAt H i := by rw [show trianglesAt H i=trianglesAt G v from sc i]; omega
    obtain ⟨w,iw,kw⟩ := cubic_supported H (mem_filter.mp ib).2 hi ik
    exact cclosed k.val ki v ((backbone_adj G).mpr ⟨ik.symm,w.val,kw,iw⟩)
  have all (v : V) (vz : v≠z) : v∈S := by
    apply Classical.byContradiction; intro out
    let T := P\S
    have vt : v∈T := mem_sdiff.mpr ⟨mem_compl.mpr (fun m => vz (mem_singleton.mp m)),out⟩
    have closed (u : V) (ut : u∈T) (w : V) (uw : J.Adj u w) : w∈T := mem_sdiff.mpr
      ⟨pclosed u (mem_sdiff.mp ut).1 w uw,fun ws => (mem_sdiff.mp ut).2 (cclosed w ws u uw.symm)⟩
    have zt : z∉T := fun m => mem_compl.mp (mem_sdiff.mp m).1 (mem_singleton_self _)
    obtain ⟨w,wt,small⟩ := (region_extremal G n t bad inj zz zt ⟨v,vt⟩ closed).2.2
    exact (mem_sdiff.mp wt).2 (allLow _ (mem_sdiff.mp wt).1 small)
  intro u v uz vz
  exact (mem_filter.mp (all u uz)).2.symm.trans (mem_filter.mp (all v vz)).2


set_option maxHeartbeats 1200000 in
/-- A counterexample on 33 vertices with 33 types has a connected spanning
counterexample with the prescribed leaf edge and exactly one degree-two vertex.
The latter is the original score-one vertex, and every individual score survives. -/
theorem spanning_leaf_ear (n : Fintype.card V=33) (t : (types G).card=33) (conn : G.Connected)
    (bad : bound G<gamma G) (inj : Function.Injective (trianglesAt G)) {z a : V}
    (zz : trianglesAt G z=0) (za : G.Adj z a) :
    ∃ (F : SimpleGraph V) (d : DecidableRel F.Adj), letI := d
      F≤G ∧ F.Connected ∧ bound F<gamma F ∧ (∀ v,trianglesAt F v=trianglesAt G v) ∧
      F.neighborFinset z={a} ∧ ∃ y,trianglesAt G y=1 ∧ ¬G.Adj z y ∧
        F.degree y=2 ∧ (∀ w,F.degree w=2 → w=y) := by
  classical
  let P := ({z} : Finset V)ᶜ
  let H := G.induce (P : Set V)
  obtain ⟨y,one,no,_⟩ := zero_one_separated G n t conn bad inj zz
  have yz : y≠z := fun eq => Nat.one_ne_zero (one.symm.trans (eq ▸ zz))
  have ya : y≠a := fun eq => no (eq ▸ za)
  have finish (F : SimpleGraph V) [DecidableRel F.Adj] (fg : F≤G) (fc : F.Connected)
      (sc : ∀ v,trianglesAt F v=trianglesAt G v) (leaf : F.neighborFinset z={a}) (dy : F.degree y=2) :
      F≤G ∧ F.Connected ∧ bound F<gamma F ∧ (∀ v,trianglesAt F v=trianglesAt G v) ∧
      F.neighborFinset z={a} ∧ ∃ v,trianglesAt G v=1 ∧ ¬G.Adj z v ∧ F.degree v=2 ∧
        (∀ w,F.degree w=2 → w=v) := by
    have same : types F=types G := congrArg (fun f : V → ℕ => univ.image f) (funext sc)
    have bd : bound F=bound G := by simp only [bound,same]
    refine ⟨fg,fc,bd ▸ bad.trans_le (PositiveCore33.gamma_mono G F fg),sc,leaf,y,one,no,dy,?_⟩
    intro w dw
    have dz : F.degree z=1 := by rw [← card_neighborFinset_eq_degree,leaf,card_singleton]
    have pos : 0<trianglesAt F w := Nat.pos_of_ne_zero (fun s => by
      have eq := inj ((sc w).symm.trans (s.trans zz.symm)); subst w; omega)
    have ub := Repair.triangles_le_choose F w
    rw [dw,Nat.choose_self] at ub
    exact inj ((sc w).symm.trans ((show trianglesAt F w=1 by omega).trans one.symm))
  rcases dichotomy G n t conn bad inj zz za with ⟨e,es,ed,er⟩|⟨min3,_,_,_,_⟩
  · let F := leafAt G z a
    obtain ⟨fc,leaf,sc,_⟩ := leaf_reduction G n t conn bad inj zz za
    have es' := (extremal_core G n t conn bad inj zz za).2.2.1 e
    have eq : e.val=y := inj (es'.symm.trans (es.trans one.symm))
    have sub : G.neighborSet e.val ⊆ (P : Set V) := by
      intro v vm
      apply mem_compl.mpr; intro vz
      exact no (eq ▸ (mem_singleton.mp vz) ▸ (show G.Adj e.val v from vm).symm)
    have mapped : (H.neighborFinset e).map (Function.Embedding.subtype _)=G.neighborFinset e.val := by
      ext w; constructor
      · intro wm; obtain ⟨k,km,rfl⟩ := mem_map.mp wm
        exact (G.mem_neighborFinset _ _).mpr ((H.mem_neighborFinset _ _).mp km)
      · intro wm
        have ew := (G.mem_neighborFinset _ _).mp wm
        exact mem_map.mpr ⟨⟨w,sub ew⟩,(H.mem_neighborFinset _ _).mpr ew,rfl⟩
    have de := congrArg card mapped
    rw [card_map,card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at de
    have dg : G.degree y=2 := eq ▸ (de.symm.trans ed)
    have nb : F.neighborFinset y=G.neighborFinset y := by
      ext w; rw [F.mem_neighborFinset,G.mem_neighborFinset]
      exact ⟨fun h => h.1,fun edge => ⟨edge,fun e' => (yz e').elim,fun eq' => (no (eq' ▸ edge.symm)).elim⟩⟩
    have df : F.degree y=2 := by rw [← card_neighborFinset_eq_degree,nb,card_neighborFinset_eq_degree,dg]
    exact ⟨F,inferInstance,finish F (fun _ _ h => h.1) fc sc leaf df⟩
  · let F := TrianglePrune.skeleton G a {z}
    have fg : F≤G := fun _ _ h => h.1
    have sc (v : V) : trianglesAt F v=trianglesAt G v := TrianglePrune.scores G a {z} v
    have bg : backbone G z≤F := fun _ _ h => ⟨((backbone_adj G).mp h).1,Or.inl ((backbone_adj G).mp h).2⟩
    have root : F.Adj z a := ⟨za,Or.inr (Or.inl ⟨mem_singleton_self _,rfl⟩)⟩
    have leaf : F.neighborFinset z={a} := by
      ext v; rw [F.mem_neighborFinset,mem_singleton]
      constructor
      · intro edge
        rcases edge.2 with ⟨w,zw,vw⟩|⟨_,eq⟩|⟨_,eq⟩
        · have := (TrianglePrune.triangle_iff G z).mpr ⟨v,w,edge.1,zw,vw⟩; omega
        · exact eq
        · exact (za.ne eq).elim
      · intro eq; exact eq ▸ root
    have fc : F.Connected := by
      apply (connected_iff_exists_forall_reachable F).mpr
      refine ⟨a,fun v => ?_⟩
      by_cases vz : v=z
      · exact vz ▸ root.symm.reachable
      exact Reachable.mono bg (cubic_core_routes G n t conn bad inj zz za min3 a v za.ne.symm vz)
    have normal : TrianglePrune.Normal F := by
      refine ⟨fun u v su sv => inj ((sc u).symm.trans (su.trans (sv.symm.trans (sc v)))),?_,?_⟩
      · intro w wz u v wu wv
        have eq := inj ((sc w).symm.trans (wz.trans zz.symm)); subst w
        have eu := (F.mem_neighborFinset _ _).mpr wu; have ev := (F.mem_neighborFinset _ _).mpr wv
        rw [leaf,mem_singleton] at eu ev; exact eu.trans ev.symm
      · intro u v edge pu pv
        rcases edge.2 with ⟨w,uw,vw⟩|⟨um,_⟩|⟨vm,_⟩
        · exact ⟨w,bg ((backbone_adj G).mpr ⟨uw,v,edge.1,vw.symm⟩),bg ((backbone_adj G).mpr ⟨vw,u,edge.1.symm,uw.symm⟩)⟩
        · have eq : u=z := mem_singleton.mp um; rw [sc,eq,zz] at pu; omega
        · have eq : v=z := mem_singleton.mp vm; rw [sc,eq,zz] at pv; omega
    obtain ⟨u,v,uv,nb⟩ := Minimal.score_one_ear F normal y ((sc y).trans one) (fun w edge =>
      Nat.pos_of_ne_zero (fun s => no ((inj ((sc w).symm.trans (s.trans zz.symm))) ▸ (fg edge).symm)))
    have d : F.degree y=2 := by rw [← card_neighborFinset_eq_degree,nb,card_pair uv.ne]
    exact ⟨F,inferInstance,finish F fg fc sc leaf d⟩

end Graffiti384b.PositiveCore33
#print axioms Graffiti384b.PositiveCore33.cubic_supported
#print axioms Graffiti384b.PositiveCore33.cubic_core_routes
#print axioms Graffiti384b.PositiveCore33.spanning_leaf_ear
