import BothCubics33

namespace Graffiti384b.ForcedCubics
open Finset SimpleGraph PositiveCore33 CliquePivot33 EarOnClique33
open private PositiveCore33.positive_clique from CliquePivot33
open private TrianglePrune.reach_closed TrianglePrune.triangle_iff from TrianglePrune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem exact_counts_injective (n : Fintype.card V=33) (t : (types G).card=33) :
    Function.Injective (trianglesAt G) := by
  have sz : (univ.image (trianglesAt G)).card=(univ : Finset V).card := t.trans (n.symm.trans card_univ.symm)
  exact fun i j eq => (card_image_iff.mp sz) (mem_univ i) (mem_univ j) eq

/-- The two small positive scores are forced at cubic vertices in the
original graph, with no triangle normalization and no restriction on z's degree. -/
theorem full_pair (n : Fintype.card V=33) (t : (types G).card=33) (conn : G.Connected)
    (bad : bound G<gamma G) {z : V} (zz : trianglesAt G z=0) :
    ∃ u v,trianglesAt G u=2 ∧ G.degree u=3 ∧ ¬G.Adj z u ∧
      trianglesAt G v=3 ∧ G.degree v=3 ∧ ¬G.Adj z v := by
  classical
  have inj := exact_counts_injective G n t
  have neighbor : ∃ b,G.Adj z b := by
    apply Classical.byContradiction; intro none
    have every (v : V) : v∈({z} : Finset V) := TrianglePrune.reach_closed G {z} (by
      intro u um w uw; obtain rfl := mem_singleton.mp um; exact (none ⟨w,uw⟩).elim) (mem_singleton_self _) (conn z v)
    have eq := congrArg card (eq_univ_of_forall every)
    rw [card_singleton,card_univ,n] at eq; omega
  obtain ⟨a,za⟩ := neighbor
  let P := ({z} : Finset V)ᶜ
  let H := G.induce (P : Set V)
  let R := univ.filter (fun v : P => G.Adj v.val z)
  obtain ⟨sz,_,sc,pos,distinct,g⟩ := extremal_core G n t conn bad inj zz za
  have ord : Fintype.card P=32 := (Fintype.card_coe P).trans sz
  have both : Available H R := by
    rcases dichotomy G n t conn bad inj zz za with ⟨e,_,de,_⟩|⟨_,_,image,roots,_⟩
    · obtain ⟨b,c,eb,ec,bc⟩ := (TrianglePrune.triangle_iff H e).mp (pos e)
      have five : ¬G.CliqueFree 5 := fun free => (not_lt_of_ge (CliqueFrontier34.exact_of_five_clique_free G conn (by omega) t.ge free)) bad
      simp only [CliqueFree,not_forall,Classical.not_not] at five
      obtain ⟨C,cl⟩ := five
      obtain ⟨K,kc⟩ := PositiveCore33.positive_clique G zz cl
      exact both_required H ord de eb ec bc pos distinct kc g.ge (rooted_tight G n t bad z)
    · let B := univ.filter (fun v : P => H.degree v=3)
      have get {k : ℕ} (km : k∈Icc 1 3) : ∃ v : P,H.degree v=3 ∧ trianglesAt H v=k ∧ v∉R := by
        obtain ⟨v,vm,vk⟩ := mem_image.mp (show k∈B.image (trianglesAt H) from image.symm ▸ km)
        exact ⟨v,(mem_filter.mp vm).2,vk,roots v vm⟩
      obtain ⟨u,du,us,ur⟩ := get (by decide : 2∈Icc 1 3)
      obtain ⟨v,dv,vs,vr⟩ := get (by decide : 3∈Icc 1 3)
      exact ⟨u,v,du,us,ur,dv,vs,vr⟩
  have lift (v : P) (vr : v∉R) (d : H.degree v=3) : G.degree v.val=3 ∧ ¬G.Adj z v.val := by
    have vz : ¬G.Adj v.val z := fun ed => vr (mem_filter.mpr ⟨mem_univ _,ed⟩)
    have eq : P.filter (G.Adj v.val)=G.neighborFinset v.val := by
      ext w
      simp only [mem_filter,G.mem_neighborFinset,P,mem_compl,mem_singleton]
      exact ⟨And.right,fun h => ⟨fun eq => vz (eq ▸ h),h⟩⟩
    have num := EarAnchor.induced_degree G (W:=P) v
    change H.degree v=(P.filter (G.Adj v.val)).card at num
    rw [eq,card_neighborFinset_eq_degree] at num
    exact ⟨num ▸ d,fun h => vz h.symm⟩
  obtain ⟨u,v,du,us,ur,dv,vs,vr⟩ := both
  obtain ⟨gu,zu⟩ := lift u ur du
  obtain ⟨gv,zv⟩ := lift v vr dv
  exact ⟨u.val,v.val,(sc u).symm.trans us,gu,zu,(sc v).symm.trans vs,gv,zv⟩

/-- A low-score neighbor of any degree proves the bound. -/
theorem low_score_neighbor (n : Fintype.card V=33) (t : (types G).card=33) (conn : G.Connected)
    {z b : V} (zz : trianglesAt G z=0) (zb : G.Adj z b) (low : trianglesAt G b≤3) :
    gamma G≤bound G := by
  apply Nat.le_of_not_gt; intro bad
  have inj := exact_counts_injective G n t
  obtain ⟨e,es,en,_⟩ := zero_one_separated G n t conn bad inj zz
  obtain ⟨u,v,us,_,un,vs,_,vn⟩ := full_pair G n t conn bad zz
  rcases (show trianglesAt G b=0 ∨ trianglesAt G b=1 ∨ trianglesAt G b=2 ∨ trianglesAt G b=3 by omega) with s|s|s|s
  · exact zb.ne (inj (zz.trans s.symm))
  · exact en (inj (s.trans es.symm) ▸ zb)
  · exact un (inj (s.trans us.symm) ▸ zb)
  · exact vn (inj (s.trans vs.symm) ▸ zb)

/-- Occurrence of both scores transfers through the earlier induced
diversity-33 reduction, so the missing-score criterion holds at every order. -/
theorem missing_score (conn : G.Connected) (hn : 2<Fintype.card V) (t : (types G).card=33)
    (miss : 2∉types G ∨ 3∉types G) : gamma G≤bound G := by
  apply Nat.le_of_not_gt; intro bad
  obtain ⟨s,sz,hc,same,_,_,⟨z,zero,_⟩,fail⟩ := OneEar.diversity33_failure G conn hn bad t
  let J := G.induce (s : Set V)
  obtain ⟨u,v,us,_,_,vs,_,_⟩ := full_pair J ((Fintype.card_coe s).trans sz) ((congrArg card same).trans t) hc fail zero
  have present (v : s) : trianglesAt J v∈types G := same ▸ mem_image_of_mem (trianglesAt J) (mem_univ v)
  exact miss.elim (fun h => h (us ▸ present u)) (fun h => h (vs ▸ present v))

end Graffiti384b.ForcedCubics
#print axioms Graffiti384b.ForcedCubics.full_pair
#print axioms Graffiti384b.ForcedCubics.low_score_neighbor
#print axioms Graffiti384b.ForcedCubics.missing_score
