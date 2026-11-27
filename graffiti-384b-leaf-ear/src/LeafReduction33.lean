import PositiveCore33

namespace Graffiti384b.PositiveCore33
open Finset SimpleGraph
open private Prune.links from Prune384b
open private TrianglePrune.triangle_iff from TrianglePrune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Reverse the colors on an arbitrary union of components. -/
def flip (A R : Finset V) := univ.filter (fun v => ¬(v∈A ↔ v∈R))

theorem flip_colors {A R : Finset V} {z : V} (h : Colors G z A)
    (closed : ∀ u v,G.Adj u v → (u∈R ↔ v∈R)) : Colors G z (flip A R) := by
  intro v ne
  apply (h v ne).trans (card_le_card ?_)
  intro w wm
  obtain ⟨o,vw⟩ := mem_filter.mp wm
  obtain ⟨wp,c⟩ := mem_filter.mp o
  refine mem_filter.mpr ⟨mem_filter.mpr ⟨wp,?_⟩,vw⟩
  have iff := closed v w vw
  simp only [flip,mem_filter,mem_univ,true_and]
  tauto

/-- The two neighbors of a zero vertex in a failure already communicate by
edges on triangles, without passing through the zero vertex. -/
theorem neighbor_route (n : Fintype.card V=33) (t : (types G).card=33) (fail : bound G<gamma G)
    (inj : Function.Injective (trianglesAt G)) {z a b : V} (zz : trianglesAt G z=0)
    (za : G.Adj z a) (zb : G.Adj z b) : (backbone G z).Reachable a b := by
  classical
  by_cases eq : a=b
  · exact eq ▸ Reachable.refl _
  apply Classical.byContradiction
  intro apart
  let J := backbone G z
  let R := univ.filter (fun v => J.Reachable a v)
  obtain ⟨A,col⟩ := color_exists G inj zz
  have closed (u v : V) (uv : J.Adj u v) : (u∈R ↔ v∈R) := by
    simp only [R,mem_filter,mem_univ,true_and]
    exact ⟨fun p => p.trans uv.reachable,fun p => p.trans uv.symm.reachable⟩
  have fa := flip_colors J col closed
  have one := forced_split G n t fail (lift_colors G col) eq za zb
  have two := forced_split G n t fail (lift_colors G fa) eq za zb
  have ar : a∈R := mem_filter.mpr ⟨mem_univ _,Reachable.refl _⟩
  have br : b∉R := fun m => apart (mem_filter.mp m).2
  simp only [flip,mem_filter,mem_univ,true_and,ar,br,iff_true,iff_false,not_not] at two
  tauto

/-- Delete exactly the edges at the zero vertex other than the chosen one. -/
def leafAt (z a : V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ (u=z → v=a) ∧ (v=z → u=a)
  symm := fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless := fun _ h => h.1.ne rfl

instance (z a : V) : DecidableRel (leafAt G z a).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

private theorem scores_mono (H : SimpleGraph V) [DecidableRel H.Adj] (le : H≤G) (v : V) :
    trianglesAt H v ≤ trianglesAt G v := by
  change (Prune.links H v).card ≤ (Prune.links G v).card
  apply card_le_card
  intro p pm
  obtain ⟨nc,edges⟩ := mem_filter.mp pm
  obtain ⟨sub,sz⟩ := mem_powersetCard.mp nc
  exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨fun w wm => (G.mem_neighborFinset _ _).mpr
    (le ((H.mem_neighborFinset _ _).mp (sub wm))),sz⟩,fun u um w wm ne => le (edges u um w wm ne)⟩

omit [DecidableEq V] in
private theorem gamma_mono (H : SimpleGraph V) [DecidableRel H.Adj] (le : H≤G) : gamma G≤gamma H := by
  have avail : {k : ℕ | ∃ D, TwoDominates H D ∧ D.card=k}.Nonempty := ⟨_,univ,by simp [TwoDominates],rfl⟩
  obtain ⟨D,dom,sz⟩ := Nat.sInf_mem avail
  exact Nat.sInf_le ⟨D,fun v out => (dom v out).trans (card_le_card
    (show D.filter (H.Adj v)⊆D.filter (G.Adj v) from fun w wm => mem_filter.mpr ⟨(mem_filter.mp wm).1,le (mem_filter.mp wm).2⟩)),sz⟩

/-- Any neighbor can be made the sole neighbor, on the same vertex set.
Every individual triangle score and connected failure are preserved. -/
theorem leaf_reduction (n : Fintype.card V=33) (t : (types G).card=33)
    (conn : G.Connected) (fail : bound G<gamma G) (inj : Function.Injective (trianglesAt G))
    {z a : V} (zz : trianglesAt G z=0) (za : G.Adj z a) :
    (leafAt G z a).Connected ∧ (leafAt G z a).neighborFinset z={a} ∧
    (∀ v,trianglesAt (leafAt G z a) v=trianglesAt G v) ∧
    bound (leafAt G z a)<gamma (leafAt G z a) := by
  classical
  let F := leafAt G z a
  have fg : F≤G := fun _ _ h => h.1
  have sub : backbone G z≤F := by
    intro u v edge
    obtain ⟨uv,w,uw,vw⟩ := (backbone_adj G).mp edge
    have up := (TrianglePrune.triangle_iff G u).mpr ⟨v,w,uv,uw,vw⟩
    have vp := (TrianglePrune.triangle_iff G v).mpr ⟨u,w,uv.symm,vw,uw⟩
    exact ⟨uv,fun uz => ((Nat.ne_of_gt up) (uz ▸ zz)).elim,fun vz => ((Nat.ne_of_gt vp) (vz ▸ zz)).elim⟩
  have root : F.Adj z a := ⟨za,fun _ => rfl,fun eq => (za.ne eq.symm).elim⟩
  have fromZ (v : V) (zv : G.Adj z v) : F.Reachable z v :=
    root.reachable.trans (Reachable.mono sub (neighbor_route G n t fail inj zz za zv))
  have connF : F.Connected := by
    apply (connected_iff_exists_forall_reachable F).mpr
    refine ⟨z,fun v => ?_⟩
    have walk := (G.reachable_iff_reflTransGen z v).mp (conn z v)
    induction walk with
    | refl => exact Reachable.refl _
    | @tail u v _ edge ih =>
      apply ih.trans
      by_cases uz : u=z
      · subst u; exact fromZ _ edge
      by_cases vz : v=z
      · subst v; exact (fromZ _ edge.symm).symm
      exact (show F.Adj u v from ⟨edge,fun eq => (uz eq).elim,fun eq => (vz eq).elim⟩).reachable
  have sc (v : V) : trianglesAt F v=trianglesAt G v := by
    apply Nat.le_antisymm (scores_mono G F fg v)
    exact (backbone_scores G z v) ▸ (scores_mono F (backbone G z) sub v)
  have same : types F=types G := congrArg (fun f : V → ℕ => univ.image f) (funext sc)
  have boundEq : bound F=bound G := by simp only [bound,same]
  have neigh : F.neighborFinset z={a} := by
    ext v; rw [F.mem_neighborFinset,mem_singleton]
    exact ⟨fun e => e.2.1 rfl,fun eq => eq ▸ root⟩
  exact ⟨connF,neigh,sc,boundEq ▸ fail.trans_le (gamma_mono G F fg)⟩

end Graffiti384b.PositiveCore33
#print axioms Graffiti384b.PositiveCore33.flip_colors
#print axioms Graffiti384b.PositiveCore33.neighbor_route
#print axioms Graffiti384b.PositiveCore33.leaf_reduction
