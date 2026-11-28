import EarTriangleLoss
namespace Graffiti384b.OddStars.RichCore
open Finset SimpleGraph PositivePalette EarPacking EarFootprint EarTriangleLoss
open private Prune.links from Prune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def fiber (k : ℕ) := (rich G).filter (fun v => EarTriangleLoss.inside G v=k)

/-- A shared internal score can occur at most three times in a failure.
The three possible original scores lie in a single length-three interval. -/
theorem fiber_cap (bad : bound G<gamma G) (k : ℕ) : (fiber G k).card≤3 := by
  classical
  let B := fiber G k
  have inj : Set.InjOn (trianglesAt G) (B : Set V) := fun _ xm _ _ eq =>
    distinct_rich G bad (mem_filter.mp (mem_filter.mp xm).1).2 eq
  have sub : B.image (trianglesAt G)⊆{k,k+1,k+2} := by
    intro n nm; obtain ⟨v,vm,rfl⟩ := mem_image.mp nm
    have internal := (mem_filter.mp vm).2
    have low := card_filter_le (Prune.links (patch G ∅) v) (fun p => p⊆rich G)
    change EarTriangleLoss.inside G v≤trianglesAt (patch G ∅) v at low
    rw [patch_scores] at low
    have high := loss_at_most_two G bad v
    change EarTriangleLoss.inside G v=k at internal
    simp only [mem_insert,mem_singleton]; omega
  have ct := card_le_card sub
  rw [card_image_iff.mpr inj] at ct
  exact ct.trans card_le_three

theorem diversity (bad : bound G<gamma G) (one : 1∈types G) :
    (types G).card≤3*((rich G).image (EarTriangleLoss.inside G)).card+2 := by
  let I := (rich G).image (EarTriangleLoss.inside G)
  have part := card_eq_sum_card_image (EarTriangleLoss.inside G) (rich G)
  change (rich G).card=∑k∈I,(fiber G k).card at part
  have cap : (∑k∈I,(fiber G k).card)≤∑_k∈I,3 := sum_le_sum (fun k _ => fiber_cap G bad k)
  simp only [sum_const,Nat.nsmul_eq_mul] at cap
  have count := rich_count G bad one
  change _≤3*I.card+2
  omega

theorem exact_of_four_equal {k : ℕ} (size : 4≤(fiber G k).card) : gamma G≤bound G := by
  by_contra! bad
  have cap := fiber_cap G bad k
  omega

/-- The full catalogue bound when the internal triangle count is constant
on each component induced by the rich vertices. -/
theorem exact_of_locally_constant (conn : G.Connected) (ord : 2<Fintype.card V)
    (regular : ∀v∈rich G,∀w∈rich G,G.Adj v w → EarTriangleLoss.inside G v=EarTriangleLoss.inside G w) : gamma G≤bound G := by
  classical
  by_contra! bad
  apply (Nat.not_le_of_gt bad) (exact_of_disjoint_rich_triangles G conn ord ?_)
  intro v vr
  let B := fiber G (EarTriangleLoss.inside G v)
  have vb : v∈B := mem_filter.mpr ⟨vr,rfl⟩
  have ct := fiber_cap G bad (EarTriangleLoss.inside G v)
  have limit : (B.erase v).card≤2 := by
    have h := card_erase_add_one vb
    change B.card≤3 at ct
    omega
  let J := patch G ∅
  have sub : (Prune.links J v).filter (fun p => p⊆rich G)⊆(B.erase v).powersetCard 2 := by
    intro p pm
    obtain ⟨pl,allowed⟩ := mem_filter.mp pm
    obtain ⟨ns,two⟩ := mem_powersetCard.mp (mem_filter.mp pl).1
    refine mem_powersetCard.mpr ⟨?_,two⟩
    intro w wm
    have edge := (J.mem_neighborFinset ..).mp (ns wm)
    exact mem_erase.mpr ⟨edge.ne.symm,mem_filter.mpr ⟨allowed wm,(regular v vr w (allowed wm) edge.1).symm⟩⟩
  have count := card_le_card sub
  rw [card_powersetCard] at count
  exact count.trans ((Nat.choose_le_choose 2 limit).trans (by decide))

/-- The local count agrees with the catalogue triangle invariant computed
on the actual induced simple graph. -/
theorem induced_score (v : rich G) : trianglesAt (G.induce (rich G:Set V)) v=EarTriangleLoss.inside G v.val := by
  classical
  let S := rich G
  let H := G.induce (S:Set V)
  let J := patch G ∅
  let emb : S ↪ V := Function.Embedding.subtype _
  have linkSub : Prune.links J v.val⊆Prune.links G v.val := by
    intro p m
    obtain ⟨pm,pe⟩ := mem_filter.mp m
    obtain ⟨sub,sz⟩ := mem_powersetCard.mp pm
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨fun x xm => (G.mem_neighborFinset ..).mpr
      ((J.mem_neighborFinset ..).mp (sub xm)).1,sz⟩,fun x xm y ym ne => (pe x xm y ym ne).1⟩
  have linksEq : Prune.links J v.val=Prune.links G v.val :=
    eq_of_subset_of_card_le linkSub (patch_scores G ∅ v.val).symm.le
  have eq : (Prune.links H v).image (map emb)=(Prune.links G v.val).filter (fun p => p⊆S) := by
    ext p; constructor
    · intro hp
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
      obtain ⟨qq,edge⟩ := mem_filter.mp hq
      obtain ⟨ns,two⟩ := mem_powersetCard.mp qq
      apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_,by simpa using two⟩,?_⟩,?_⟩
      · intro x hx; obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
        exact (G.mem_neighborFinset ..).mpr ((H.mem_neighborFinset ..).mp (ns hy))
      · intro x hx y hy ne
        obtain ⟨w,hw,rfl⟩ := mem_map.mp hx; obtain ⟨z,hz,rfl⟩ := mem_map.mp hy
        exact edge w hw z hz (fun h => ne (congrArg emb h))
      · intro x hx; obtain ⟨w,_,rfl⟩ := mem_map.mp hx; exact w.2
    · intro hp
      obtain ⟨pl,ps⟩ := mem_filter.mp hp
      let q := p.subtype (fun w => w∈S)
      have mapped : q.map emb=p := subtype_map_of_mem ps
      refine mem_image.mpr ⟨q,?_,mapped⟩
      obtain ⟨pm,edge⟩ := mem_filter.mp pl
      obtain ⟨ns,two⟩ := mem_powersetCard.mp pm
      refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_,?_⟩,?_⟩
      · intro w hw
        exact (H.mem_neighborFinset ..).mpr ((G.mem_neighborFinset ..).mp (ns (mem_subtype.mp hw)))
      · have cm := congrArg Finset.card mapped; simpa [two] using cm
      · intro w hw z hz nz
        exact edge w.val (mem_subtype.mp hw) z.val (mem_subtype.mp hz) (fun id => nz (Subtype.ext id))
  change (Prune.links H v).card=((Prune.links J v.val).filter (fun p => p⊆S)).card
  rw [linksEq,←eq,card_image_of_injective _ (Finset.map_injective emb)]

theorem exact_of_component_scores (conn : G.Connected) (ord : 2<Fintype.card V)
    (same : ∀v w : rich G,(G.induce (rich G:Set V)).Adj v w →
      trianglesAt (G.induce (rich G:Set V)) v=trianglesAt (G.induce (rich G:Set V)) w) :
    gamma G≤bound G := by
  apply exact_of_locally_constant G conn ord
  intro v vm w wm adj
  exact (induced_score G ⟨v,vm⟩).symm.trans ((same ⟨v,vm⟩ ⟨w,wm⟩ adj).trans (induced_score G ⟨w,wm⟩))

end Graffiti384b.OddStars.RichCore
#print axioms Graffiti384b.OddStars.RichCore.fiber_cap
#print axioms Graffiti384b.OddStars.RichCore.diversity
#print axioms Graffiti384b.OddStars.RichCore.exact_of_four_equal
#print axioms Graffiti384b.OddStars.RichCore.exact_of_locally_constant
#print axioms Graffiti384b.OddStars.RichCore.induced_score
#print axioms Graffiti384b.OddStars.RichCore.exact_of_component_scores
