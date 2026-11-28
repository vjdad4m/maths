import EarFootprint
namespace Graffiti384b.OddStars.EarTriangleLoss
set_option maxHeartbeats 800000
open Finset SimpleGraph PositivePalette EarPacking EarFootprint
open private Prune.links from Prune384b
open private TrianglePrune.triangle_iff from TrianglePrune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Counts the triangles at v whose other two vertices each have score at least two. -/
def inside (v : V) := ((Prune.links (patch G ∅) v).filter (fun p => p⊆rich G)).card

private theorem pair_at {v x : V} {p : Finset V} (hp : p∈Prune.links (patch G ∅) v) (xm : x∈p) :
    ∃u,x≠u ∧ v≠u ∧ v≠x ∧ p={x,u} ∧ (patch G ∅).Adj x v ∧ (patch G ∅).Adj x u ∧ (patch G ∅).Adj v u := by
  let J := patch G ∅
  obtain ⟨n,ed⟩ := mem_filter.mp hp
  obtain ⟨sub,two⟩ := mem_powersetCard.mp n
  obtain ⟨u,um,ux⟩ := exists_ne_of_one_lt_card (show 1<p.card by omega) x
  have vx := (J.mem_neighborFinset ..).mp (sub xm)
  have vu := (J.mem_neighborFinset ..).mp (sub um)
  have eq : {x,u}=p := eq_of_subset_of_card_le (insert_subset xm (singleton_subset_iff.mpr um))
    (by rw [card_pair ux.symm,two])
  exact ⟨u,ux.symm,vu.ne,vx.ne,eq.symm,vx.symm,ed x xm u um ux.symm,vu⟩

private theorem pair_for_one {v x : V} {p : Finset V} (hp : p∈Prune.links (patch G ∅) v)
    (xm : x∈p) (one : trianglesAt G x=1) :
    ∃u,v≠u ∧ v≠x ∧ p={x,u} ∧ (patch G ∅).neighborFinset x={v,u} := by
  let J := patch G ∅
  obtain ⟨u,_,vu,vx,eq,xv,xu,_⟩ := pair_at G hp xm
  have sub : {v,u}⊆J.neighborFinset x := insert_subset ((J.mem_neighborFinset ..).mpr xv)
    (singleton_subset_iff.mpr ((J.mem_neighborFinset ..).mpr xu))
  exact ⟨u,vu,vx,eq,(eq_of_subset_of_card_le sub (by rw [card_pair vu,card_neighborFinset_eq_degree]; exact (one_degree G one).le)).symm⟩

private theorem identifiable {v x : V} {p q : Finset V} (hp : p∈Prune.links (patch G ∅) v)
    (hq : q∈Prune.links (patch G ∅) v) (xp : x∈p) (xq : x∈q) (one : trianglesAt G x=1) : p=q := by
  obtain ⟨u,vu,_,pEq,nx⟩ := pair_for_one G hp xp one
  obtain ⟨w,_,_,qEq,nx'⟩ := pair_for_one G hq xq one
  have em : u∈({v,w}:Finset V) := (nx.symm.trans nx') ▸ mem_insert_of_mem (mem_singleton_self u)
  have uw := mem_singleton.mp ((mem_insert.mp em).resolve_left vu.symm)
  rw [pEq,qEq,uw]

private theorem apart {v x y : V} {p q : Finset V} (hp : p∈Prune.links (patch G ∅) v)
    (hq : q∈Prune.links (patch G ∅) v) (xp : x∈p) (yq : y∈q)
    (one : trianglesAt G x=1) (two : trianglesAt G y=1) (ne : p≠q) :
    x≠y ∧ ¬(patch G ∅).Adj x y := by
  refine ⟨fun eq => ne (identifiable G hp hq xp (eq ▸ yq) one),?_⟩
  intro xy
  obtain ⟨u,_,_,pEq,nx⟩ := pair_for_one G hp xp one
  have ym := ((patch G ∅).mem_neighborFinset ..).mpr xy
  rw [nx] at ym
  have vy := ((patch G ∅).mem_neighborFinset ..).mp ((mem_powersetCard.mp (mem_filter.mp hq).1).1 yq)
  have yu := mem_singleton.mp ((mem_insert.mp ym).resolve_left vy.ne.symm)
  exact ne (identifiable G hp hq (by rw [pEq,yu]; simp) yq two)

/-- At most two incident triangles can be lost at any vertex when all
score-one vertices are removed (with the center itself retained). -/
theorem loss_at_most_two (bad : bound G<gamma G) (v : V) : trianglesAt G v≤ inside G v+2 := by
  classical
  let J := patch G ∅
  let L := Prune.links J v
  let I := L.filter (fun p => p⊆rich G)
  let B := L\I
  have decode {p : Finset V} (pm : p∈B) : ∃x∈p,trianglesAt G x=1 := by
    obtain ⟨lp,ni⟩ := mem_sdiff.mp pm
    have ns : ¬p⊆rich G := fun sub => ni (mem_filter.mpr ⟨lp,sub⟩)
    obtain ⟨x,xp,out⟩ := not_subset.mp ns
    obtain ⟨u,_,_,_,_,xv,xu,vu⟩ := pair_at G lp xp
    have pos := (TrianglePrune.triangle_iff G x).mpr ⟨v,u,xv.1,xu.1,vu.1⟩
    have no : ¬2≤trianglesAt G x := fun h => out (mem_filter.mpr ⟨mem_univ _,h⟩)
    exact ⟨x,xp,by omega⟩
  have maxB : B.card≤2 := by
    by_contra! three
    obtain ⟨p,q,r,pm,qm,rm,pq,pr,qr⟩ := two_lt_card_iff.mp three
    obtain ⟨x,xp,sx⟩ := decode pm
    obtain ⟨y,yq,sy⟩ := decode qm
    obtain ⟨z,zr,sz⟩ := decode rm
    have pp := (mem_sdiff.mp pm).1
    have qq := (mem_sdiff.mp qm).1
    have rr := (mem_sdiff.mp rm).1
    obtain ⟨xy,nxy⟩ := apart G pp qq xp yq sx sy pq
    obtain ⟨xz,nxz⟩ := apart G pp rr xp zr sx sz pr
    obtain ⟨yz,nyz⟩ := apart G qq rr yq zr sy sz qr
    let F : Finset V := {x,y,z}
    have onesF : ∀w∈F,trianglesAt G w=1 := by simp [F,sx,sy,sz]
    have ind : ∀a∈F,∀b∈F,¬J.Adj a b := by
      simp only [F,forall_mem_insert,mem_singleton,forall_eq]
      exact ⟨⟨J.irrefl,nxy,nxz⟩,⟨fun e => nxy e.symm,J.irrefl,nyz⟩,fun e => nxz e.symm,fun e => nyz e.symm,J.irrefl⟩
    have one : 1∈types G := sx ▸ mem_image_of_mem (trianglesAt G) (mem_univ x)
    have inc := (matching_profile G bad one onesF ind).1
    obtain ⟨i,_,_,_,nx⟩ := pair_for_one G pp xp sx
    obtain ⟨j,_,_,_,ny⟩ := pair_for_one G qq yq sy
    obtain ⟨k,_,_,_,nz⟩ := pair_for_one G rr zr sz
    have cover : anchors G F⊆{v,i,j,k} := by
      intro w wm
      obtain ⟨a,af,wa⟩ := mem_biUnion.mp (mem_inter.mp wm).1
      rcases (show a=x ∨ a=y ∨ a=z by simpa [F] using af) with rfl|rfl|rfl
      · rw [nx] at wa; simp only [mem_insert,mem_singleton] at wa ⊢; exact wa.elim Or.inl (fun h => Or.inr (Or.inl h))
      · rw [ny] at wa; simp only [mem_insert,mem_singleton] at wa ⊢; exact wa.elim Or.inl (fun h => Or.inr (Or.inr (Or.inl h)))
      · rw [nz] at wa; simp only [mem_insert,mem_singleton] at wa ⊢; exact wa.elim Or.inl (fun h => Or.inr (Or.inr (Or.inr h)))
    have lim := (card_le_card cover).trans card_le_four
    have sizeF : F.card=3 := by simp [F,xy,xz,yz]
    omega
  have total := card_sdiff_add_card_eq_card (filter_subset (fun p => p⊆rich G) L)
  change B.card+I.card=L.card at total
  have score : L.card=trianglesAt G v := patch_scores G ∅ v
  change _≤I.card+2
  omega

/-- A hypothetical failure needs a rich center with at least t−3
triangles formed entirely by rich vertices, where t is the diversity. -/
theorem dense_center (conn : G.Connected) (ord : 2<Fintype.card V) (bad : bound G<gamma G) :
    ∃v∈rich G,(types G).card≤ inside G v+3 := by
  classical
  have big : 4<(types G).card := by
    by_contra! small
    exact (Nat.not_le_of_gt bad) (exact_of_at_most_four G conn ord small)
  have nz : (types G).Nonempty := card_pos.mp (by omega)
  let m := (types G).max' nz
  obtain ⟨v,_,eq⟩ := mem_image.mp ((types G).max'_mem nz)
  have sub : types G⊆range (m+1) := fun k km => mem_range.mpr (Nat.lt_succ_of_le (le_max' _ _ km))
  have ct := card_le_card sub
  rw [card_range] at ct
  change trianglesAt G v=m at eq
  have insideBound := loss_at_most_two G bad v
  exact ⟨v,mem_filter.mpr ⟨mem_univ _,by omega⟩,by omega⟩

/-- If the subgraph on score-at-least-two vertices has vertex-disjoint
triangles, the full catalogue inequality holds in every admissible order. -/
theorem exact_of_disjoint_rich_triangles (conn : G.Connected) (ord : 2<Fintype.card V)
    (few : ∀v∈rich G,inside G v≤1) : gamma G≤bound G := by
  by_contra! bad
  have cap (v : V) : trianglesAt G v≤3 := by
    by_cases richV : 2≤trianglesAt G v
    · have a := few v (mem_filter.mpr ⟨mem_univ _,richV⟩); have b := loss_at_most_two G bad v; omega
    · omega
  have sub : types G⊆range 4 := by
    intro n nm; obtain ⟨v,_,rfl⟩ := mem_image.mp nm; exact mem_range.mpr (by have a := cap v; omega)
  have count := card_le_card sub
  rw [card_range] at count
  exact (Nat.not_le_of_gt bad) (exact_of_at_most_four G conn ord count)

end Graffiti384b.OddStars.EarTriangleLoss
#print axioms Graffiti384b.OddStars.EarTriangleLoss.loss_at_most_two
#print axioms Graffiti384b.OddStars.EarTriangleLoss.dense_center
#print axioms Graffiti384b.OddStars.EarTriangleLoss.exact_of_disjoint_rich_triangles
