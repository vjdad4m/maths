import FlankIllumination189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath Graffiti189LongestPath.Rigidity
open Graffiti189LongestPath.OneSlack Graffiti189LongestPath.SingleStar
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two
  Graffiti189LongestPath.boundary_card_of_connectivity from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.mem_omittedStar Graffiti189LongestPath.Rigidity.mem_external Graffiti189LongestPath.Rigidity.pin_pos from Rigidity189
open private Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary
  Graffiti189LongestPath.OneSlack.cardinal_flankVertices from OneSlack189
set_option warningAsError true
namespace Graffiti189LongestPath.FlankShore
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every component beyond the exact singleton star cut contains a flank.
Moreover the pin's neighbors in that component are precisely its flanks. -/
theorem pins_meet_complement_in_flanks (hc : G.Connected) (k : Nat)
    (cap : ∀ v, (EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x∉p.support)
    (one : (Pins p x).card=1) (far : (Shell G x 4).Nonempty)
    {i : Nat} (hi : i∈Pins p x)
    (C : Finset V) (cn : C.Nonempty)
    (ca : Disjoint C (OmittedStar p x)) (cb : Disjoint C (External G (OmittedStar p x)))
    (closed : ∀ u∈C,∀ v∉C,G.Adj u v → v∈External G (OmittedStar p x)) :
    (C.filter (G.Adj (p.getVert i))).Nonempty ∧
      C.filter (G.Adj (p.getVert i)) = C∩FlankVertices p x := by
  classical
  let t := p.getVert i
  let A := OmittedStar p x
  let B := External G A
  let F := FlankVertices p x
  have hxA : x∈A := Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have ab : Disjoint A B := disjoint_left.mpr (fun _ h h' =>
    (Graffiti189LongestPath.Rigidity.mem_external.mp h').1 h)
  have tx : G.Adj x t := (Graffiti189LongestPath.pin_data hi).2
  have htB : t∈B := Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary hx
    (mem_image.mpr ⟨i,hi,rfl⟩)
  have hstar := singleton_star_budget hc k conn hp hx one (cap x)
  obtain ⟨bk,rigid⟩ := hstar.2.2.2.2.1 far
  change B.card=k at bk
  change DistanceTwo G x \ B=F at rigid
  have bsmall : (B.erase t).card+1=k := (card_erase_add_one htB).trans bk
  have existsN : (C.filter (G.Adj t)).Nonempty := by
    apply Classical.byContradiction
    intro fail
    obtain ⟨s,hs⟩ := cn
    have hb : ∀ u∈C,∀ v∉C,G.Adj u v → v∈B.erase t := by
      intro u hu v hv ed
      have b : v∈B := closed u hu v hv ed
      have ne : v≠t := fun e => fail ⟨u,mem_filter.mpr ⟨hu,e ▸ ed.symm⟩⟩
      exact mem_erase.mpr ⟨ne,b⟩
    have dis : Disjoint C (B.erase t) := disjoint_left.mpr
      (fun _ h h' => disjoint_left.mp cb h (mem_erase.mp h').2)
    have k := Graffiti189LongestPath.boundary_card_of_connectivity k conn hs
      (fun e => disjoint_left.mp ca e hxA)
      (fun e => disjoint_left.mp ab hxA (mem_erase.mp e).2) dis hb
    omega
  refine ⟨existsN,?_⟩
  have sing : Pins p x={i} := by
    refine (eq_of_subset_of_card_le ?_ ?_).symm
    · intro u hu
      exact (mem_singleton.mp hu).symm ▸ hi
    · rw [card_singleton,one]
  have goodF : ∀ u∈F, G.Adj t u := by
    intro u hu
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hu
    rcases mem_union.mp hj with h|h
    · obtain ⟨l,hl,rfl⟩ := mem_image.mp h
      rw [sing] at hl
      have e : l=i := mem_singleton.mp hl
      subst l
      have pos := Graffiti189LongestPath.Rigidity.pin_pos hp hx hi
      have up := (Graffiti189LongestPath.pin_data hi).1
      have e := p.adj_getVert_succ (i:=i-1) (by omega)
      rw [show i-1+1=i by omega] at e
      exact e.symm
    · obtain ⟨l,hl,rfl⟩ := mem_image.mp h
      rw [sing] at hl
      have e : l=i := mem_singleton.mp hl
      subst l
      exact p.adj_getVert_succ (Graffiti189LongestPath.pin_data hi).1
  apply Finset.ext
  intro z
  constructor
  · intro hz
    obtain ⟨zc,ed⟩ := mem_filter.mp hz
    have noB : z∉B := fun h => disjoint_left.mp cb zc h
    have noA : z∉A := fun h => disjoint_left.mp ca zc h
    have xz : x≠z := fun e => noA (e ▸ hxA)
    have nxz : ¬G.Adj x z := fun e => noB
      (Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨noA,x,hxA,e⟩)
    have dd := Graffiti189LongestPath.mem_distanceTwo.mpr
      (Graffiti189LongestPath.dist_two hc xz nxz tx ed)
    have zf : z∈F := rigid ▸ mem_sdiff.mpr ⟨dd,noB⟩
    exact mem_inter.mpr ⟨zc,zf⟩
  · intro hz
    exact mem_filter.mpr ⟨(mem_inter.mp hz).1,goodF z (mem_inter.mp hz).2⟩

/-- Hence three pairwise disjoint nonempty complementary components
are impossible in the far singleton configuration. -/
theorem no_three_complementary_shores (hc : G.Connected) (k : Nat)
    (cap : ∀ v, (EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x∉p.support)
    (one : (Pins p x).card=1) (far : (Shell G x 4).Nonempty)
    {i : Nat} (hi : i∈Pins p x)
    (C : Fin 3 → Finset V)
    (cn : ∀ j, (C j).Nonempty)
    (ca : ∀ j, Disjoint (C j) (OmittedStar p x))
    (cb : ∀ j, Disjoint (C j) (External G (OmittedStar p x)))
    (cd : Pairwise (fun j l => Disjoint (C j) (C l)))
    (closed : ∀ j u, u∈C j → ∀ v∉C j,G.Adj u v → v∈External G (OmittedStar p x)) : False := by
  classical
  have ray (j : Fin 3) : ∃ w∈C j, w∈FlankVertices p x := by
    obtain ⟨no,eq⟩ := pins_meet_complement_in_flanks hc k cap conn hp hx one far hi
      (C j) (cn j) (ca j) (cb j) (closed j)
    rw [eq] at no
    obtain ⟨w,hw⟩ := no
    exact ⟨w,(mem_inter.mp hw).1,(mem_inter.mp hw).2⟩
  obtain ⟨u,uC,uF⟩ := ray 0
  obtain ⟨v,vC,vF⟩ := ray 1
  obtain ⟨w,wC,wF⟩ := ray 2
  have uv : u≠v := fun e => disjoint_left.mp (cd (by decide : (0:Fin 3)≠1)) uC (e.symm ▸ vC)
  have uw : u≠w := fun e => disjoint_left.mp (cd (by decide : (0:Fin 3)≠2)) uC (e.symm ▸ wC)
  have vw : v≠w := fun e => disjoint_left.mp (cd (by decide : (1:Fin 3)≠2)) vC (e.symm ▸ wC)
  have big := two_lt_card.mpr ⟨u,uF,v,vF,w,wF,uv,uw,vw⟩
  have sing : Pins p x={i} := by
    refine (eq_of_subset_of_card_le ?_ ?_).symm
    · intro z hz
      exact (mem_singleton.mp hz).symm ▸ hi
    · rw [card_singleton,one]
  have small : (FlankVertices p x).card≤2 := by
    rw [Graffiti189LongestPath.OneSlack.cardinal_flankVertices hp]
    simp only [FlankIndices,sing,image_singleton]
    exact (card_union_le _ _).trans (by simp)
  omega
#print axioms pins_meet_complement_in_flanks
#print axioms no_three_complementary_shores
end Graffiti189LongestPath.FlankShore
