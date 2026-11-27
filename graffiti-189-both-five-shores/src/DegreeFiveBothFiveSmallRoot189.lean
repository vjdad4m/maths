import DegreeFiveBothFiveRooted189
import RootedTwoUniversal189
import ResidualOre189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private residue residue_count residual_neighbor_bound common_sub_ports
  from DegreeFiveBothFiveResidual189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- A saturated five-port shore of order at most seven has a route
starting at a cut porter even if its common count is only one or two. -/
theorem rooted_port_route_at_small_five_shore
    (degree : ∀ u v : V,u≠v → 5 ≤ G.degree u ∨ 5 ≤ G.degree v)
    {C : Cmp (G:=G) (a:=a) (b:=b)}
    (five : (cutPorts C).card=5) (small : (Shore C).card ≤ 7)
    {x : V} (xk : x∈sharedPortSet C)
    (univ : ∀ u∈sharedPortSet C,∀ w∈Shore C,u≠w → G.Adj u w) :
    ∃ p∈cutPorts C,∃ q,RouteOn G (Shore C) p q := by
  classical
  let K := sharedPortSet C
  let R := residue C
  have xK : x∈K := xk
  have tally : R.card+K.card=(Shore C).card := residue_count C
  have kPos := card_pos.mpr ⟨x,xK⟩
  have off : Disjoint K R := by
    apply disjoint_left.mpr
    intro w wk wr
    exact (mem_sdiff.mp wr).2 wk
  have whole : K∪R=Shore C := union_sdiff_of_subset (show K⊆Shore C from filter_subset _ _)
  have join (u : V) (uk : u∈K) (w : V) (wm : w∈K∪R) (uw : u≠w) : G.Adj u w :=
    univ u uk w (whole ▸ wm) uw
  by_cases big : 3≤K.card
  · have room : (Shore C).card ≤ 2*(sharedPortSet C).card+2 := by
      have q : 3≤(sharedPortSet C).card := big
      omega
    obtain ⟨y,p,_⟩ := rooted_route_at_five_port_shore_with_big_shared degree five big
      (by omega) room xk univ
    exact ⟨x,common_sub_ports C xk,y,p⟩
  by_cases k2 : K.card=2
  · have pair (u : V) (ur : u∈R) (v : V) (vr : v∈R) (uv : u≠v) :
        2≤(R.filter (G.Adj u)).card ∨ 2≤(R.filter (G.Adj v)).card := by
      have p : G.degree u≤K.card+(R.filter (G.Adj u)).card+1 := residual_neighbor_bound ur
      have q : G.degree v≤K.card+(R.filter (G.Adj v)).card+1 := residual_neighbor_bound vr
      exact (degree u v uv).imp (fun h=>by omega) (fun h=>by omega)
    obtain ⟨y,p⟩ := rooted_route_with_two_universal K R k2 (by omega) xk off join pair
    exact ⟨x,common_sub_ports C xk,y,whole ▸ p⟩
  have k1 : K.card=1 := by omega
  have keq : K={x} := (eq_of_subset_of_card_le (singleton_subset_iff.mpr xK)
    (by simp [k1])).symm
  have psub : cutPorts C⊆Shore C := filter_subset _ _
  have lower : 5≤(Shore C).card := by rw [←five]; exact card_le_card psub
  have rpos : R.Nonempty := card_pos.mp (by omega)
  have pair (u : V) (ur : u∈R) (v : V) (vr : v∈R) (uv : u≠v) :
      3≤(R.filter (G.Adj u)).card ∨ 3≤(R.filter (G.Adj v)).card := by
    have p : G.degree u≤K.card+(R.filter (G.Adj u)).card+1 := residual_neighbor_bound ur
    have q : G.degree v≤K.card+(R.filter (G.Adj v)).card+1 := residual_neighbor_bound vr
    exact (degree u v uv).imp (fun h=>by omega) (fun h=>by omega)
  by_cases all : ∀ w∈R,(R.filter (G.Adj w)).card<3 → ∃ v∈R,G.Adj w v
  · obtain ⟨u,ur,v,vr,p⟩ := residual_route_if_low_not_isolated R (by omega) rpos pair all
    have xr : x∉R := fun h=>disjoint_left.mp off xK h
    have xu : G.Adj x u := join x xK u (mem_union_right _ ur) (fun e=>xr (e.symm ▸ ur))
    have eq : insert x R=Shore C := by
      rw [←whole,keq]
      ext w
      simp
    exact ⟨x,common_sub_ports C xk,v,eq ▸ p.prefix xu xr⟩
  push_neg at all
  obtain ⟨z,zr,low,iso⟩ := all
  let Z := R.erase z
  have notsmall : ¬cutPorts C⊆({x,z} : Finset V) := by
    intro sub
    have q := card_le_card sub
    have h := card_insert_le x ({z} : Finset V)
    rw [card_singleton] at h
    omega
  obtain ⟨u,up,un⟩ := not_subset.mp notsmall
  have uz : u≠z := fun e=>un (mem_insert.mpr (.inr (mem_singleton.mpr e)))
  have ux : u≠x := fun e=>un (mem_insert.mpr (.inl e))
  have ur : u∈R := by
    apply mem_sdiff.mpr
    refine ⟨psub up,?_⟩
    change u∉K
    rw [keq]
    exact fun h=>ux (mem_singleton.mp h)
  have uZ : u∈Z := mem_erase.mpr ⟨uz,ur⟩
  have high (w : V) (wZ : w∈Z) : 3≤(Z.filter (G.Adj w)).card := by
    obtain ⟨wz,wr⟩ := mem_erase.mp wZ
    have eq : Z.filter (G.Adj w)=R.filter (G.Adj w) := by
      ext v
      constructor
      · intro h
        obtain ⟨vZ,wv⟩ := mem_filter.mp h
        exact mem_filter.mpr ⟨(mem_erase.mp vZ).2,wv⟩
      intro h
      obtain ⟨vr,wv⟩ := mem_filter.mp h
      have vz : v≠z := fun e=>iso w wr (e ▸ wv.symm)
      exact mem_filter.mpr ⟨mem_erase.mpr ⟨vz,vr⟩,wv⟩
    rw [eq]
    exact (pair z zr w wr wz.symm).resolve_left (by omega)
  have sz : Z.card ≤ 6 := (card_le_card (erase_subset _ _)).trans (by omega)
  obtain ⟨v,vZ,p⟩ := rooted_high_residual_Ore Z sz high uZ
  have vr := (mem_erase.mp vZ).2
  have xr : x∉R := fun h=>disjoint_left.mp off xK h
  have xv : G.Adj x v := join x xK v (mem_union_right _ vr) (fun e=>xr (e.symm ▸ vr))
  have xz : G.Adj x z := join x xK z (mem_union_right _ zr) (fun e=>xr (e.symm ▸ zr))
  have p' := p.suffix xv.symm (fun h=>xr (mem_erase.mp h).2)
  have p'' := p'.suffix xz (fun h=> (mem_insert.mp h).elim
    (fun e=>xr (e ▸ zr)) (fun h=>(mem_erase.mp h).1 rfl))
  have eq : insert z (insert x Z)=Shore C := by
    have rz : insert z Z=R := insert_erase zr
    rw [insert_comm,rz,←whole,keq]
    ext w
    simp
  exact ⟨u,up,z,eq ▸ p''⟩

#print axioms rooted_port_route_at_small_five_shore
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
