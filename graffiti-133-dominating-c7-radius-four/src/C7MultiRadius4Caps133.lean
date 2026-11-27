import C7MultiSmallScopes133
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace Graffiti133MultiC7
open SimpleGraph Finset Graffiti133 Graffiti133NoFive
open scoped Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem radius_at (v : V) (k : ℕ) (h : ∀ w,G.dist v w≤k) :
    radius G ≤ k := by
  classical
  unfold radius
  have hm : Finset.univ.sup (G.dist v) ∈ Finset.univ.image (fun u => Finset.univ.sup (G.dist u)) :=
    Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
  have hl := Finset.min_le hm
  cases e : (Finset.univ.image (fun u => Finset.univ.sup (G.dist u))).min with
  | top => exact Nat.zero_le _
  | coe d =>
    have hu : d≤Finset.univ.sup (G.dist v) := by simpa [e] using hl
    exact hu.trans (Finset.sup_le_iff.mpr (fun w _=>h w))

private theorem adjacent_pair_dist (hc : G.Connected) {x y z : V}
    (xy : G.Adj x y) (yz : G.Adj y z) : G.dist x z≤2 := by
  have d : G.dist x z≤G.dist x y+G.dist y z := hc.dist_triangle
  rw [dist_eq_one_iff_adj.mpr xy,dist_eq_one_iff_adj.mpr yz] at d
  exact d

theorem two_far_shortcuts_imply_radius_three (H : Hole G 7) (hc : G.Connected)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i))
    (i : Fin 7) (near : ∀ j,farSites i j→∃ x,G.Adj (H.c i) x ∧ G.Adj x (H.c j)) :
    radius G≤3 := by
  have cycle (j : Fin 7) : G.dist (H.c i) (H.c j)≤2 := by
    by_cases eq : i=j
    · subst j
      rw [SimpleGraph.dist_self]
      decide
    by_cases adj : Cyclic i j
    · rw [dist_eq_one_iff_adj.mpr ((H.adj i j).mpr adj)]
      decide
    by_cases mixed : ∃ k,Cyclic i k ∧ Cyclic j k
    · obtain ⟨k,ik,jk⟩ := mixed
      exact adjacent_pair_dist hc ((H.adj i k).mpr ik) (((H.adj j k).mpr jk).symm)
    · obtain ⟨x,ix,xj⟩ := near j ⟨eq,adj,mixed⟩
      exact adjacent_pair_dist hc ix xj
  apply radius_at (H.c i) 3
  intro x
  by_cases out : Outside H.c x
  · obtain ⟨j,xj⟩ := dom x out
    have e : G.dist (H.c j) x=1 := dist_eq_one_iff_adj.mpr xj.symm
    have d : G.dist (H.c i) x≤G.dist (H.c i) (H.c j)+G.dist (H.c j) x := hc.dist_triangle
    have := cycle j
    omega
  · unfold Outside at out
    push_neg at out
    obtain ⟨j,eq⟩ := out
    subst x
    exact (cycle j).trans (by decide)

theorem triple_contact_implies_radius_three
    (H : Hole G 7) (hc : G.Connected) (h4 : FourCycleFree G)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i))
    (x : V) (out : Outside H.c x) (three : (contactSet H x).card=3) : radius G≤3 := by
  obtain ⟨i,hit,center⟩ := geometry_triple_center _ (contacts_are_allowed H h4 x out) three
  apply two_far_shortcuts_imply_radius_three H hc dom i
  intro j far
  exact ⟨x,((mem_contactSet H x i).mp hit).symm,(mem_contactSet H x j).mp (center j far)⟩

theorem geometry_far_two : ∀ i : Fin 7, ((Finset.univ : Finset (Fin 7)).filter (farSites i)).card=2 := by decide

theorem radius_four_far_matching_at_site
    (H : Hole G 7) (hc : G.Connected)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i))
    (r : 4≤radius G) (i j k : Fin 7) (hj : farSites i j) (hk : farSites i k)
    (xy : ∃ x,G.Adj (H.c i) x ∧ G.Adj x (H.c j))
    (xz : ∃ y,G.Adj (H.c i) y ∧ G.Adj y (H.c k)) : j=k := by
  by_contra ne
  let F := (Finset.univ : Finset (Fin 7)).filter (farSites i)
  have sub : ({j,k} : Finset (Fin 7))⊆F := by
    intro y hy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl|rfl <;> simp [F, *]
  have eq : ({j,k}:Finset (Fin 7))=F :=
    Finset.eq_of_subset_of_card_le sub (by rw [show F.card=2 from geometry_far_two i]; simp [ne])
  have all (a : Fin 7) (h : farSites i a) : ∃ y,G.Adj (H.c i) y ∧ G.Adj y (H.c a) := by
    have e : a∈F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
    rw [←eq] at e
    simp only [Finset.mem_insert,Finset.mem_singleton] at e
    rcases e with rfl|rfl
    · exact xy
    · exact xz
  have d := two_far_shortcuts_imply_radius_three H hc dom i all
  omega

#print axioms triple_contact_implies_radius_three
#print axioms radius_four_far_matching_at_site
end Graffiti133MultiC7


namespace Graffiti133MultiC7
open SimpleGraph Finset Graffiti133 Graffiti133NoFive
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem saturated_clean_sites_force_radius_three (H : Hole G 7) (hc : G.Connected)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i))
    (x : V)
    (touch : ∀ i∈cleanSites (contactSet H x),∃ y,G.Adj x y ∧ G.Adj y (H.c i)) :
    radius G≤3 := by
  classical
  have around (i : Fin 7) : G.dist x (H.c i)≤2 := by
    by_cases hit : i∈contactSet H x
    · rw [dist_eq_one_iff_adj.mpr ((mem_contactSet H x i).mp hit)]
      decide
    by_cases clean : i∈cleanSites (contactSet H x)
    · obtain ⟨y,xy,yi⟩ := touch i clean
      exact adjacent_pair_dist hc xy yi
    · have j : ∃ j∈contactSet H x,Cyclic i j := by
        by_contra! none
        exact clean (Finset.mem_filter.mpr ⟨Finset.mem_univ _,none⟩)
      obtain ⟨j,jm,ij⟩ := j
      exact adjacent_pair_dist hc ((mem_contactSet H x j).mp jm) (((H.adj i j).mpr ij).symm)
  apply radius_at x 3
  intro z
  by_cases out : Outside H.c z
  · obtain ⟨i,e⟩ := dom z out
    have t := hc.dist_triangle (u:=x) (v:=H.c i) (w:=z)
    rw [dist_eq_one_iff_adj.mpr e.symm] at t
    have := around i
    omega
  · unfold Outside at out
    push_neg at out
    obtain ⟨i,e⟩ := out
    rw [e]
    exact (around i).trans (by decide)

theorem saturated_exterior_degree_implies_radius_three
    (H : Hole G 7) (hc : G.Connected) (h4 : FourCycleFree G)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i))
    (x : V) (off : Outside H.c x)
    (full : (cleanSites (contactSet H x)).card≤(exteriorNeighbors H x).card) : radius G≤3 := by
  classical
  let E := exteriorNeighbors H x
  let A := cleanSites (contactSet H x)
  have prop (y : V) (ym : y∈E) : Outside H.c y ∧ G.Adj x y := (Finset.mem_filter.mp ym).2
  choose tag ed using (fun y : {y // y∈E}=>dom y.val (prop y.val y.property).1)
  let f (y : V) := if ym : y∈E then tag ⟨y,ym⟩ else 0
  have ev (y : V) (ym : y∈E) : f y=tag ⟨y,ym⟩ := dif_pos ym
  have inj : Set.InjOn f (E : Set V) := by
    intro y ym z zm eq
    change y∈E at ym
    change z∈E at zm
    rw [ev y ym,ev z zm] at eq
    exact h4 x (H.c (tag ⟨y,ym⟩)) y z (off _) (prop y ym).2 (ed ⟨y,ym⟩).symm
      (prop z zm).2 (by rw [eq]; exact (ed ⟨z,zm⟩).symm)
  have sub : E.image f⊆A := by
    intro i im
    obtain ⟨y,ym,rfl⟩ := Finset.mem_image.mp im
    rw [ev y ym]
    exact neighbor_sites_clean H h4 off (prop y ym).1 (prop y ym).2 _ (ed ⟨y,ym⟩)
  have eq : E.image f=A := by
    apply Finset.eq_of_subset_of_card_le sub
    rw [Finset.card_image_of_injOn inj]
    exact full
  apply saturated_clean_sites_force_radius_three H hc dom x
  intro i im
  change i∈A at im
  rw [←eq] at im
  obtain ⟨y,ym,my⟩ := Finset.mem_image.mp im
  exact ⟨y,(prop y ym).2,by rw [←my,ev y ym]; exact ed ⟨y,ym⟩⟩

theorem radius_four_multi_degree_caps
    (H : Hole G 7) (hc : G.Connected) (h4 : FourCycleFree G)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i)) (hr : 4≤radius G)
    (x : V) (xm : x∈multiVertices H) :
    (contactSet H x).card=2 ∧ (exteriorNeighbors H x).card≤2 := by
  have m := (Finset.mem_filter.mp xm).2
  rcases geometry_cap _ (contacts_are_allowed H h4 x m.1) m.2 with ⟨a,b⟩|⟨a,b⟩
  · refine ⟨a,?_⟩
    by_contra! too
    have full : (cleanSites (contactSet H x)).card≤(exteriorNeighbors H x).card := by omega
    have d := saturated_exterior_degree_implies_radius_three H hc h4 dom x m.1 full
    omega
  · have d := triple_contact_implies_radius_three H hc h4 dom x m.1 a
    omega

def adjacentPairs (A : Finset (Fin 7)) : Finset (Finset (Fin 7)) :=
  (A.powersetCard 2).filter (fun T => ∃ i∈T,∃ j∈T,Cyclic i j)

theorem adjacent_pair_resource : (adjacentPairs (Finset.univ : Finset (Fin 7))).card=7 := by decide

noncomputable def adjacentMulti (H : Hole G 7) : Finset V :=
  (multiVertices H).filter (fun x=>∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j)

noncomputable def farMulti (H : Hole G 7) : Finset V :=
  (multiVertices H).filter (fun x=>¬∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j)

theorem radius_four_pair_profile_counts
    (H : Hole G 7) (hc : G.Connected) (h4 : FourCycleFree G)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i)) (hr : 4≤radius G) :
    (adjacentMulti H).card≤7 ∧ (farMulti H).card≤3 := by
  classical
  have sz (x : V) (m : x∈multiVertices H) : (contactSet H x).card=2 :=
    (radius_four_multi_degree_caps H hc h4 dom hr x m).1
  constructor
  · rw [←adjacent_pair_resource]
    apply Finset.card_le_card_of_injOn (contactSet H)
    · intro x xm
      obtain ⟨xd,adj⟩ := Finset.mem_filter.mp xm
      exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,sz x xd⟩,adj⟩
    · intro x xm y ym eq
      by_contra ne
      have cap := disjoint_contact_pairs H h4 ne
      rw [eq,Finset.inter_self,sz y (Finset.mem_filter.mp ym).1] at cap
      omega
  · let F := farMulti H
    have dis : Set.PairwiseDisjoint (F : Set V) (contactSet H) := by
      intro x xm y ym ne
      apply Finset.disjoint_left.mpr
      intro i ix iy
      obtain ⟨xa,xno⟩ := Finset.mem_filter.mp xm
      obtain ⟨ya,yno⟩ := Finset.mem_filter.mp ym
      obtain ⟨j,jx,jne⟩ := Finset.exists_ne_of_one_lt_card (show 1<(contactSet H x).card by rw [sz x xa]; decide) i
      obtain ⟨k,ky,kne⟩ := Finset.exists_ne_of_one_lt_card (show 1<(contactSet H y).card by rw [sz y ya]; decide) i
      have ax := (Finset.mem_filter.mp xa).2.1
      have ay := (Finset.mem_filter.mp ya).2.1
      have fj : farSites i j := ⟨jne.symm,fun hh=>xno ⟨i,ix,j,jx,hh⟩,
        contacts_are_allowed H h4 x ax i ix j jx jne.symm⟩
      have fk : farSites i k := ⟨kne.symm,fun hh=>yno ⟨i,iy,k,ky,hh⟩,
        contacts_are_allowed H h4 y ay i iy k ky kne.symm⟩
      have eq := radius_four_far_matching_at_site H hc dom hr i j k fj fk
        ⟨x,((mem_contactSet H x i).mp ix).symm,(mem_contactSet H x j).mp jx⟩
        ⟨y,((mem_contactSet H y i).mp iy).symm,(mem_contactSet H y k).mp ky⟩
      have common := h4 x y (H.c i) (H.c j) ne
        ((mem_contactSet H x i).mp ix) ((mem_contactSet H y i).mp iy)
        ((mem_contactSet H x j).mp jx) ((mem_contactSet H y j).mp (eq.symm ▸ ky))
      exact jne (H.inj common).symm
    have total : (F.biUnion (contactSet H)).card=2*F.card := by
      calc
        _ = ∑ x∈F,(contactSet H x).card := Finset.card_biUnion dis
        _ = ∑ x∈F,(2:Nat) := Finset.sum_congr rfl (fun x xm=>sz x (Finset.mem_filter.mp xm).1)
        _ = _ := by simp [Nat.mul_comm]
    have cap := Finset.card_le_univ (F.biUnion (contactSet H))
    rw [total] at cap
    have seven : Fintype.card (Fin 7)=7 := by simp
    change F.card≤3
    omega

#print axioms radius_four_multi_degree_caps
#print axioms radius_four_pair_profile_counts
end Graffiti133MultiC7
