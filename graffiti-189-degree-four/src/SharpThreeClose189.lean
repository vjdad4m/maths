import SharpThreeReach189
import MultiPinRotation189
namespace Graffiti189LongestPath.SharpThree.Close
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.DistanceOnly
open Graffiti189LongestPath.SharpThree.Reach Graffiti189LongestPath.OneSlack
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false
section
variable (h : Hyp G)
include h
variable {a b : V} {p : G.Walk a b}

private theorem cross_ex (hp : IsLongest p) (H : OmittedComponent p)
    (_hH : ∀ v, v∈H.vertices ↔ v∉p.support)
    (active : ∀ x ∉ p.support, ∃ s∈PathPins p, G.Adj x s) :
    ∃ x ∉ p.support, ∃ y ∉ p.support, ∃ s∈PathPins p, ∃ t∈PathPins p,
      G.Adj x y ∧ G.Adj x s ∧ G.Adj y t ∧ s≠t := by
  classical
  by_contra no
  obtain ⟨x,hx,y,hy,i,hi,j,hj,ij⟩ := two_porters_of_component h hp H
  let s := p.getVert i
  let t := p.getVert j
  have sx : G.Adj x s := (pin_data hi).2
  have ty : G.Adj y t := (pin_data hj).2
  have sp : s∈PathPins p := mem_pathPins.mpr ⟨p.getVert_mem_support i,x,H.off x hx,sx⟩
  have tp : t∈PathPins p := mem_pathPins.mpr ⟨p.getVert_mem_support j,y,H.off y hy,ty⟩
  obtain ⟨q,_,hq⟩ := H.joined x hx y hy
  have propagate {u v : V} (q : G.Walk u v) (hq : ∀ w∈q.support,w∉p.support)
      (adj : G.Adj u s) : G.Adj v s := by
    induction q with
    | nil => exact adj
    | @cons u w v e q ih =>
      apply ih (fun z hz => hq z (by simp [hz]))
      obtain ⟨r,rp,wr⟩ := active w (hq w (by simp))
      by_cases sr : s=r
      · rwa [sr]
      · exact (no ⟨u,hq u (by simp),w,hq w (by simp),s,sp,r,rp,e,adj,wr,sr⟩).elim
  have ys := propagate q (fun v hv => H.off v (hq v hv)) sx
  have eq := unique_path_neighbor h hp (H.off y hy) (mem_pathPins.mp sp).1 (mem_pathPins.mp tp).1 ys ty
  exact ij (hp.1.getVert_injOn (pin_data hi).1.le (pin_data hj).1.le eq)

private theorem cross_makes_universal (hp : IsLongest p) (H : OmittedComponent p)
    (hH : ∀ v, v∈H.vertices ↔ v∉p.support)
    {x y s t : V} (xo : x∉p.support) (yo : y∉p.support) (sp : s∈p.support) (tp : t∈p.support)
    (xy : G.Adj x y) (xs : G.Adj x s) (yt : G.Adj y t) (st : s≠t) :
    ∀ z∉p.support, z=x ∨ G.Adj x z := by
  have xt : ¬G.Adj x t := fun e => st (unique_path_neighbor h hp xo sp tp xs e)
  have dt := dist_two h.con (show x≠t from fun e => xo (e.symm ▸ tp)) xt xy yt
  obtain ⟨i,hi,si⟩ := pin_of_neighbor_mem hp xo sp xs
  obtain ⟨j,hj,tj⟩ := pin_of_neighbor_mem hp yo tp yt
  have ij : i≠j := fun e => st (si.symm.trans ((congrArg p.getVert e).trans tj))
  have tf := pin_not_other_flank h hp H ((hH x).mpr xo) ((hH y).mpr yo) hi hj ij
  rw [tj] at tf
  intro z zo
  obtain ⟨q,_,hq⟩ := H.joined x ((hH x).mpr xo) z ((hH z).mpr zo)
  have propagate {u v : V} (q : G.Walk u v) (hq : ∀ w∈q.support,w∉p.support)
      (adj : u=x ∨ G.Adj x u) : v=x ∨ G.Adj x v := by
    induction q with
    | nil => exact adj
    | @cons u w v e q ih =>
      apply ih (fun z hz => hq z (by simp [hz]))
      rcases adj with rfl|adj
      · exact Or.inr e
      by_cases wx : w=x
      · exact Or.inl wx
      by_cases aw : G.Adj x w
      · exact Or.inr aw
      have dw := dist_two h.con (Ne.symm wx) aw adj e
      have wo := hq w (by simp)
      have wf : w∉Flanks p i := by
        simpa [Flanks] using And.intro
          (fun e : w=p.getVert (i-1) => wo (e.symm ▸ p.getVert_mem_support _))
          (fun e : w=p.getVert (i+1) => wo (e.symm ▸ p.getVert_mem_support _))
      have eq := third_unique h hp xo hi dw dt wf tf
      exact (wo (eq.symm ▸ tp)).elim
  exact propagate q (fun v hv => H.off v (hq v hv)) (Or.inl rfl)

private theorem pin_two (hp : IsLongest p) (ha : 4≤G.degree a) (hb : 4≤G.degree b)
    (H : OmittedComponent p) (hH : ∀ v, v∈H.vertices ↔ v∉p.support)
    {x s : V} (xo : x∉p.support) (sp : s∈p.support) (xs : G.Adj x s) :
    2 ≤ ((DistanceTwo G s).filter (·∈p.support)).card := by
  obtain ⟨i,hi,rfl⟩ := pin_of_neighbor_mem hp xo sp xs
  apply pin_has_two_on_path_general_of_d2 h.con 2 h.d2 h.conn
    (fun u v uv => (h.degree u v uv).imp (by omega) (by omega)) hp (by omega) (by omega) xo hi
  intro j jl edge
  rcases chord_lifts_or_flank h hp xo (p.getVert_mem_support j) hi edge with fl|⟨u,uo,xu,uj⟩
  · simp only [Flanks,mem_insert,mem_singleton] at fl
    have il := (pin_data hi).1
    rcases fl with f|f
    · exact Or.inl (hp.1.getVert_injOn jl (show i-1≤p.length by omega) f)
    · exact Or.inr (Or.inl (hp.1.getVert_injOn jl (show i+1≤p.length by omega) f))
  · have jlt : j<p.length := by
      apply Nat.lt_of_le_of_ne jl
      intro eq
      have e := no_endpoints hp uo
      rw [eq,getVert_length] at uj
      exact e.2 uj
    have hj : j∈Pins p u := mem_filter.mpr ⟨mem_range.mpr jlt,uj⟩
    have ij : i≠j := fun eq => edge.ne (congrArg p.getVert eq)
    apply Or.inr
    apply Or.inr
    refine ⟨u,uo,hj,?_⟩
    rcases lt_or_gt_of_ne ij with lt|gt
    · exact Or.inl (pin_gap_of_component h hp H ((hH x).mpr xo) ((hH u).mpr uo) hi hj lt)
    · exact Or.inr (pin_gap_of_component h hp H ((hH u).mpr uo) ((hH x).mpr xo) hj hi gt)


private theorem at_most_one_miss (hp : IsLongest p) (ha : 4≤G.degree a) (hb : 4≤G.degree b)
    (H : OmittedComponent p) (hH : ∀ v, v∈H.vertices ↔ v∉p.support)
    {x s : V} (xo : x∉p.support) (sp : s∈p.support) (xs : G.Adj x s)
    (univ : ∀ z∉p.support, z=x ∨ G.Adj x z)
    {u v : V} (uo : u∉p.support) (vo : v∉p.support)
    (us : ¬G.Adj u s) (vs : ¬G.Adj v s) : u=v := by
  let D := DistanceTwo G s
  let A := D.filter (·∈p.support)
  let B := D.filter (·∉p.support)
  have eq : A.card+B.card=D.card := filter_card_add_filter_neg_card_eq_card _
  have ge : 2≤A.card := pin_two h hp ha hb H hH xo sp xs
  have le : D.card≤3 := h.d2 s
  have cap : B.card≤1 := by omega
  have mem {z : V} (zo : z∉p.support) (zs : ¬G.Adj z s) : z∈B := by
    have zx : z≠x := fun e => zs (e.symm ▸ xs)
    have xz := (univ z zo).resolve_left zx
    have sd := dist_two h.con (show s≠z from fun e => zo (e ▸ sp)) (fun e => zs e.symm) xs.symm xz
    exact mem_filter.mpr ⟨mem_distanceTwo.mpr sd,zo⟩
  exact card_le_one.mp cap u (mem uo us) v (mem vo vs)

private theorem no_longest_omits (hp : IsLongest p) (ha : 4≤G.degree a) (hb : 4≤G.degree b)
    {z : V} (zo : z∉p.support) : False := by
  obtain ⟨H,hH⟩ := actual_omitted_component h hp zo
  obtain ⟨x,xo,y,yo,s,sP,t,tP,xy,xs,yt,st⟩ :=
    cross_ex h hp H hH (fun w wo => all_omitted_active h hp ha hb H hH wo)
  have sp := (mem_pathPins.mp sP).1
  have tp := (mem_pathPins.mp tP).1
  have xu := cross_makes_universal h hp H hH xo yo sp tp xy xs yt st
  have yu := cross_makes_universal h hp H hH yo xo tp sp xy.symm yt xs st.symm
  have ys : ¬G.Adj y s := fun e => st (unique_path_neighbor h hp yo sp tp e yt)
  have xt : ¬G.Adj x t := fun e => st (unique_path_neighbor h hp xo sp tp xs e)
  have off (w : V) (wo : w∉p.support) : w=x ∨ w=y := by
    by_cases ws : G.Adj w s
    · have wt : ¬G.Adj w t := fun e => st (unique_path_neighbor h hp wo sp tp ws e)
      exact Or.inl (at_most_one_miss h hp ha hb H hH yo tp yt yu wo xo wt xt)
    · exact Or.inr (at_most_one_miss h hp ha hb H hH xo sp xs xu wo yo ws ys)
  have deg {u v r : V} (uo : u∉p.support) (rp : r∈p.support)
      (ur : G.Adj u r) (only : ∀ w∉p.support, w=u ∨ w=v) : G.degree u≤2 := by
    have sub : G.neighborFinset u ⊆ {v,r} := by
      intro w hw
      have uw : G.Adj u w := (mem_neighborFinset G u w).mp hw
      by_cases wp : w∈p.support
      · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (unique_path_neighbor h hp uo wp rp uw ur)))
      · exact mem_insert.mpr (Or.inl ((only w wp).resolve_left uw.ne.symm))
    have ls := card_le_card sub
    have ins := card_insert_le v ({r} : Finset V)
    rw [card_neighborFinset_eq_degree] at ls
    simp only [card_singleton] at ins
    omega
  have dx := deg xo sp xs off
  have dy := deg yo tp yt (fun w wo => (off w wo).symm)
  exact (h.degree x y xy.ne).elim (by omega) (by omega)

end

/-- Graffiti.pc #189 under the distance-two cap three, at degree threshold four. -/
theorem traceable_of_distanceTwo_three_degree_four
    (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card≤5)
    (d2 : ∀ x, (DistanceTwo G x).card≤3)
    (conn : ∀ S : Finset V, S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u≠v → 4≤G.degree u ∨ 4≤G.degree v) :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ ∀ v, v∈p.support := by
  classical
  have gdegree (u v : V) (ne : u≠v) : 2+1 ≤ G.degree u ∨ 2+1 ≤ G.degree v :=
    (degree u v ne).imp (by omega) (by omega)
  let hp : Hyp G :=
    ⟨hc,even,d2,conn,degree,
      fun hp hx => unique_omitted_pin_at_near_connectivity_of_d2 hc 2 d2 conn gdegree hp hx,
      fun hp hx _ hi => rigid_flanks_of_d2 hc 2 d2 conn gdegree hp hx hi,
      fun hp hx _ hi => start_not_adj_pin_of_two_le_of_d2 hc 2 d2 conn gdegree hp hx hi,
      fun hp hx _ hi => end_not_adj_pin_of_two_le_of_d2 hc 2 d2 conn gdegree hp hx hi⟩
  by_contra fail
  obtain ⟨a,b,p,long⟩ := exists_longest hc
  obtain ⟨z,zo⟩ : ∃ z, z∉p.support := not_forall.mp (fun all => fail ⟨a,b,p,long.1,all⟩)
  obtain ⟨u,v,q,hq,eq,hu,hv⟩ := MultiRotation.rotate_to_two_high_endpoints_general
    hc 2 (by omega) 4 conn degree long zo
  exact no_longest_omits hp hq hu hv ((eq z).not.mp zo)

#print axioms traceable_of_distanceTwo_three_degree_four


/-- Graffiti.pc #189 for second-smallest degree four, connectivity at
least two, and radius at least four. -/
theorem traceable_of_radius_four_degree_four
    (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card≤5)
    (radius : ∀ x, ∃ y, 4≤G.dist x y)
    (conn : ∀ S : Finset V, S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u≠v → 4≤G.degree u ∨ 4≤G.degree v) :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ ∀ v, v∈p.support := by
  apply traceable_of_distanceTwo_three_degree_four hc even _ conn degree
  intro x
  obtain ⟨y,hy⟩ := radius x
  have big := distanceTwo_add_two_le_even_of_far hc hy
  have cap := even x
  omega

#print axioms traceable_of_radius_four_degree_four
end Graffiti189LongestPath.SharpThree.Close
