import SingleStar189
import ExactStarShore189
import TwoShoreDefect189
import MultiPinRotation189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.ActiveStarHeight
open Graffiti189LongestPath.TruncatedHall Graffiti189LongestPath.ForeignPorts
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.no_endpoints Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two
  Graffiti189LongestPath.distance_on_geodesic from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.mem_omittedStar Graffiti189LongestPath.Rigidity.mem_external
  Graffiti189LongestPath.Rigidity.pin_pos from Rigidity189
open private Graffiti189LongestPath.OneSlack.cardinal_flankVertices Graffiti189LongestPath.OneSlack.card_pinVertices
  Graffiti189LongestPath.OneSlack.first_eq_if_no_pair Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary
    Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem from OneSlack189
open private Graffiti189LongestPath.OneSlack.MultiRotation.rigidity_of_tight from MultiPinRotation189
set_option warningAsError true
set_option maxHeartbeats 4000000
namespace Graffiti189LongestPath.SingleFourthBudget
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The exact-cut single-pin star spends its missing distance-two slots
at either the unique pin or a non-pin gateway. -/
theorem single_star_order_upper_radius_four (hc : G.Connected) (k : Nat) (hk : 6≤k)
    (cap : ∀ v, (EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x∉p.support)
    (high : k+2≤G.degree x) (one : (Pins p x).card=1)
    (bk : (External G (OmittedStar p x)).card=k) (rad : ∀ z,G.dist x z≤4) :
    Fintype.card V≤(OmittedStar p x).card+k+k*(k+2) := by
  classical
  let d := k+2
  let A := OmittedStar p x
  let B := External G A
  let F := DistanceTwo G x \ B
  let C := B\PinVertices p x
  let H := Shell G x 3
  let W := Shell G x 4
  have cap₂ (u : V) : (DistanceTwo G u).card≤d := distanceTwo_le_of_even d u (cap u)
  have budget := SingleStar.singleton_star_budget hc k conn hp hx one (cap x)
  change k≤B.card ∧ B.card≤k+1 ∧ 2≤F.card ∧
    B.card+F.card+(Shell G x 4).card≤k+3 ∧ _ at budget
  change B.card=k at bk
  have fs : F.card+W.card≤3 := by have h := budget.2.2.2.1; change B.card+F.card+W.card≤k+3 at h; omega
  have fl : 2≤F.card := budget.2.2.1
  have cs : C.card+1=k := by
    have e := card_sdiff_add_card_eq_card (Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary hx)
    rw [Graffiti189LongestPath.OneSlack.card_pinVertices hp,one] at e
    change C.card+1=B.card at e
    omega
  have xs := star_card_degree_and_pins hp hx
  change A.card+(Pins p x).card=G.degree x+1 at xs
  have xa : x∈A := Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have ab : Disjoint A B := disjoint_left.mpr (fun _ h h' =>
    (Graffiti189LongestPath.Rigidity.mem_external.mp h').1 h)
  have acl : ∀ u∈A,∀ v∉A,G.Adj u v → v∈B := fun _ ha _ hn e =>
    Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨hn,_,ha,e⟩
  have twoA {u : V} (hu : u∈A) : G.dist x u≤1 := by
    rcases (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp hu).2 with h|h
    · rw [h,dist_self]; omega
    · have e := dist_eq_one_iff_adj.mpr h; omega
  have noAH {u z : V} (hu : u∈A) (hz : z∈H) : ¬G.Adj u z := by
    intro e
    have st := dist_eq_one_iff_adj.mpr e
    have tr := hc.dist_triangle (u:=x) (v:=u) (w:=z)
    have hz := mem_shell.mp hz
    have hu := twoA hu
    omega
  have neAH {u z : V} (hu : u∈A) (hz : z∈H) : u≠z := by
    intro e
    have hu := twoA hu
    have hz := mem_shell.mp hz
    rw [e] at hu
    omega
  have block (v : V) (vc : v∈C) : (H.filter (G.Adj v)).card≤d := by
    obtain ⟨_,u,ua,uv⟩ := Graffiti189LongestPath.Rigidity.mem_external.mp (mem_sdiff.mp vc).1
    have sub : H.filter (G.Adj v)⊆DistanceTwo G u := by
      intro z hz
      obtain ⟨zh,vz⟩ := mem_filter.mp hz
      exact Graffiti189LongestPath.mem_distanceTwo.mpr
        (Graffiti189LongestPath.dist_two hc (neAH ua zh) (noAH ua zh) uv vz)
    exact (card_le_card sub).trans (cap₂ u)
  obtain ⟨i,hi⟩ := card_pos.mp (by omega : 0<(Pins p x).card)
  have pair : Pins p x={i} :=
    (eq_of_subset_of_card_le (singleton_subset_iff.mpr hi) (by simp [one])).symm
  let t := p.getVert i
  let T := A.filter (fun z => ¬G.Adj t z)
  let Y := H∩DistanceTwo G t
  have tx : G.Adj x t := (Graffiti189LongestPath.pin_data hi).2
  have miss (v : V) (vp : v∈p.support) (vx : G.Adj x v) :
      A.filter (fun z => ¬G.Adj v z)⊆DistanceTwo G v := by
    intro u hu
    obtain ⟨ua,ed⟩ := mem_filter.mp hu
    obtain ⟨off,eq|xu⟩ := Graffiti189LongestPath.Rigidity.mem_omittedStar.mp ua
    · exact (ed (eq.symm ▸ vx.symm)).elim
    · exact Graffiti189LongestPath.mem_distanceTwo.mpr
        (Graffiti189LongestPath.dist_two hc (fun e => off (e ▸ vp)) ed vx.symm xu)
  have charge (v : V) (vp : v∈p.support) (vx : G.Adj x v) :
      (A.filter (fun z => ¬G.Adj v z)).card+(H∩DistanceTwo G v).card≤d := by
    have dis : Disjoint (A.filter (fun z => ¬G.Adj v z)) (H∩DistanceTwo G v) :=
      disjoint_left.mpr (fun _ m h => neAH (mem_filter.mp m).1 (mem_inter.mp h).1 rfl)
    have c := card_le_card (union_subset (miss v vp vx) (inter_subset_right : H∩DistanceTwo G v⊆_))
    rw [card_union_of_disjoint dis] at c
    exact c.trans (cap₂ _)
  have ty : T.card+Y.card≤d := charge t (p.getVert_mem_support i) tx
  have fromFlank (f : V) (ff : f∈F) : G.Adj t f := by
    have df := Graffiti189LongestPath.mem_distanceTwo.mp (mem_sdiff.mp ff).1
    obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist x f
    have len := ql.trans df
    let v := q.getVert 1
    have xv : G.Adj x v := by simpa [v] using q.adj_getVert_succ (i:=0) (by omega)
    have vf : G.Adj v f := by
      have e := q.adj_getVert_succ (i:=1) (by omega : 1<q.length)
      rwa [show q.getVert 2=f by rw [←len,getVert_length]] at e
    have vp : v∈p.support := by
      by_contra nv
      have va : v∈A := Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨nv,Or.inr xv⟩
      have fa : f∉A := fun h => by have hh := twoA h; omega
      exact (mem_sdiff.mp ff).2 (acl v va f fa vf)
    obtain ⟨j,hj,eq⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp hx vp xv
    have ji : j=i := by simpa [pair] using hj
    rw [ji] at eq
    change G.Adj (p.getVert i) f
    rw [eq]
    exact vf
  let E := C.biUnion (fun v => H.filter (G.Adj v))
  have hcov : H⊆E∪Y := by
    intro z hz
    have dz := mem_shell.mp hz
    obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist x z
    have len := ql.trans dz
    let u := q.getVert 2
    have du : G.dist x u=2 := Graffiti189LongestPath.distance_on_geodesic hc q ql 2 (by omega)
    have uz : G.Adj u z := by
      have e := q.adj_getVert_succ (i:=2) (by omega : 2<q.length)
      rwa [show q.getVert 3=z by rw [←len,getVert_length]] at e
    by_cases ub : u∈B
    · have no : u∉PinVertices p x := by
        intro h
        obtain ⟨l,hl,eq⟩ := mem_image.mp h
        have ed : G.Adj x u := eq ▸ (Graffiti189LongestPath.pin_data hl).2
        have e := dist_eq_one_iff_adj.mpr ed
        omega
      exact mem_union.mpr (Or.inl (mem_biUnion.mpr
        ⟨u,mem_sdiff.mpr ⟨ub,no⟩,mem_filter.mpr ⟨hz,uz⟩⟩))
    have uf : u∈F := mem_sdiff.mpr ⟨Graffiti189LongestPath.mem_distanceTwo.mpr du,ub⟩
    have give (v : V) (xv : G.Adj x v) (vu : G.Adj v u) : z∈DistanceTwo G v := by
      have vx := dist_eq_one_iff_adj.mpr xv
      have ne : v≠z := fun r => by rw [r] at vx; omega
      have no : ¬G.Adj v z := by
        intro ed
        have vz := dist_eq_one_iff_adj.mpr ed
        have tri := hc.dist_triangle (u:=x) (v:=v) (w:=z)
        omega
      exact Graffiti189LongestPath.mem_distanceTwo.mpr (Graffiti189LongestPath.dist_two hc ne no vu uz)
    exact mem_union.mpr (Or.inr (mem_inter.mpr ⟨hz,give t tx (fromFlank u uf)⟩))
  have eb : E.card≤C.card*d := card_biUnion_le_card_mul C _ d block
  have stronger : E.card+F.card+W.card≤C.card*d ∨ T.card≥F.card+W.card := by
    by_cases ts : F.card+W.card≤T.card
    · exact Or.inr ts
    left
    have pick (D : Finset V) (dc : D⊆C) (dg : 3≤D.card) :
        ∃ v∈D,∃ u∈A,G.Adj v u ∧ G.Adj t u := by
      have mm := truncated_hall k A B D conn ab bk (dc.trans sdiff_subset)
        (fun h => (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp h).1 p.start_mem_support)
        (by
          intro h
          obtain ⟨_,u,ua,ed⟩ := Graffiti189LongestPath.Rigidity.mem_external.mp h
          exact (Graffiti189LongestPath.no_endpoints hp
            ((Graffiti189LongestPath.Rigidity.mem_omittedStar.mp ua).1)).1 ed) acl
      have cs' := card_le_card dc
      rw [min_eq_right (by omega : D.card≤A.card)] at mm
      apply Classical.byContradiction
      intro bad
      have su : shoreNeighbors G A D⊆T := by
        intro u hu
        obtain ⟨ua,v,vc,vu⟩ := mem_filter.mp hu
        exact mem_filter.mpr ⟨ua,fun e => bad ⟨v,vc,u,ua,vu,e⟩⟩
      have q := card_le_card su
      omega
    have better (v u : V) (ua : u∈A) (vu : G.Adj v u) (tu : G.Adj t u) :
        F.card+(H.filter (G.Adj v)).card≤d := by
      have F₂ : F⊆DistanceTwo G u := by
        intro f hf
        have fno := (mem_sdiff.mp hf).2
        have fd := Graffiti189LongestPath.mem_distanceTwo.mp (mem_sdiff.mp hf).1
        have far : f∉A := fun h => by have hh := twoA h; omega
        have ne : u≠f := fun h => far (h ▸ ua)
        have no : ¬G.Adj u f := fun e => fno
          (Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨far,u,ua,e⟩)
        exact Graffiti189LongestPath.mem_distanceTwo.mpr
          (Graffiti189LongestPath.dist_two hc ne no tu.symm (fromFlank f hf))
      have sub : H.filter (G.Adj v)⊆DistanceTwo G u := by
        intro z hz
        obtain ⟨zh,vz⟩ := mem_filter.mp hz
        exact Graffiti189LongestPath.mem_distanceTwo.mpr
          (Graffiti189LongestPath.dist_two hc (neAH ua zh) (noAH ua zh) vu.symm vz)
      have dj : Disjoint F (H.filter (G.Adj v)) := disjoint_left.mpr (by
        intro z f h
        have a := Graffiti189LongestPath.mem_distanceTwo.mp
          (mem_sdiff.mp f).1
        have b := mem_shell.mp (mem_filter.mp h).1
        omega)
      have improved := card_le_card (union_subset F₂ sub)
      rw [card_union_of_disjoint dj] at improved
      exact improved.trans (cap₂ u)
    obtain ⟨v,vc,u,ua,vu,tu⟩ := pick C Subset.rfl (by omega)
    let C' := C.erase v
    have c' : C'.card+1=C.card := card_erase_add_one vc
    obtain ⟨v',vc',u',ua',vu',tu'⟩ := pick C' (erase_subset _ _) (by omega)
    let C'' := C'.erase v'
    let E'' := C''.biUnion (fun u => H.filter (G.Adj u))
    have c'' : C''.card+1=C'.card := card_erase_add_one vc'
    have e'' : E''.card≤C''.card*d :=
      card_biUnion_le_card_mul C'' _ d (fun z hz => block z
        (mem_erase.mp (mem_erase.mp hz).2).2)
    have cov : E⊆E''∪(H.filter (G.Adj v'))∪(H.filter (G.Adj v)) := by
      intro z hz
      obtain ⟨s,hs,sz⟩ := mem_biUnion.mp hz
      by_cases e : s=v
      · exact mem_union.mpr (Or.inr (e ▸ sz))
      have hs' : s∈C' := mem_erase.mpr ⟨e,hs⟩
      by_cases e' : s=v'
      · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr (e' ▸ sz))))
      exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (mem_biUnion.mpr
        ⟨s,mem_erase.mpr ⟨e',hs'⟩,sz⟩))))
    have u₁ := card_union_le (E''∪(H.filter (G.Adj v'))) (H.filter (G.Adj v))
    have u₂ := card_union_le E'' (H.filter (G.Adj v'))
    have u₃ := card_le_card cov
    have b₁ := better v u ua vu tu
    have b₂ := better v' u' ua' vu' tu'
    have mul : C.card*d=C''.card*d+2*d := by
      rw [show C.card=C''.card+2 by omega,Nat.add_mul]
    omega
  have cH := card_le_card hcov
  have eh := card_union_le E Y
  have estimate : H.card+F.card+W.card≤k*d := by
    have m : k*d=C.card*d+d := by rw [←cs,Nat.add_mul,one_mul]
    rcases stronger with h|h <;> omega
  have cover : (univ : Finset V)⊆A∪B∪F∪H∪W := by
    intro z _
    apply mem_union.mpr
    by_cases w : G.dist x z=4
    · exact Or.inr (mem_shell.mpr w)
    apply Or.inl
    by_cases za : z∈A
    · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (mem_union.mpr (Or.inl za)))))
    by_cases zb : z∈B
    · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (mem_union.mpr (Or.inr zb)))))
    have nz : x≠z := fun e => za (e ▸ xa)
    have no : ¬G.Adj x z := fun e => zb (acl x xa z za e)
    have lo := hc.one_lt_dist_of_ne_of_not_adj nz no
    have hi := rad z
    by_cases d2 : G.dist x z=2
    · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr
        (mem_sdiff.mpr ⟨Graffiti189LongestPath.mem_distanceTwo.mpr d2,zb⟩))))
    · exact mem_union.mpr (Or.inr (mem_shell.mpr (by omega)))
  have cv := card_le_card cover
  rw [card_univ] at cv
  have c₁ := card_union_le A B
  have c₂ := card_union_le (A∪B) F
  have c₃ := card_union_le (A∪B∪F) H
  have c₄ := card_union_le (A∪B∪F∪H) W
  change Fintype.card V≤A.card+k+k*d
  omega

#print axioms single_star_order_upper_radius_four
end Graffiti189LongestPath.SingleFourthBudget
