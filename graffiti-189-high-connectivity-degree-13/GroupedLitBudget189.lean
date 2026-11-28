import SingleStar189
import OneDefectHall189
import ExactStarShore189
import TwoShoreDefect189
import MultiPinRotation189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.ActiveStarHeight
open Graffiti189LongestPath.OneDefectHall Graffiti189LongestPath.TruncatedHall Graffiti189LongestPath.ForeignPorts
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.no_endpoints Graffiti189LongestPath.boundary_card_of_connectivity Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two
  Graffiti189LongestPath.distance_on_geodesic from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.mem_omittedStar Graffiti189LongestPath.Rigidity.mem_external
  Graffiti189LongestPath.Rigidity.pin_pos from Rigidity189
open private Graffiti189LongestPath.OneSlack.cardinal_flankVertices Graffiti189LongestPath.OneSlack.card_pinVertices
  Graffiti189LongestPath.OneSlack.first_eq_if_no_pair Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary
    Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem from OneSlack189
open private Graffiti189LongestPath.OneSlack.MultiRotation.rigidity_of_tight from MultiPinRotation189
set_option warningAsError true
set_option maxHeartbeats 4000000
namespace Graffiti189LongestPath.GroupedLitBudget
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The exact-cut single-pin star spends its missing distance-two slots
at either the unique pin or a non-pin gateway. -/
theorem oversized_single_grouped_budget (hc : G.Connected) (k : Nat) (hk : 11≤k)
    (cap : ∀ v, (EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x∉p.support)
    (high : k+2≤G.degree x) (one : (Pins p x).card=1)
    (ht : (OmittedStar p x).card≤k+4) (bk : (External G (OmittedStar p x)).card=k+1) (rad : ∀ z,G.dist x z≤4)
    (donor : ∃ v : ↥((OmittedStar p x : Finset V) : Set V),
      (G.induce (OmittedStar p x : Set V)).degree v≤(OmittedStar p x).card/2 ∧
        k+2≤G.degree v.val) :
    Fintype.card V+k+2*(k-1)≤2*(OmittedStar p x).card+k*(k+2)+9 := by
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
  change B.card=k+1 at bk
  have fs : F.card+W.card≤2 := by have h := budget.2.2.2.1; change B.card+F.card+W.card≤k+3 at h; omega
  have fl : 2≤F.card := budget.2.2.1
  have cs : C.card=k := by
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
  change A.card≤k+4 at ht
  let L := C.filter (G.Adj t)
  let Q := C\L
  have ql : Q.card+L.card=k := (card_sdiff_add_card_eq_card (filter_subset _ _)).trans cs
  have tc : t∈PinVertices p x := mem_image.mpr ⟨i,hi,rfl⟩
  have tb : t∈B := Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary hx tc
  have ld : k≤G.degree t := by
    by_cases h : ∃ z,z≠t ∧ ¬G.Adj t z
    · obtain ⟨z,zt,n⟩ := h
      rw [←G.card_neighborFinset_eq_degree]
      exact Graffiti189LongestPath.boundary_card_of_connectivity k conn
        (mem_singleton_self t) (fun e => zt (mem_singleton.mp e))
        (fun e => n ((G.mem_neighborFinset _ _).mp e))
        (disjoint_left.mpr (fun _ a b => ((G.mem_neighborFinset _ _).mp b).ne
          (mem_singleton.mp a).symm))
        (fun a ha v _ ed => (G.mem_neighborFinset _ _).mpr ((mem_singleton.mp ha) ▸ ed))
    · have hV : (univ : Finset V)⊆insert t (G.neighborFinset t) := by
        intro z _
        by_cases zt : z=t
        · exact mem_insert.mpr (Or.inl zt)
        exact mem_insert.mpr (Or.inr ((G.mem_neighborFinset _ _).mpr
          (Classical.byContradiction (fun no => h ⟨z,zt,no⟩))))
      have e := (card_le_card hV).trans (card_insert_le _ _)
      rw [card_univ,G.card_neighborFinset_eq_degree] at e
      have v := (card_le_card (subset_univ (G.neighborFinset x)))
      rw [card_univ,G.card_neighborFinset_eq_degree] at v
      omega
  have pinset : PinVertices p x={t} := by
    change (Pins p x).image p.getVert={t}
    rw [pair,image_singleton]
  have pcount : T.card+G.degree t≤L.card+A.card+2 := by
    let N := A.filter (G.Adj t)
    have cn : N.card+T.card=A.card := by
      have e : A\N=T := by ext z; simp [N,T]; tauto
      rw [←e,add_comm,card_sdiff_add_card_eq_card (filter_subset _ _)]
    have cover : G.neighborFinset t⊆N∪L∪F := by
      intro v hv
      have ed := (G.mem_neighborFinset _ _).mp hv
      by_cases va : v∈A
      · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (mem_filter.mpr ⟨va,ed⟩))))
      by_cases vb : v∈B
      · have nc : v∉PinVertices p x := by rw [pinset]; exact fun h => ed.ne (mem_singleton.mp h).symm
        exact mem_union.mpr (Or.inl (mem_union.mpr
          (Or.inr (mem_filter.mpr ⟨mem_sdiff.mpr ⟨vb,nc⟩,ed⟩))))
      have xv : x≠v := fun eq => va (eq ▸ xa)
      have no : ¬G.Adj x v := fun e => vb (acl x xa v va e)
      exact mem_union.mpr (Or.inr (mem_sdiff.mpr
        ⟨Graffiti189LongestPath.mem_distanceTwo.mpr (Graffiti189LongestPath.dist_two hc xv no tx ed),vb⟩))
    have c := card_le_card cover
    rw [G.card_neighborFinset_eq_degree] at c
    have a := card_union_le N L
    have b := card_union_le (N∪L) F
    omega
  let E := Q.biUnion (fun v => H.filter (G.Adj v))
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
    have give (v : V) (xv : G.Adj x v) (vu : G.Adj v u) : z∈DistanceTwo G v := by
      have vx := dist_eq_one_iff_adj.mpr xv
      have ne : v≠z := fun r => by rw [r] at vx; omega
      have no : ¬G.Adj v z := by
        intro ed
        have vz := dist_eq_one_iff_adj.mpr ed
        have tri := hc.dist_triangle (u:=x) (v:=v) (w:=z)
        omega
      exact Graffiti189LongestPath.mem_distanceTwo.mpr (Graffiti189LongestPath.dist_two hc ne no vu uz)
    by_cases ub : u∈B
    · have no : u∉PinVertices p x := by
        intro h
        obtain ⟨l,hl,eq⟩ := mem_image.mp h
        have ed : G.Adj x u := eq ▸ (Graffiti189LongestPath.pin_data hl).2
        have e := dist_eq_one_iff_adj.mpr ed
        omega
      have uc : u∈C := mem_sdiff.mpr ⟨ub,no⟩
      by_cases ut : G.Adj t u
      · exact mem_union.mpr (Or.inr (mem_inter.mpr ⟨hz,give t tx ut⟩))
      exact mem_union.mpr (Or.inl (mem_biUnion.mpr
        ⟨u,mem_sdiff.mpr ⟨uc,fun h => ut (mem_filter.mp h).2⟩,mem_filter.mpr ⟨hz,uz⟩⟩))
    have uf : u∈F := mem_sdiff.mpr ⟨Graffiti189LongestPath.mem_distanceTwo.mpr du,ub⟩
    exact mem_union.mpr (Or.inr (mem_inter.mpr ⟨hz,give t tx (fromFlank u uf)⟩))
  let D := Q.filter (fun v => ¬∃ u∈A,G.Adj v u ∧ G.Adj t u)
  let K := Q\D
  have ds : D⊆Q := filter_subset _ _
  have ks : K.card+D.card=Q.card := card_sdiff_add_card_eq_card ds
  have dt : D.card≤T.card+1 := by
    have mm := defective_hall k A B D conn ab (by omega) (ds.trans (sdiff_subset.trans sdiff_subset))
      (fun h => (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp h).1 p.start_mem_support)
      (by
        intro h
        obtain ⟨_,u,ua,ed⟩ := Graffiti189LongestPath.Rigidity.mem_external.mp h
        exact (Graffiti189LongestPath.no_endpoints hp
          ((Graffiti189LongestPath.Rigidity.mem_omittedStar.mp ua).1)).1 ed) acl
    have ca := (card_le_card ds)
    rw [min_eq_right (by omega : D.card-1≤A.card)] at mm
    have sub : shoreNeighbors G A D⊆T := by
      intro u hu
      obtain ⟨ua,v,vd,vu⟩ := mem_filter.mp hu
      exact mem_filter.mpr ⟨ua,fun e => (mem_filter.mp vd).2 ⟨u,ua,vu,e⟩⟩
    have bc := card_le_card sub
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
  have diet (v : V) (vk : v∈K) : (H.filter (G.Adj v)).card≤d-2 := by
    have good : ∃ u∈A,G.Adj v u ∧ G.Adj t u :=
      Classical.byContradiction (fun bad => (mem_sdiff.mp vk).2
        (mem_filter.mpr ⟨(mem_sdiff.mp vk).1,bad⟩))
    obtain ⟨u,ua,vu,tu⟩ := good
    have e := better v u ua vu tu
    omega
  let ED := D.biUnion (fun v => H.filter (G.Adj v))
  let EK := K.biUnion (fun v => H.filter (G.Adj v))
  have ed : ED.card≤D.card*d := card_biUnion_le_card_mul D _ d
    (fun v vd => block v (mem_sdiff.mp (ds vd)).1)
  have ek : EK.card≤K.card*(d-2) := card_biUnion_le_card_mul K _ _ diet
  have cov : E⊆ED∪EK := by
    intro z hz
    obtain ⟨s,hs,sz⟩ := mem_biUnion.mp hz
    by_cases h : s∈D
    · exact mem_union.mpr (Or.inl (mem_biUnion.mpr ⟨s,h,sz⟩))
    · exact mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨s,mem_sdiff.mpr ⟨hs,h⟩,sz⟩))
  have es := (card_le_card cov).trans (card_union_le ED EK)
  have id : D.card*d+K.card*(d-2)+2*K.card=Q.card*d := by
    have xd : d-2+2=d := by omega
    rw [mul_comm 2 K.card,add_assoc,←Nat.mul_add,xd,←Nat.add_mul]
    rw [add_comm D.card K.card,ks]
  have shellbound : E.card+2*K.card+2*(d-3)≤Q.card*d+L.card*(d-3) := by
    by_cases lit : 2≤L.card
    · have l := Nat.mul_le_mul_right (d-3) lit
      omega
    obtain ⟨v,vid,vhigh⟩ := donor
    let u := v.val
    let I := G.induce (A : Set V)
    change I.degree v≤A.card/2 at vid
    let U := Q.filter (G.Adj u)
    have us : U⊆Q := filter_subset _ _
    have g : G.degree u≤I.degree v+U.card+L.card+1 := by
      let N := A.filter (G.Adj u)
      have ns : N.card=I.degree v := by
        rw [←I.card_neighborFinset_eq_degree]
        refine card_bij' (fun z hz => (⟨z,(mem_filter.mp hz).1⟩ : ↥(A : Set V)))
          (fun z _ => z.val) ?_ ?_ ?_ ?_
        · intro z hz
          exact (I.mem_neighborFinset _ _).mpr (mem_filter.mp hz).2
        · intro z hz
          exact mem_filter.mpr ⟨z.property,(I.mem_neighborFinset _ _).mp hz⟩
        · intro z hz; rfl
        · intro z hz; exact Subtype.ext rfl
      have cov : G.neighborFinset u⊆N∪U∪L∪{t} := by
        intro z hz
        have e := (G.mem_neighborFinset _ _).mp hz
        by_cases za : z∈A
        · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (mem_union.mpr
            (Or.inl (mem_filter.mpr ⟨za,e⟩))))))
        have zb := acl u v.property z za e
        by_cases zt : z=t
        · exact mem_union.mpr (Or.inr (mem_singleton.mpr zt))
        have zc : z∈C := mem_sdiff.mpr ⟨zb,by rw [pinset]; exact fun h => zt (mem_singleton.mp h)⟩
        by_cases zl : z∈L
        · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr zl)))
        exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (mem_union.mpr
          (Or.inr (mem_filter.mpr ⟨mem_sdiff.mpr ⟨zc,zl⟩,e⟩))))))
      have le := card_le_card cov
      rw [G.card_neighborFinset_eq_degree] at le
      have a := card_union_le N U
      have b := card_union_le (N∪U) L
      have c := card_union_le (N∪U∪L) ({t}:Finset V)
      rw [card_singleton] at c
      omega
    change k+2≤G.degree u at vhigh
    have three : 3≤U.card := by omega
    let EU := U.biUnion (fun v => H.filter (G.Adj v))
    have eU : EU.card≤d := by
      have ss : EU⊆DistanceTwo G u := by
        intro z zz
        obtain ⟨b,bu,zb⟩ := mem_biUnion.mp zz
        exact Graffiti189LongestPath.mem_distanceTwo.mpr
          (Graffiti189LongestPath.dist_two hc (neAH v.property (mem_filter.mp zb).1)
            (noAH v.property (mem_filter.mp zb).1) (mem_filter.mp bu).2 (mem_filter.mp zb).2)
      exact (card_le_card ss).trans (cap₂ u)
    let D' := D\U
    let K' := K\U
    let ED' := D'.biUnion (fun v => H.filter (G.Adj v))
    let EK' := K'.biUnion (fun v => H.filter (G.Adj v))
    have ed' : ED'.card≤D'.card*d := card_biUnion_le_card_mul D' _ d
      (fun v vd => block v (mem_sdiff.mp (ds (mem_sdiff.mp vd).1)).1)
    have ek' : EK'.card≤K'.card*(d-2) := card_biUnion_le_card_mul K' _ _ (fun v vk => diet v (mem_sdiff.mp vk).1)
    have cover : E⊆ED'∪EK'∪EU := by
      intro z hz
      obtain ⟨b,bq,bz⟩ := mem_biUnion.mp hz
      by_cases bu : b∈U
      · exact mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨b,bu,bz⟩))
      by_cases bd : b∈D
      · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl
          (mem_biUnion.mpr ⟨b,mem_sdiff.mpr ⟨bd,bu⟩,bz⟩))))
      exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr
        (mem_biUnion.mpr ⟨b,mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨bq,bd⟩,bu⟩,bz⟩))))
    have cd : D'.card+(D∩U).card=D.card := card_sdiff_add_card_inter _ _
    have ck : K'.card+(K∩U).card=K.card := card_sdiff_add_card_inter _ _
    have une : (D∩U)∪(K∩U)=U := by
      ext z
      simp only [mem_union,mem_inter]
      constructor
      · exact fun q => q.elim And.right And.right
      · intro h
        by_cases dz : z∈D
        · exact Or.inl ⟨dz,h⟩
        · exact Or.inr ⟨mem_sdiff.mpr ⟨us h,dz⟩,h⟩
    have dis : Disjoint (D∩U) (K∩U) :=
      disjoint_left.mpr (fun _ a b => (mem_sdiff.mp (mem_inter.mp b).1).2 (mem_inter.mp a).1)
    have su := congrArg Finset.card une
    rw [card_union_of_disjoint dis] at su
    have payoff := Nat.mul_le_mul_right (d-2) three
    have gain : U.card*(d-2)≤(D∩U).card*d+(K∩U).card*(d-2) := by
      rw [←su,Nat.add_mul]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
    have cd' := congrArg (fun n => n*d) cd
    have ck' := congrArg (fun n => n*(d-2)) ck
    simp only [Nat.add_mul] at cd' ck'
    have cv := card_le_card cover
    have a := card_union_le ED' EK'
    have b := card_union_le (ED'∪EK') EU
    have po : 3*(d-2)=d+2*(d-3) := by omega
    have drop : d+2*(d-3)≤U.card*(d-2) := po ▸ payoff
    omega
  have cH := card_le_card hcov
  have eh := card_union_le E Y
  have estimate : H.card+F.card+W.card+2*k+2*(d-3)≤k*d+A.card+8 := by
    have cd : k*d=Q.card*d+L.card*d := by rw [←ql,Nat.add_mul]
    have l' : L.card*(d-3)+3*L.card=L.card*d := by
      rw [mul_comm 3,←Nat.mul_add,show d-3+3=d by omega]
    omega
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

  change Fintype.card V+k+2*(k-1)≤2*A.card+k*d+9
  have e : d-3=k-1 := by omega
  rw [e] at estimate
  omega

#print axioms oversized_single_grouped_budget
end Graffiti189LongestPath.GroupedLitBudget
