import SmallSeparator189
import ArticulationGeneralClosure189
import ThreeFifthsDeficit189
open Finset SimpleGraph SimpleGraph.Walk
set_option maxHeartbeats 5000000
namespace Graffiti189LongestPath.SplitCliqueRoute

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- If q off-clique vertices each have q+1 clique neighbors, a path
can consume them one at a time from any prescribed clique start.
Edges between off-clique vertices are irrelevant. -/
theorem path_from_clique_start (C I : Finset V) (c0 : V) (start : c0∈C)
    (dis : Disjoint C I) (clique : ∀ u∈C,∀ v∈C,u≠v → G.Adj u v)
    (deg : ∀ u∈I,I.card+1≤(C.filter (G.Adj u)).card) :
    ∃ v,∃ q : G.Walk c0 v,q.IsPath ∧ ∀ z,z∈q.support↔z∈C∪I := by
  classical
  have claim (n : Nat) : ∀ (C I : Finset V), C.card+I.card=n → ∀ (c0 : V), c0∈C →
      Disjoint C I → (∀ u∈C,∀ v∈C,u≠v → G.Adj u v) →
      (∀ u∈I,I.card+1≤(C.filter (G.Adj u)).card) →
      ∃ v,∃ q : G.Walk c0 v,q.IsPath ∧ ∀ z,z∈q.support↔z∈C∪I := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro C I hn c0 cC dis clique deg
      let R := C.erase c0
      have cs : R⊆C := erase_subset _ _
      have hC : R.card+1=C.card := card_erase_add_one cC
      have cliqueR (u : V) (ur : u∈R) (v : V) (vr : v∈R) (ne : u≠v) :
          G.Adj u v := clique u (cs ur) v (cs vr) ne
      have ncR : c0∉R := fun e => (mem_erase.mp e).1 rfl
      have ncI : c0∉I := fun e => disjoint_left.mp dis cC e
      have lose (v : V) : (C.filter (G.Adj v)).card≤(R.filter (G.Adj v)).card+1 := by
        have inc : (C.filter (G.Adj v)).erase c0⊆R.filter (G.Adj v) := by
          intro z zz
          obtain ⟨zn,zC⟩ := mem_erase.mp zz
          obtain ⟨zC,ed⟩ := mem_filter.mp zC
          exact mem_filter.mpr ⟨mem_erase.mpr ⟨zn,zC⟩,ed⟩
        have b := card_le_card inc
        by_cases cc : c0∈C.filter (G.Adj v)
        · have e := card_erase_add_one cc
          omega
        · rw [erase_eq_of_not_mem cc] at b
          omega
      by_cases sees : ∃ u∈I,G.Adj c0 u
      · obtain ⟨u,ui,cu⟩ := sees
        let J := I.erase u
        have js : J⊆I := erase_subset _ _
        have jcard : J.card+1=I.card := card_erase_add_one ui
        have du := deg u ui
        have iPos := card_pos.mpr ⟨u,ui⟩
        obtain ⟨c1,c1N,cn⟩ := exists_ne_of_one_lt_card
          (show 1<(C.filter (G.Adj u)).card from by omega) c0
        obtain ⟨c1C,uc1⟩ := mem_filter.mp c1N
        have sr : c1∈R := mem_erase.mpr ⟨cn,c1C⟩
        have dis' : Disjoint R J := disjoint_left.mpr (fun _ zz yy => disjoint_left.mp dis (cs zz) (js yy))
        have deg' (v : V) (vj : v∈J) : J.card+1≤(R.filter (G.Adj v)).card := by
          have a := deg v (js vj)
          have e := lose v
          omega
        obtain ⟨v,q,qp,qs⟩ := ih (R.card+J.card) (by omega) R J rfl c1 sr dis' cliqueR deg'
        have un : u∉q.support := by
          intro uq
          rcases mem_union.mp ((qs u).mp uq) with ur|uj
          · exact disjoint_left.mp dis (cs ur) ui
          · exact (mem_erase.mp uj).1 rfl
        have c0q : c0∉q.support := by
          intro z
          exact (mem_union.mp ((qs c0).mp z)).elim ncR (fun e => ncI (js e))
        have cn : c0∉(Walk.cons uc1 q).support := by
          simp only [support_cons,List.mem_cons,not_or]
          exact ⟨cu.ne,c0q⟩
        refine ⟨v,.cons cu (.cons uc1 q),(qp.cons un).cons cn,?_⟩
        intro z
        simp only [support_cons,List.mem_cons,qs,mem_union,mem_erase,J,R]
        have hC : z=c0 → z∈C := fun h => h.symm ▸ cC
        have hI : z=u → z∈I := fun h => h.symm ▸ ui
        tauto
      · by_cases nonempty : R.Nonempty
        · obtain ⟨c1,c1R⟩ := nonempty
          have dis' : Disjoint R I := disjoint_left.mpr (fun _ zC zI => disjoint_left.mp dis (cs zC) zI)
          have deg' (u : V) (ui : u∈I) : I.card+1≤(R.filter (G.Adj u)).card := by
            have sub : C.filter (G.Adj u)⊆R.filter (G.Adj u) := by
              intro z zz
              obtain ⟨zC,uz⟩ := mem_filter.mp zz
              exact mem_filter.mpr ⟨mem_erase.mpr ⟨fun h => sees ⟨u,ui,h ▸ uz.symm⟩,zC⟩,uz⟩
            exact (deg u ui).trans (card_le_card sub)
          obtain ⟨v,q,qp,qs⟩ := ih (R.card+I.card) (by omega) R I rfl c1 c1R dis' cliqueR deg'
          have edge := clique c0 cC c1 (cs c1R) (mem_erase.mp c1R).1.symm
          have endN : c0∉q.support := by
            intro z
            exact (mem_union.mp ((qs c0).mp z)).elim ncR ncI
          refine ⟨v,.cons edge q,qp.cons endN,?_⟩
          intro z
          simp only [support_cons,List.mem_cons,qs,mem_union,mem_erase,R]
          have hC : z=c0 → z∈C := fun h => h.symm ▸ cC
          tauto
        · have r0 : R.card=0 := by
            apply Nat.eq_zero_of_not_pos
            intro h
            exact nonempty (card_pos.mp h)
          have i0 : I=∅ := by
            ext z
            constructor
            · intro zi
              have b := deg z zi
              have r := card_le_card (filter_subset (G.Adj z) C)
              have j := card_pos.mpr ⟨z,zi⟩
              omega
            · simp
          have c1 : C={c0} := by
            ext z
            constructor
            · intro hz
              exact mem_singleton.mpr (Classical.byContradiction
                (fun h => nonempty ⟨z,mem_erase.mpr ⟨h,hz⟩⟩))
            · intro hz
              exact (mem_singleton.mp hz).symm ▸ cC
          refine ⟨c0,.nil,IsPath.nil,?_⟩
          intro z
          simp [c1,i0]
  exact claim (C.card+I.card) C I rfl c0 start dis clique deg

#print axioms path_from_clique_start
end Graffiti189LongestPath.SplitCliqueRoute
open Finset SimpleGraph SimpleGraph.Walk
set_option maxHeartbeats 5000000
namespace Graffiti189LongestPath.SplitUniversalRoute
open Graffiti189LongestPath.SplitCliqueRoute
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
theorem alternating_from_clique_start (C I : Finset V) (c0 : V) (start : c0∈C)
    (dis : Disjoint C I) (equal : C.card=I.card)
    (all : ∀ u∈C,∀ v∈I,G.Adj u v) :
    ∃ v,∃ q : G.Walk c0 v,q.IsPath ∧ ∀ z,z∈q.support↔z∈C∪I := by
  classical
  have claim (n : Nat) : ∀ (C I : Finset V), C.card=n → C.card=I.card →
      ∀ (c0 : V),c0∈C → Disjoint C I → (∀ u∈C,∀ v∈I,G.Adj u v) →
      ∃ v,∃ q : G.Walk c0 v,q.IsPath ∧ ∀ z,z∈q.support↔z∈C∪I := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro C I cn eq c0 c0C dis all
      have cpos : 0<C.card := card_pos.mpr ⟨c0,c0C⟩
      obtain ⟨u,ui⟩ := card_pos.mp (show 0<I.card from by omega)
      have cu : G.Adj c0 u := all _ c0C _ ui
      let R := C.erase c0
      let J := I.erase u
      have cs : R⊆C := erase_subset _ _
      have js : J⊆I := erase_subset _ _
      have rc : R.card+1=C.card := card_erase_add_one c0C
      have jc : J.card+1=I.card := card_erase_add_one ui
      by_cases r : R.Nonempty
      · obtain ⟨c1,sr⟩ := r
        have dis' : Disjoint R J := disjoint_left.mpr (fun _ zz yy => disjoint_left.mp dis (cs zz) (js yy))
        have all' (u : V) (uR : u∈R) (v : V) (vJ : v∈J) : G.Adj u v :=
          all _ (cs uR) _ (js vJ)
        obtain ⟨v,q,qp,qs⟩ := ih R.card (by omega) R J rfl (by omega) c1 sr dis' all'
        have uc1 : G.Adj u c1 := (all _ (cs sr) _ ui).symm
        have un : u∉q.support := by
          intro uq
          rcases mem_union.mp ((qs u).mp uq) with ur|uj
          · exact disjoint_left.mp dis (cs ur) ui
          · exact (mem_erase.mp uj).1 rfl
        have c0q : c0∉q.support := by
          intro uq
          rcases mem_union.mp ((qs c0).mp uq) with ur|uj
          · exact (mem_erase.mp ur).1 rfl
          · exact disjoint_left.mp dis c0C (js uj)
        have ne : c0∉(Walk.cons uc1 q).support := by
          simp only [support_cons,List.mem_cons,not_or]
          exact ⟨cu.ne,c0q⟩
        refine ⟨v,.cons cu (.cons uc1 q),(qp.cons un).cons ne,?_⟩
        intro z
        simp only [support_cons,List.mem_cons,qs,mem_union,mem_erase,J,R]
        have c : z=c0 → z∈C := fun h => h.symm ▸ c0C
        have u' : z=u → z∈I := fun h => h.symm ▸ ui
        tauto
      · have rc0 : R.card=0 := Nat.eq_zero_of_not_pos (fun pos => r (card_pos.mp pos))
        have jc0 : J.card=0 := by omega
        have cs' : C={c0} := by
          have s : {c0}⊆C := singleton_subset_iff.mpr c0C
          exact (eq_of_subset_of_card_le s (by rw [card_singleton]; omega)).symm
        have js' : I={u} := by
          have s : {u}⊆I := singleton_subset_iff.mpr ui
          exact (eq_of_subset_of_card_le s (by rw [card_singleton]; omega)).symm
        exact ⟨u,cu.toWalk,IsPath.of_adj cu, by intro z; simp [cs',js',SimpleGraph.Adj.toWalk]⟩
  exact claim C.card C I rfl equal c0 start dis all

theorem universal_from_clique_start (C I : Finset V) (c0 : V) (start : c0∈C)
    (dis : Disjoint C I) (le : I.card≤C.card)
    (clique : ∀ u∈C,∀ v∈C,u≠v → G.Adj u v)
    (all : ∀ u∈C,∀ v∈I,G.Adj u v) :
    ∃ v,∃ q : G.Walk c0 v,q.IsPath ∧ ∀ z,z∈q.support↔z∈C∪I := by
  by_cases eq : C.card=I.card
  · exact alternating_from_clique_start C I c0 start dis eq all
  apply path_from_clique_start C I c0 start dis clique
  intro u ui
  have e : C⊆C.filter (G.Adj u) := fun v vc => mem_filter.mpr ⟨vc,(all v vc u ui).symm⟩
  exact (show I.card+1≤C.card from by omega).trans (card_le_card e)

#print axioms alternating_from_clique_start
#print axioms universal_from_clique_start
end Graffiti189LongestPath.SplitUniversalRoute
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.DeficitActive Graffiti189LongestPath.DeficitLongest
open Graffiti189LongestPath.SplitCliqueRoute Graffiti189LongestPath.SplitUniversalRoute
open private Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two from SmallSeparator189
set_option maxHeartbeats 9000000
namespace Graffiti189LongestPath.SplitTraceability
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem traceable_of_split_min_degree_two (hc : G.Connected) (d : Nat) (d2 : 2≤d)
    (floor : ∀ u,2≤G.degree u)
    (deg : ∀ u v : V,u≠v → d≤G.degree u ∨ d≤G.degree v)
    (tight : ∃ u v : V,u≠v ∧ G.degree u≤d ∧ G.degree v≤d)
    (even : ∀ u,(EvenFrom G u).card≤d+1)
    (C I : Finset V) (parts : (univ:Finset V)=C∪I) (di : Disjoint C I)
    (cl : ∀ u∈C,∀ v∈C,u≠v → G.Adj u v)
    (ind : ∀ u∈I,∀ v∈I,¬G.Adj u v) :
    ∃ (a b : V) (q : G.Walk a b),q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  let N (u : V) := C.filter (G.Adj u)
  have part (z : V) : z∈C∨z∈I := mem_union.mp (parts ▸ mem_univ z)
  have cardP : Fintype.card V=C.card+I.card := by
    have q := congrArg Finset.card parts
    rwa [card_univ,card_union_of_disjoint di] at q
  have nh (u : V) (ui : u∈I) : G.neighborFinset u=N u := by
    ext z
    rw [G.mem_neighborFinset]
    constructor
    · intro uz
      exact mem_filter.mpr ⟨(part z).resolve_right (fun zi => ind u ui z zi uz),uz⟩
    · exact fun zN => (mem_filter.mp zN).2
  have nd (u : V) (ui : u∈I) : (N u).card=G.degree u := by
    rw [←nh u ui,G.card_neighborFinset_eq_degree]
  have ns (u : V) : N u⊆C := filter_subset _ _
  have adDC (u : V) (ui : u∈I) : ∃ c∈C,G.Adj u c := by
    obtain ⟨v,vn⟩ := card_pos.mp (show 0<(N u).card from by have ne := floor u; rw [nd u ui]; omega)
    exact ⟨v,(mem_filter.mp vn).1,(mem_filter.mp vn).2⟩
  have share (u v : V) (ui : u∈I) (vi : v∈I) (sum : C.card<G.degree u+G.degree v) :
      ∃ z∈C,G.Adj u z∧G.Adj v z := by
    apply Classical.byContradiction
    intro contrary
    have ds : Disjoint (N u) (N v) := disjoint_left.mpr (fun z zu zv =>
      contrary ⟨z,ns u zu,(mem_filter.mp zu).2,(mem_filter.mp zv).2⟩)
    have nn := card_le_card (union_subset (ns u) (ns v))
    rw [card_union_of_disjoint ds,nd u ui,nd v vi] at nn
    omega
  have pack (u : V) (ui : u∈I) (J : Finset V) (ji : J⊆I) (un : u∉J)
      (ac : ∀ v∈J,∃ z∈C,G.Adj u z∧G.Adj v z) :
      C.card+J.card≤d+G.degree u := by
    obtain ⟨c,cc,uc⟩ := adDC u ui
    have a : C\N u⊆DistanceTwo G u := by
      intro z zz
      obtain ⟨zc,zn⟩ := mem_sdiff.mp zz
      have ne : u≠z := fun e => disjoint_left.mp di (e.symm ▸ zc) ui
      have na : ¬G.Adj u z := fun h => zn (mem_filter.mpr ⟨zc,h⟩)
      have cZ : c≠z := fun e => na (e ▸ uc)
      exact Graffiti189LongestPath.mem_distanceTwo.mpr
        (Graffiti189LongestPath.dist_two hc ne na uc (cl c cc z zc cZ))
    have b : J⊆DistanceTwo G u := by
      intro z zj
      obtain ⟨v,_,uv,zv⟩ := ac z zj
      have ne : u≠z := fun e => un (e.symm ▸ zj)
      exact Graffiti189LongestPath.mem_distanceTwo.mpr
        (Graffiti189LongestPath.dist_two hc ne (ind u ui z (ji zj)) uv zv.symm)
    have ds : Disjoint (C\N u) J := disjoint_left.mpr (fun _ cc jj =>
      disjoint_left.mp di (mem_sdiff.mp cc).1 (ji jj))
    have z := (card_le_card (union_subset a b)).trans (distanceTwo_le_of_even d u (even u))
    rw [card_union_of_disjoint ds] at z
    have su := card_sdiff_add_card_eq_card (ns u)
    rw [nd u ui] at su
    omega
  have basic (u : V) (ui : u∈I) : C.card≤d+G.degree u := by
    have q := pack u ui ∅ (empty_subset _) (by simp) (by simp)
    simpa using q
  have up (u : V) (ui : u∈I) : G.degree u≤C.card := by
    rw [←nd u ui]
    exact card_le_card (ns u)
  have nspan (size : Fintype.card V≤2*d+1) :
      ∃ (a b : V) (q : G.Walk a b),q.IsPath ∧ ∀ z,z∈q.support := by
    apply Classical.byContradiction
    intro fail
    obtain ⟨a,b,p,pp⟩ := exists_longest hc
    have len := longest_length_ge_twice_of_not_traceable hc d d2 floor deg fail pp
    let X := p.support.toFinset
    have cX : X.card=p.length+1 := by
      dsimp [X]
      rw [List.toFinset_card_of_nodup pp.1.support_nodup,length_support]
    have all : (univ:Finset V)⊆X := by
      have ca : (univ:Finset V).card≤X.card := by rw [card_univ,cX]; omega
      exact (eq_of_subset_of_card_le (subset_univ X) ca).symm ▸ subset_univ _
    exact fail ⟨a,b,p,pp.1,fun z => List.mem_toFinset.mp (all (mem_univ z))⟩
  by_cases nen : I.Nonempty
  · obtain ⟨x,xi,xall⟩ : ∃ x∈I,∀ v∈I,v≠x → d≤G.degree v := by
      by_cases low : ∃ x∈I,G.degree x<d
      · obtain ⟨x,xi,xl⟩ := low
        exact ⟨x,xi,fun v _ ne => (deg v x ne).resolve_right (Nat.not_le_of_lt xl)⟩
      · obtain ⟨x,xi⟩ := nen
        exact ⟨x,xi,fun v vi _ => Nat.le_of_not_gt (fun e => low ⟨v,vi,e⟩)⟩
    let J := I.erase x
    have jc : J.card+1=I.card := card_erase_add_one xi
    have js : J⊆I := erase_subset _ _
    have Jhi (v : V) (vj : v∈J) : d≤G.degree v := xall v (js vj) (mem_erase.mp vj).1
    obtain ⟨c0,cc,xc0⟩ := adDC x xi
    have dj : Disjoint C J := disjoint_left.mpr (fun _ vc vj => disjoint_left.mp di vc (js vj))
    have lift (v : V) (q : G.Walk c0 v) (qp : q.IsPath)
        (qs : ∀ z,z∈q.support↔z∈C∪J) :
        ∃ (a b : V) (q : G.Walk a b),q.IsPath ∧ ∀ z,z∈q.support := by
      have xn : x∉q.support := by
        intro xq
        rcases mem_union.mp ((qs x).mp xq) with xc|xj
        · exact disjoint_left.mp di xc xi
        · exact (mem_erase.mp xj).1 rfl
      refine ⟨x,v,.cons xc0 q,qp.cons xn,?_⟩
      intro z
      by_cases zx : z=x
      · subst z
        exact (Walk.cons xc0 q).start_mem_support
      have mem : z∈C∪J := (part z).elim (fun vc => mem_union.mpr (Or.inl vc))
        (fun zi => mem_union.mpr (Or.inr (mem_erase.mpr ⟨zx,zi⟩)))
      exact List.mem_cons_of_mem _ ((qs z).mpr mem)
    have solve (limit : J.card+1≤d) :
        ∃ (a b : V) (q : G.Walk a b),q.IsPath ∧ ∀ z,z∈q.support := by
      obtain ⟨v,q,qp,qs⟩ := path_from_clique_start C J c0 cc dj cl (by
        intro u uj
        rw [show (C.filter (G.Adj u)).card=G.degree u from nd u (js uj)]
        exact limit.trans (Jhi u uj))
      exact lift v q qp qs
    by_cases one : I.card≤1
    · exact solve (by omega)
    have jPos : J.Nonempty := card_pos.mp (by omega)
    obtain ⟨y,yJ⟩ := jPos
    have yi := js yJ
    have hy := Jhi y yJ
    have cd : d≤C.card := hy.trans (up y yi)
    have universal (all : ∀ u∈J,C.card≤G.degree u) :
        ∃ (a b : V) (q : G.Walk a b),q.IsPath ∧ ∀ z,z∈q.support := by
      have full (u : V) (uj : u∈J) : N u=C := eq_of_subset_of_card_le (ns u) (by
        rw [nd u (js uj)]
        exact all u uj)
      have jp : J.card≤C.card := by
        have c := pack y yi (I.erase y) (erase_subset _ _) (by simp) (by
          intro z zz
          have zi := (mem_erase.mp zz).2
          obtain ⟨v,vc,zv⟩ := adDC z zi
          exact ⟨v,vc,(mem_filter.mp ((full y yJ).symm ▸ vc)).2,zv⟩)
        have ie := card_erase_add_one yi
        have small := up y yi
        omega
      obtain ⟨v,q,qp,qs⟩ := universal_from_clique_start C J c0 cc dj jp cl (by
        intro z zc u uj
        exact ((mem_filter.mp ((full u uj).symm ▸ zc)).2).symm)
      exact lift v q qp qs
    by_cases eqd : C.card=d
    · exact universal (by intro u ui; rw [eqd]; exact Jhi u ui)
    by_cases near : C.card=d+1
    · by_cases hit : ∃ u∈I,G.degree u=d
      · obtain ⟨u,ui,du⟩ := hit
        have c := pack u ui (I.erase u) (erase_subset _ _) (by simp) (by
          intro v vv
          have ii := (mem_erase.mp vv).2
          have h := floor v
          exact share u v ui ii (by omega))
        have ee := card_erase_add_one ui
        exact nspan (by omega)
      · exact universal (by
          intro u uj
          have uu := Jhi u uj
          have neq : G.degree u≠d := fun h => hit ⟨u,js uj,h⟩
          omega)
    have large : d+2≤C.card := by omega
    have cdeg (u : V) (uc : u∈C) : C.card≤G.degree u+1 := by
      have all : C.erase u⊆G.neighborFinset u := by
        intro v vv
        obtain ⟨ne,vc⟩ := mem_erase.mp vv
        exact (G.mem_neighborFinset _ _).mpr (cl u uc v vc ne.symm)
      have a := card_le_card all
      rw [G.card_neighborFinset_eq_degree] at a
      have b := card_erase_add_one uc
      omega
    obtain ⟨u,ui,du⟩ : ∃ u∈I,G.degree u=d := by
      obtain ⟨a,b,ne,ha,hb⟩ := tight
      have ai : a∈I := (part a).resolve_left (fun ac => by have q := cdeg a ac; omega)
      have bi : b∈I := (part b).resolve_left (fun bc => by have q := cdeg b bc; omega)
      exact (deg a b ne).elim (fun h => ⟨a,ai,by omega⟩) (fun h => ⟨b,bi,by omega⟩)
    have ctop : C.card≤2*d := by have q := basic u ui; omega
    by_cases border : C.card=2*d
    · have disjN (v : V) (vi : v∈I) (ne : v≠u) : Disjoint (N u) (N v) := by
        apply disjoint_left.mpr
        intro z zu zv
        have q := pack u ui ({v}:Finset V) (singleton_subset_iff.mpr vi)
          (by simpa only [mem_singleton] using ne.symm) (by
            intro w wv
            have eq := mem_singleton.mp wv
            exact ⟨z,ns u zu,(mem_filter.mp zu).2,eq.symm ▸ (mem_filter.mp zv).2⟩)
        rw [card_singleton] at q
        omega
      have compl (v : V) (vi : v∈I) (ne : v≠u) : N v=C\N u := by
        have incl : N v⊆C\N u := fun z zz =>
          mem_sdiff.mpr ⟨ns v zz,fun zu => disjoint_left.mp (disjN v vi ne) zu zz⟩
        have q := basic v vi
        have e := card_sdiff_add_card_eq_card (ns u)
        rw [nd u ui] at e
        exact eq_of_subset_of_card_le incl (by rw [nd v vi]; omega)
      have one : (I.erase u).card≤1 := by
        apply Nat.le_of_not_gt
        intro h
        obtain ⟨v,vI,w,wI,ne⟩ := one_lt_card.mp h
        obtain ⟨vn,vi⟩ := mem_erase.mp vI
        obtain ⟨wn,wi⟩ := mem_erase.mp wI
        have vr := compl v vi vn
        have wr := compl w wi wn
        obtain ⟨z,zC,vz⟩ := adDC v vi
        have zN : z∈N v := mem_filter.mpr ⟨zC,vz⟩
        have zW : z∈N w := (wr.trans vr.symm).symm ▸ zN
        have q := pack v vi ({w}:Finset V) (singleton_subset_iff.mpr wi)
          (by simpa using ne) (by
            intro z' hz'
            have eq := mem_singleton.mp hz'
            exact ⟨z,zC,vz,eq.symm ▸ (mem_filter.mp zW).2⟩)
        rw [card_singleton] at q
        have e := card_sdiff_add_card_eq_card (ns u)
        rw [nd u ui] at e
        have cv := congrArg Finset.card vr
        rw [nd v vi] at cv
        omega
      have ee := card_erase_add_one ui
      exact solve (by omega)
    · have q := pack u ui (J.erase u) ((erase_subset _ _).trans js) (by simp) (by
        intro v vv
        have vj := (mem_erase.mp vv).2
        have z := Jhi v vj
        exact share u v ui (js vj) (by omega))
      have ee : J.card≤(J.erase u).card+1 := by
        by_cases uu : u∈J
        · have e := card_erase_add_one uu; omega
        · rw [erase_eq_of_not_mem uu]; omega
      exact solve (by omega)
  · have i0 : I=∅ := not_nonempty_iff_eq_empty.mp nen
    obtain ⟨c0⟩ := hc.nonempty
    have cc : c0∈C := (part c0).elim id (fun h => by simp [i0] at h)
    obtain ⟨v,q,qp,qs⟩ := path_from_clique_start C I c0 cc di cl (by
      intro u ui
      simp [i0] at ui)
    exact ⟨c0,v,q,qp,fun z => (qs z).mpr (parts ▸ mem_univ z)⟩


/-- The exact second-smallest-degree claim for a connected split graph,
with the low-degree and articulation boundary already separated. -/
theorem traceable_of_split (hc : G.Connected) (d : Nat) (d2 : 2≤d)
    (deg : ∀ u v : V,u≠v → d≤G.degree u ∨ d≤G.degree v)
    (tight : ∃ u v : V,u≠v ∧ G.degree u≤d ∧ G.degree v≤d)
    (even : ∀ u,(EvenFrom G u).card≤d+1)
    (C I : Finset V) (parts : (univ:Finset V)=C∪I) (di : Disjoint C I)
    (cl : ∀ u∈C,∀ v∈C,u≠v → G.Adj u v)
    (ind : ∀ u∈I,∀ v∈I,¬G.Adj u v) :
    ∃ (a b : V) (q : G.Walk a b),q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  by_cases robust : ∀ S : Finset V,S.card<2 → (G.induce ((↑S:Set V)ᶜ)).Connected
  · have enough : 3≤Fintype.card V := by
      obtain ⟨u,v,ne,_,_⟩ := tight
      have uD := G.degree_lt_card_verts u
      have vD := G.degree_lt_card_verts v
      cases deg u v ne <;> omega
    exact traceable_of_split_min_degree_two hc d d2
      (degree_floor_when_enough_vertices 2 robust enough) deg tight even C I parts di cl ind
  · obtain ⟨S,small,bad⟩ : ∃ S : Finset V,S.card<2 ∧ ¬(G.induce ((↑S:Set V)ᶜ)).Connected := by
      apply Classical.byContradiction
      intro none
      apply robust
      intro S small
      exact Classical.byContradiction (fun z => none ⟨S,small,z⟩)
    have nonempty : S.Nonempty := by
      apply Classical.byContradiction
      intro e
      have empty : S=∅ := not_nonempty_iff_eq_empty.mp e
      apply bad
      rw [empty,coe_empty,Set.compl_empty]
      exact (SimpleGraph.induceUnivIso G).connected_iff.mpr hc
    obtain ⟨x,xs⟩ := nonempty
    have eq : S={x} := (eq_of_subset_of_card_le (singleton_subset_iff.mpr xs)
      (by rw [card_singleton]; omega)).symm
    have setEq : (↑S:Set V)ᶜ={z : V | z≠x} := by rw [eq]; ext z; simp
    exact Graffiti189LongestPath.CrossSaturation.traceable_at_articulation_general hc d d2 even deg x
      (by rw [←setEq]; exact bad)

#print axioms traceable_of_split_min_degree_two
#print axioms traceable_of_split
end Graffiti189LongestPath.SplitTraceability
