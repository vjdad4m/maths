import ThreeMatchedSwap384b
import ThreeUntouched384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
open scoped BigOperators
open private Repair.nbr_add Repair.full_nbr Repair.omit_set from Repair384b
open private Graffiti384b.DiversityEleven.cubic_pair_nonadjacent from ThreeUntouched384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The 12-nonleaf independent-low case is exact. -/
theorem exact_twelve_independent (sup : Supported G)
    (t : (types G).card=11) (nine : (high G).card=9) (qc : (nonleaves G).card=12)
    (scores : Set.InjOn (trianglesAt G) (high G : Set V))
    (min : ∀ x∈high G,2≤trianglesAt G x)
    (ind : ∀ x∈nonleaves G \ high G,∀ y∈nonleaves G \ high G,¬G.Adj x y) :
    gamma G≤bound G := by
  classical
  let O := nonleaves G \ high G
  let N : V → Finset V := fun x=>G.neighborFinset x
  let P := O.biUnion N
  have low : Disjoint O (high G) :=
    Finset.disjoint_left.mpr (fun _ xo xh => (mem_sdiff.mp xo).2 xh)
  have sub : high G ⊆ nonleaves G := by
    intro x xh
    have d := (mem_filter.mp xh).2
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  have three : O.card=3 := by
    have c := card_sdiff_add_card_eq_card sub
    dsimp [O]; omega
  have deg (x : V) (xm : x∈O) : G.degree x=2 := by
    obtain ⟨xn,xh⟩ := mem_sdiff.mp xm
    have up : ¬3≤G.degree x := fun d => xh (mem_filter.mpr ⟨mem_univ _,d⟩)
    have down := (mem_filter.mp xn).2
    omega
  have nbr_nonleaf {x y : V} (xy : G.Adj x y) : y∈nonleaves G := by
    obtain ⟨z,xz,yz⟩ := sup xy
    have p : ({x,z} : Finset V)⊆N y := insert_subset ((G.mem_neighborFinset ..).mpr xy.symm)
      (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr yz))
    have d := card_le_card p
    rw [card_pair xz.ne,show (N y).card=G.degree y from card_neighborFinset_eq_degree ..] at d
    exact mem_filter.mpr ⟨mem_univ _,d⟩
  have anch (e : V) (eo : e∈O) : N e⊆high G := by
    intro x xm
    have ex := (G.mem_neighborFinset ..).mp xm
    by_contra x0
    exact ind e eo x (mem_sdiff.mpr ⟨nbr_nonleaf ex,x0⟩) ex
  have nc (e : V) (eo : e∈O) : (N e).card=2 := by
    rw [show (N e).card=G.degree e from card_neighborFinset_eq_degree ..,deg e eo]
  have touch : ∀ v∈high G,(∃ e∈O,G.Adj e v)→v∈P :=
    fun _ _ ⟨e,eo,ev⟩=>mem_biUnion.mpr ⟨e,eo,(G.mem_neighborFinset ..).mpr ev⟩
  by_cases cap : P.card≤5
  · exact exact_of_three_low_footprint_five G t nine scores min three.ge
      low (fun e eo=>(deg e eo).ge) ind touch cap
  have matchN : (O : Set V).PairwiseDisjoint N := by
    intro e eo f fo ef
    apply Finset.disjoint_left.mpr
    intro x xe xf
    let Q := (O.erase e).biUnion N
    have xo : x∈Q := mem_biUnion.mpr ⟨f,mem_erase.mpr ⟨ef.symm,fo⟩,xf⟩
    have ee : P=N e∪Q := by
      change O.biUnion N=N e∪(O.erase e).biUnion N
      rw [←biUnion_insert,insert_erase eo]
    have qr : Q.card≤4 := by
      have c := card_biUnion_le_card_mul (O.erase e) N 2
        (fun v vm=>(nc v (mem_of_mem_erase vm)).le)
      rw [card_erase_of_mem eo,three] at c
      exact c
    have i : 0<(N e∩Q).card := card_pos.mpr ⟨x,mem_inter.mpr ⟨xe,xo⟩⟩
    have eq := card_union_add_card_inter (N e) Q
    rw [←ee,nc e eo] at eq
    omega
  have pc : P.card=6 := by
    change (O.biUnion N).card=6
    rw [card_biUnion matchN]
    calc
      (∑ x ∈ O,(N x).card)=∑ _ ∈ O,2 := sum_congr rfl (fun x xm=>nc x xm)
      _=6 := by simp [three]
  have ph : P⊆high G := by
    intro x xm
    obtain ⟨e,eo,ex⟩ := mem_biUnion.mp xm
    exact anch e eo ex
  let U := (high G)\P
  have uc : U.card=3 := by
    change ((high G)\P).card=3
    rw [card_sdiff ph,nine,pc]
  have uh : U⊆high G := sdiff_subset
  have free (x : V) (xo : x∈O) (v : V) (vu : v∈U) : ¬G.Adj x v :=
    fun e => (mem_sdiff.mp vu).2 (touch v (uh vu) ⟨x,xo,e⟩)
  by_cases ready : ∀ v∈U,2+nbr G v U≤G.degree v
  · have dj : Disjoint O U := low.mono_right uh
    have om := Repair.omit_set G (O∪U) (by
      intro x xm
      have part := Repair.full_nbr G x (O∪U)
      rw [Repair.nbr_add G x dj] at part
      have nz (S : Finset V) (h : ∀ y∈S,¬G.Adj x y) : nbr G x S=0 := by
        rw [nbr,filter_eq_empty_iff.mpr h,card_empty]
      rcases mem_union.mp xm with xo|xu
      · have a := nz O (ind x xo)
        have b := nz U (free x xo)
        have d := deg x xo
        omega
      · have a := nz O (fun y yo h=>free y yo x xu h.symm)
        have b := ready x xu
        omega)
    have ca := card_union_of_disjoint dj
    unfold bound
    rw [t]
    omega
  push_neg at ready
  obtain ⟨x,xu,notg⟩ := ready
  let R := U.erase x
  have rc : R.card=2 := by rw [show R=U.erase x by rfl,card_erase_of_mem xu,uc]
  have ub : U.filter (G.Adj x)⊆R := by
    intro v vm
    exact mem_erase.mpr ⟨(mem_filter.mp vm).2.ne.symm,(mem_filter.mp vm).1⟩
  have ncx : nbr G x U≤2 := by
    have d := card_le_card ub
    rwa [rc] at d
  have dx : G.degree x=3 := by
    have d := (mem_filter.mp (uh xu)).2
    omega
  have cn : nbr G x U=2 := by omega
  have eq : U.filter (G.Adj x)=R := eq_of_subset_of_card_le ub (by rw [rc]; exact cn.ge)
  obtain ⟨y,z,yz,Ryz⟩ := card_eq_two.mp rc
  have yr : y∈R := Ryz ▸ mem_insert_self ..
  have zr : z∈R := Ryz ▸ mem_insert_of_mem (mem_singleton_self _)
  have yu := mem_of_mem_erase yr
  have zu := mem_of_mem_erase zr
  have xy : x≠y := (mem_erase.mp yr).1.symm
  have xz : x≠z := (mem_erase.mp zr).1.symm
  have xyA : G.Adj x y := (mem_filter.mp (eq ▸ yr)).2
  have xzA : G.Adj x z := (mem_filter.mp (eq ▸ zr)).2
  have hiOther (v : V) (vu : v∈U) (xv : x≠v) (edge : G.Adj x v) : 4≤G.degree v := by
    have dh := (mem_filter.mp (uh vu)).2
    by_contra! h
    have dv : G.degree v=3 := by omega
    exact Graffiti384b.DiversityEleven.cubic_pair_nonadjacent G dx dv (min x (uh xu)) (min v (uh vu))
      (fun e=>xv (scores (uh xu) (uh vu) e)) edge
  have n3 : (N x).card=3 := by rw [show (N x).card=G.degree x from card_neighborFinset_eq_degree ..,dx]
  have ns : ({y,z} : Finset V)⊆N x := insert_subset ((G.mem_neighborFinset ..).mpr xyA)
    (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr xzA))
  have ra : 0<((N x)\({y,z} : Finset V)).card := by
    rw [card_sdiff ns,n3,card_pair yz]
    decide
  obtain ⟨a,aa⟩ := card_pos.mp ra
  have an := (mem_sdiff.mp aa).1
  have av := (mem_sdiff.mp aa).2
  have a0 : a∉U := by
    intro au
    have F : a∈U.filter (G.Adj x) := mem_filter.mpr ⟨au,(G.mem_neighborFinset ..).mp an⟩
    rw [eq,Ryz] at F
    exact av F
  have ap : a∈P := by
    have aan := nbr_nonleaf ((G.mem_neighborFinset ..).mp an)
    have ao : a∉O := fun h=>free a h x xu ((G.mem_neighborFinset ..).mp an).symm
    have ah : a∈high G := Classical.byContradiction (fun h=>ao (mem_sdiff.mpr ⟨aan,h⟩))
    exact Classical.byContradiction (fun h=>a0 (mem_sdiff.mpr ⟨ah,h⟩))
  obtain ⟨e,eO,ae⟩ := mem_biUnion.mp ap
  have nx : N x={y,z,a} := by
    have hf : insert a ({y,z} : Finset V)⊆N x := insert_subset an ns
    have cf : (insert a ({y,z} : Finset V)).card=3 := by
      rw [card_insert_of_not_mem av,card_pair yz]
    have eq := eq_of_subset_of_card_le hf (by rw [cf,n3])
    have rearrange : insert a ({y,z} : Finset V)={y,z,a} := by
      ext w
      simp only [mem_insert,mem_singleton]
      tauto
    exact eq.symm.trans rearrange
  exact exact_of_three_matched_cubic_fallback G t three low deg anch matchN scores min
    xy xz yz (uh xu) (uh yu) (uh zu) (hiOther y yu xy xyA) (hiOther z zu xz xzA)
    eO ae nx (fun e eO => ⟨fun f=>free e eO x xu ((G.mem_neighborFinset ..).mp f),
      fun f=>free e eO y yu ((G.mem_neighborFinset ..).mp f),
      fun f=>free e eO z zu ((G.mem_neighborFinset ..).mp f)⟩)

#print axioms exact_twelve_independent
end Graffiti384b.DiversityEleven
