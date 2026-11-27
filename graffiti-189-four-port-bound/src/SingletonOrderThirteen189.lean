import SingleTwoBounds189

namespace Graffiti189LongestPath.FourCut.Three
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {r a b : V}
variable (S : SingleRoot G r a b)
set_option linter.unusedSectionVars false

lemma inner_dist_mk {x y : V} (xi : x∈S.inner) (xy : G.Adj x y) :
    (G.Adj a y → x∈DistanceTwo G a) ∧ (G.Adj b y → x∈DistanceTwo G b) := by
  obtain ⟨off,na,nb⟩ := S.mem_inner.mp xi
  obtain ⟨_,xa,xb⟩ := S.mem_off3.mp off
  exact ⟨fun ay=> Sides.mem_d2.mpr (Sides.dist_two S.con xa.symm na ay xy.symm),
    fun by'=> Sides.mem_d2.mpr (Sides.dist_two S.con xb.symm nb by' xy.symm)⟩

lemma shell_three_with_reserve (i : V) {v : V}
    (vs : v∈DistanceTwo G i) (vi : v∉S.inner) :
    (S.inner.filter (· ∈ DistanceTwo G i)).card≤3 := by
  have no : v∉S.inner.filter (· ∈ DistanceTwo G i) := fun h=>vi (mem_filter.mp h).1
  have sub : insert v (S.inner.filter (· ∈ DistanceTwo G i)) ⊆ DistanceTwo G i :=
    insert_subset_iff.mpr ⟨vs,fun _ h=>(mem_filter.mp h).2⟩
  have le := (card_le_card sub).trans (distanceTwo_le_of_even 4 i (S.even i))
  rw [card_insert_of_not_mem no] at le
  omega

/-- The upper finite order is already impossible structurally when
each separator has its own exclusive port. -/
theorem no_order_thirteen_explicit (four : S.ports.card=4)
    (order : Fintype.card V=13) {p q c d : V}
    (ports : S.ports={p,q,c,d}) (pq : p≠q) (pc : p≠c) (qc : q≠c)
    (ap : G.Adj a p) (nBp : ¬G.Adj b p)
    (bq : G.Adj b q) (nAq : ¬G.Adj a q)
    (ac : G.Adj a c) (bc : G.Adj b c)
    (ad : G.Adj a d) (bd : G.Adj b d)
    (de : 4≤G.degree c) : False := by
  classical
  let IA := S.inner.filter (· ∈ DistanceTwo G a)
  let IB := S.inner.filter (· ∈ DistanceTwo G b)
  have total := S.total_card four
  have six : S.inner.card=6 := by omega
  have up : p∈S.ports := by simp [ports]
  have uq : q∈S.ports := by simp [ports]
  have uc : c∈S.ports := by simp [ports]
  have ud : d∈S.ports := by simp [ports]
  have po (z : V) (hz : z∈S.ports) : z≠r ∧ z≠a ∧ z≠b :=
    S.mem_off3.mp (mem_filter.mp hz).1
  have ni (z : V) (hz : z∈S.ports) : z∉S.inner :=
    fun e=>(mem_sdiff.mp e).2 hz
  have na : a∉S.inner := fun h=>(S.mem_off3.mp (S.mem_inner.mp h).1).2.1 rfl
  have nb : b∉S.inner := fun h=>(S.mem_off3.mp (S.mem_inner.mp h).1).2.2 rfl
  have caps : IA.card≤3 ∧ IB.card≤3 := by
    by_cases e : G.Adj a b
    · exact ⟨shell_three_with_reserve S a (Sides.mem_d2.mpr (Sides.dist_two S.con (po q uq).2.1.symm
        nAq e bq)) (ni q uq),
        shell_three_with_reserve S b (Sides.mem_d2.mpr (Sides.dist_two S.con (po p up).2.2.symm
        nBp e.symm ap)) (ni p up)⟩
    · exact ⟨shell_three_with_reserve S a (Sides.mem_d2.mpr (Sides.dist_two S.con S.ab
        e S.left.symm S.right)) nb,
        shell_three_with_reserve S b (Sides.mem_d2.mpr (Sides.dist_two S.con S.ab.symm
        (fun e'=>e e'.symm) S.right.symm S.left)) na⟩
  have eq : IA∪IB=S.inner := by
    ext v
    simp only [IA,IB,mem_union,mem_filter]
    exact ⟨fun h=>h.elim And.left And.left,fun h=>(S.inner_cover four h).elim
      (fun d=>Or.inl ⟨h,d⟩) (fun d=>Or.inr ⟨h,d⟩)⟩
  have eqc := card_union_add_card_inter IA IB
  rw [eq,six] at eqc
  have sz : IA.card=3 ∧ IB.card=3 := by omega
  have dz : Disjoint IA IB := by
    apply disjoint_iff_inter_eq_empty.mpr
    exact card_eq_zero.mp (by omega)
  have noc (v : V) (vi : v∈S.inner) (z : V) (za : G.Adj a z) (zb : G.Adj b z) :
      ¬G.Adj v z := fun e => (disjoint_left.mp dz)
        (mem_filter.mpr ⟨vi,(inner_dist_mk S vi e).1 za⟩)
        (mem_filter.mpr ⟨vi,(inner_dist_mk S vi e).2 zb⟩)
  have every (v : V) (vi : v∈S.inner) : G.Adj v p ∨ G.Adj v q := by
    obtain ⟨z,zp,vz⟩ := S.adjacent_to_port four vi
    rw [ports] at zp
    simp only [mem_insert,mem_singleton] at zp
    rcases zp with rfl|rfl|rfl|rfl
    · exact Or.inl vz
    · exact Or.inr vz
    · exact (noc v vi _ ac bc vz).elim
    · exact (noc v vi _ ad bd vz).elim
  have iap (v : V) (vI : v∈IA) : G.Adj v p := by
    have vi := (mem_filter.mp vI).1
    exact (every v vi).resolve_right (fun e => disjoint_left.mp dz vI
      (mem_filter.mpr ⟨vi,(inner_dist_mk S vi e).2 bq⟩))
  have ibq (v : V) (vI : v∈IB) : G.Adj v q := by
    have vi := (mem_filter.mp vI).1
    exact (every v vi).resolve_left (fun e => disjoint_left.mp dz
      (mem_filter.mpr ⟨vi,(inner_dist_mk S vi e).1 ap⟩) vI)
  have reserves (u : V) (ou : u∈S.inner) (edge : G.Adj c p) (up' : G.Adj u p) :
      u∈DistanceTwo G c := Sides.mem_d2.mpr (Sides.dist_two S.con
        (fun e=>ni c uc (e.symm ▸ ou)) (fun e=>noc u ou c ac bc e.symm) edge up'.symm)
  have reservesB (u : V) (ou : u∈S.inner) (edge : G.Adj c q) (uq' : G.Adj u q) :
      u∈DistanceTwo G c := Sides.mem_d2.mpr (Sides.dist_two S.con
        (fun e=>ni c uc (e.symm ▸ ou)) (fun e=>noc u ou c ac bc e.symm) edge uq'.symm)
  have capsC := distanceTwo_le_of_even 4 c (S.even c)
  have cr : r∈DistanceTwo G c := Sides.mem_d2.mpr (Sides.dist_two S.con
    (po c uc).1 (fun e=>(S.only c e.symm).elim (po c uc).2.1 (po c uc).2.2) ac.symm S.left.symm)
  have rI : r∉S.inner := fun h=>(S.mem_off3.mp (S.mem_inner.mp h).1).1 rfl
  by_cases cp : G.Adj c p
  · by_cases cq : G.Adj c q
    · have sub : S.inner ⊆ DistanceTwo G c := by
        rw [←eq]
        exact union_subset (fun u h=>reserves u (mem_filter.mp h).1 cp (iap u h))
          (fun u h=>reservesB u (mem_filter.mp h).1 cq (ibq u h))
      have hh := card_le_card sub
      omega
    have qD : q∈DistanceTwo G c := Sides.mem_d2.mpr
      (Sides.dist_two S.con qc.symm cq bc.symm bq)
    have qI : q∉IA := fun h=>ni q uq (mem_filter.mp h).1
    have rIA : r∉insert q IA := by
      exact mt mem_insert.mp (fun h => h.elim (po q uq).1.symm (fun h => rI (mem_filter.mp h).1))
    have sub : insert r (insert q IA) ⊆ DistanceTwo G c :=
      insert_subset_iff.mpr ⟨cr,insert_subset_iff.mpr
        ⟨qD,fun u h=>reserves u (mem_filter.mp h).1 cp (iap u h)⟩⟩
    have hh := card_le_card sub
    rw [card_insert_of_not_mem rIA,card_insert_of_not_mem qI,sz.1] at hh
    omega
  · by_cases cq : G.Adj c q
    · have pD : p∈DistanceTwo G c := Sides.mem_d2.mpr
        (Sides.dist_two S.con pc.symm cp ac.symm ap)
      have pI : p∉IB := fun h=>ni p up (mem_filter.mp h).1
      have rIB : r∉insert p IB := by
        exact mt mem_insert.mp (fun h => h.elim (po p up).1.symm (fun h => rI (mem_filter.mp h).1))
      have sub : insert r (insert p IB) ⊆ DistanceTwo G c :=
        insert_subset_iff.mpr ⟨cr,insert_subset_iff.mpr
          ⟨pD,fun u h=>reservesB u (mem_filter.mp h).1 cq (ibq u h)⟩⟩
      have hh := card_le_card sub
      rw [card_insert_of_not_mem rIB,card_insert_of_not_mem pI,sz.2] at hh
      omega
    have ns : G.neighborFinset c ⊆ ({a,b,d}:Finset V) := by
      intro u hu
      have cu := (G.mem_neighborFinset _ _).mp hu
      by_cases ua : u=a
      · simp [ua]
      by_cases ub : u=b
      · simp [ub]
      by_cases ur : u=r
      · exact ((S.only c (ur ▸ cu.symm)).elim (po c uc).2.1 (po c uc).2.2).elim
      have off := S.mem_off3.mpr ⟨ur,ua,ub⟩
      by_cases m : u∈S.ports
      · rw [ports] at m
        simp only [mem_insert,mem_singleton] at m
        rcases m with rfl|rfl|rfl|rfl
        · exact (cp cu).elim
        · exact (cq cu).elim
        · exact (G.loopless _ cu).elim
        · simp
      · exact (noc u (mem_sdiff.mpr ⟨off,m⟩) c ac bc cu.symm).elim
    have h := card_le_card ns
    rw [card_neighborFinset_eq_degree] at h
    have h1 := card_insert_le a ({b,d}:Finset V)
    have h2 := card_insert_le b ({d}:Finset V)
    simp only [card_singleton] at h2
    omega
#print axioms no_order_thirteen_explicit
end Graffiti189LongestPath.FourCut.Three
