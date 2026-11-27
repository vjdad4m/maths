import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Lattice

/-! AutoGraphForge physical row 1160. GraphCalc computes the annihilation
number by taking the longest ascending degree prefix of sum at most |E|. -/
namespace CubicBridges1160
open SimpleGraph Finset
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

noncomputable def cliqueCover := sInf {k : ℕ | Gᶜ.Colorable k}
def TriangleFree := ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a

noncomputable def ascending [DecidableRel G.Adj] :=
  (univ.val.map (fun v => G.degree v)).sort (· ≤ ·)

noncomputable def annihilation [DecidableRel G.Adj] :=
  ((range (Fintype.card V+1)).filter (fun t => ((ascending G).take t).sum ≤ G.edgeFinset.card)).sup id

theorem regular_annihilation [DecidableRel G.Adj] {d : ℕ} (hd : 0 < d)
    (reg : G.IsRegularOfDegree d) : annihilation G = Fintype.card V / 2 := by
  classical
  let n := Fintype.card V
  have regular (v : V) : G.degree v = d := reg v
  have seq : ascending G = List.replicate n d := by
    apply List.eq_replicate_iff.mpr
    constructor
    · simp [ascending,n]
    · intro b hb
      obtain ⟨v,_,e⟩ := Multiset.mem_map.mp ((Multiset.mem_sort _).mp hb)
      exact e.symm.trans (regular v)
  have handshake : n*d = 2*G.edgeFinset.card := by
    simpa only [regular,sum_const,card_univ,smul_eq_mul,n] using G.sum_degrees_eq_twice_card_edges
  have budget (t : ℕ) (ht : t≤n) :
      ((ascending G).take t).sum ≤ G.edgeFinset.card ↔ 2*t ≤ n := by
    rw [seq,List.take_replicate,min_eq_left ht,List.sum_replicate_nat]
    constructor
    · intro h
      apply Nat.le_of_mul_le_mul_right (c := d) _ hd
      calc
        (2*t)*d = 2*(t*d) := Nat.mul_assoc _ _ _
        _ ≤ 2*G.edgeFinset.card := Nat.mul_le_mul_left _ h
        _ = n*d := handshake.symm
    · intro h
      have hh := Nat.mul_le_mul_right d h
      rw [Nat.mul_assoc,handshake] at hh
      omega
  apply le_antisymm
  · apply Finset.sup_le
    intro t ht
    obtain ⟨hr,hh⟩ := mem_filter.mp ht
    have hn : t ≤ n := Nat.le_of_lt_succ (mem_range.mp hr)
    have := (budget t hn).mp hh
    change t ≤ n/2
    omega
  · apply le_sup (f:=id)
    apply mem_filter.mpr
    exact ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_self n 2)),
      (budget _ (Nat.div_le_self n 2)).mpr (by omega)⟩

omit [Fintype V] in
/-- A class of a proper complement coloring is a clique in G. -/
theorem adj_of_same {K : Type*} (col : Gᶜ.Coloring K) {a b : V}
    (ne : a ≠ b) (same : col a=col b) : G.Adj a b := by
  by_contra no
  exact col.valid ((G.compl_adj _ _).mpr ⟨ne,no⟩) same

theorem fiber_small (ht : TriangleFree G) {K : Type*} [DecidableEq K]
    (col : Gᶜ.Coloring K) (i : K) : (univ.filter (fun v => col v=i)).card ≤ 2 := by
  by_contra! bad
  obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := two_lt_card_iff.mp bad
  have ea := (mem_filter.mp ha).2
  have eb := (mem_filter.mp hb).2
  have ec := (mem_filter.mp hc).2
  exact ht a b c (adj_of_same G col ab (ea.trans eb.symm))
    (adj_of_same G col bc (eb.trans ec.symm)) (adj_of_same G col ac.symm (ec.trans ea.symm))

theorem cover_attained : Gᶜ.Colorable (cliqueCover G) :=
  Nat.sInf_mem (s := {k | Gᶜ.Colorable k}) ⟨_,Gᶜ.colorable_of_fintype⟩

/-- A coloring at the half-order bound must use exactly two vertices per class. -/
theorem perfect_of_half (ht : TriangleFree G) (bound : cliqueCover G ≤ Fintype.card V/2) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  classical
  obtain ⟨c⟩ := cover_attained G
  let F (i : Fin (cliqueCover G)) := univ.filter (fun x => c x=i)
  have two (i) : (F i).card ≤ 2 := fiber_small G ht c i
  have count : Fintype.card V = ∑ i, (F i).card :=
    card_eq_sum_card_fiberwise (s:=univ) (t:=univ) (f:=fun v : V => c v) (by simp)
  have reverse : (∑ _ : Fin (cliqueCover G), 2 : ℕ) ≤ ∑ i, (F i).card := by
    rw [← count]
    simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul]
    omega
  have exactTwo (i) : (F i).card = 2 := (sum_eq_sum_iff_of_le (fun j _ => two j)).mp
    (le_antisymm (sum_le_sum (fun j _ => two j)) reverse) i (mem_univ i)
  let M : G.Subgraph := {
    verts := Set.univ
    Adj := fun a b => G.Adj a b ∧ c a=c b
    adj_sub := fun e => e.1
    edge_vert := fun _ => Set.mem_univ _
    symm := fun _ _ h => ⟨h.1.symm,h.2.symm⟩ }
  refine ⟨M,Subgraph.isPerfectMatching_iff.mpr ?_⟩
  intro x
  obtain ⟨a,b,ne,ef⟩ := card_eq_two.mp (exactTwo (c x))
  have members (v : V) : c v=c x ↔ v=a ∨ v=b := by
    change (_ ↔ _)
    have h : v ∈ F (c x) ↔ v=a ∨ v=b := by rw [ef]; simp
    simpa [F] using h
  have pair := (members a).mpr (Or.inl rfl) |>.trans ((members b).mpr (Or.inr rfl)).symm
  have ab : M.Adj a b := ⟨adj_of_same G c ne pair,pair⟩
  rcases (members x).mp rfl with xa|xb
  · refine ⟨b,xa ▸ ab,?_⟩
    intro y xy
    exact ((members y).mp xy.2.symm).resolve_left (fun e => xy.1.ne (xa.trans e.symm))
  · refine ⟨a,xb ▸ M.symm ab,?_⟩
    intro y xy
    exact ((members y).mp xy.2.symm).resolve_right (fun e => xy.1.ne (xb.trans e.symm))

/-- The edges of a perfect matching form a clique partition of half the order. -/
theorem half_of_perfect {M : G.Subgraph} (hm : M.IsPerfectMatching) :
    cliqueCover G ≤ Fintype.card V/2 := by
  classical
  let E := M.spanningCoe.edgeFinset
  choose partner edge _ using (Subgraph.isPerfectMatching_iff.mp hm)
  let slot (v : V) : ↥E := ⟨s(v,partner v), (M.spanningCoe.mem_edgeFinset).mpr (edge v)⟩
  have proper {x y : V} (e : Gᶜ.Adj x y) : slot x ≠ slot y := by
    intro same
    obtain ⟨ne,no⟩ := (G.compl_adj _ _).mp e
    rcases Sym2.eq_iff.mp (congrArg Subtype.val same) with h|h
    · exact ne h.1
    · exact no (h.2 ▸ M.adj_sub (edge x))
  let coloring : Gᶜ.Coloring ↥E := Coloring.mk slot proper
  have degree (v : V) : M.spanningCoe.degree v = 1 := by
    rw [Subgraph.degree_spanningCoe]
    exact (Subgraph.isPerfectMatching_iff_forall_degree.mp hm) v
  have card := M.spanningCoe.sum_degrees_eq_twice_card_edges
  simp only [degree,sum_const,card_univ,smul_eq_mul,mul_one] at card
  have colorable : Gᶜ.Colorable E.card := by simpa using coloring.colorable
  apply (Nat.sInf_le colorable).trans
  change M.spanningCoe.edgeFinset.card ≤ Fintype.card V/2
  omega

theorem regular_triangleFree_criterion [DecidableRel G.Adj] {d : ℕ}
    (hd : 0<d) (reg : G.IsRegularOfDegree d) (ht : TriangleFree G) :
    cliqueCover G ≤ annihilation G ↔ ∃ M : G.Subgraph, M.IsPerfectMatching := by
  rw [regular_annihilation G hd reg]
  exact ⟨perfect_of_half G ht,fun ⟨_,h⟩ => half_of_perfect G h⟩

#print axioms regular_annihilation
#print axioms regular_triangleFree_criterion
end CubicBridges1160
