import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-! Ján Pastorek's AutoGraphForge, pinned normalized row 373.
Lines 373 and 1221 are direct formalizations of consequences of known graph-family
formulas: Hogben, Lin and Shader, Theorem 9.44 (doi:10.1090/surv/270).
The power-domination model is the published maths repository's line 66 definition. -/
namespace AutoGraphPowerBurning
inductive Observed {V : Type*} (G : SimpleGraph V) (S : Finset V) : V → Prop where
  | root {v} (h : v ∈ S) : Observed G S v
  | neighbor {v w} (h : w ∈ S) (hvw : G.Adj v w) : Observed G S v
  | force {v w} (hvw : G.Adj v w) (hw : Observed G S w)
      (rest : ∀ u, G.Adj w u → u ≠ v → Observed G S u) : Observed G S v

noncomputable def power {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ S : Finset V, n = S.card ∧ ∀ v, Observed G S v}
end AutoGraphPowerBurning

namespace AutoGraphForge373
open SimpleGraph Finset AutoGraphPowerBurning
open Classical
noncomputable section
variable {V : Type*} (G : SimpleGraph V)

/-- Same predicate as upstream IsCographClass and published line 378. -/
def Cograph := ∀ a b c d : V, G.Adj a b → G.Adj b c → G.Adj c d →
  ¬G.Adj a c → ¬G.Adj b d → G.Adj a d

/-- Two vertices in the same component of the induced white graph. -/
def WhiteConnected (B : Set V) (a b : V) : Prop :=
  ∃ (ha : a ∉ B) (hb : b ∉ B),
    (G.induce Bᶜ).Reachable ⟨a, ha⟩ ⟨b, hb⟩

def step (B : Set V) : Set V := {w | w ∈ B ∨ w ∉ B ∧ ∃ v ∈ B, G.Adj v w ∧
  ∀ u, G.Adj v u → WhiteConnected G B w u → u = w}

def round (S : Finset V) : ℕ → Set V
  | 0 => ↑S
  | n+1 => step G (round S n)

def PSDSet (S : Finset V) : Prop := ∃ n, ∀ v, v ∈ round G S n

def psd : ℕ := sInf {n | ∃ S : Finset V, n = S.card ∧ PSDSet G S}

def DominatesAt (D : Finset V) (v : V) : Prop := v ∈ D ∨ ∃ d ∈ D, G.Adj d v

private theorem has_seed {S : Finset V} {v : V} {n : ℕ} (hv : v ∈ round G S n) :
    ∃ s ∈ S, G.Reachable s v := by
  induction n generalizing v with
  | zero => exact ⟨v,hv,.refl v⟩
  | succ n ih =>
    rcases hv with h | ⟨_,u,hu,uv,_⟩
    · exact ih h
    · obtain ⟨s,hs,r⟩ := ih hu
      exact ⟨s,hs,r.trans uv.reachable⟩

private theorem white_two {B : Set V} {u a w : V}
    (hu : u ∉ B) (ha : a ∉ B) (hw : w ∉ B) (e : G.Adj u a) (f : G.Adj a w) :
    WhiteConnected G B u w :=
  ⟨hu, hw, (show (G.induce Bᶜ).Adj ⟨u,hu⟩ ⟨a,ha⟩ from e).reachable.trans
    (show (G.induce Bᶜ).Adj ⟨a,ha⟩ ⟨w,hw⟩ from f).reachable⟩

/-- In a bipartite cograph every three-edge walk closes up. -/
def Rectangle := ∀ ⦃a b c d : V⦄, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj a d

private theorem rectangle_of_bipartite
    (bip : Nonempty (G →g (⊤ : SimpleGraph (Fin 2)))) (cg : Cograph G) : Rectangle G := by
  obtain ⟨c⟩ := bip
  have tri {x y z : V} (a : G.Adj x y) (b : G.Adj y z) (d : G.Adj x z) : False := by
    have i : c x ≠ c y := c.map_adj a
    have j : c y ≠ c z := c.map_adj b
    have k : c x ≠ c z := c.map_adj d
    omega
  exact fun a b c d ab bc cd => cg a b c d ab bc cd (tri ab bc) (tri bc cd)

/-- The endpoints of any edge dominate its component. -/
private theorem edge_dominates (rect : Rectangle G) {s b v : V} (sb : G.Adj s b)
    (rv : G.Reachable v s) : G.Adj s v ∨ G.Adj b v := by
  have along {x y : V} (p : G.Walk x y) (h : G.Adj s y ∨ G.Adj b y) :
      G.Adj s x ∨ G.Adj b x := by
    induction p with
    | nil => exact h
    | cons e _ ih =>
      rcases ih h with h | h
      · exact Or.inr (rect sb.symm h e.symm)
      · exact Or.inl (rect sb h e.symm)
  exact along rv.some (Or.inr sb.symm)

/-- A component seeded only at s cannot start PSD forcing if s has two neighbors
and another vertex is adjacent to every neighbor of s. -/
private theorem singleton_blocked {S : Finset V} {s b c a : V}
    (only : ∀ x ∈ S, G.Reachable x s → x = s)
    (sb : G.Adj s b) (sc : G.Adj s c) (bc : b ≠ c) (as' : a ≠ s)
    (twins : ∀ w, G.Adj s w → G.Adj a w) : ¬PSDSet G S := by
  have stuck (n : ℕ) : ∀ v ∈ round G S n, G.Reachable v s → v = s := by
    induction n with
    | zero => exact only
    | succ n ih =>
      intro v hv r
      rcases hv with old | ⟨white, z, hz, zv, unique⟩
      · exact ih v old r
      · have zs := ih z hz (zv.reachable.trans r)
        subst z
        obtain ⟨u, su, ne⟩ : ∃ u, G.Adj s u ∧ u ≠ v := by
          by_cases h : b = v
          · exact ⟨c,sc,h ▸ bc.symm⟩
          · exact ⟨b,sb,h⟩
        have uw : u ∉ round G S n := fun h => su.ne' (ih u h su.symm.reachable)
        have aw : a ∉ round G S n :=
          fun h => as' (ih a h ((twins v zv).reachable.trans r))
        exact (ne (unique u su (white_two G white aw uw (twins v zv).symm (twins u su)))).elim
  rintro ⟨n,all⟩
  exact sb.ne' (stuck n b (all b) sb.symm.reachable)

private theorem local_dominating (rect : Rectangle G) {S : Finset V} (full : PSDSet G S)
    (C : G.ConnectedComponent) :
    ∃ D : Finset V, D.card ≤ (S.filter (fun v => G.connectedComponentMk v = C)).card ∧
      ∀ v, G.connectedComponentMk v = C → DominatesAt G D v := by
  classical
  induction C using ConnectedComponent.ind with
  | h x =>
    obtain ⟨n,all⟩ := full
    obtain ⟨s,hs,rs⟩ := has_seed G (all x)
    let A := S.filter (fun v => G.connectedComponentMk v = G.connectedComponentMk x)
    change ∃ D : Finset V, D.card ≤ A.card ∧ _
    have sa : s ∈ A := mem_filter.mpr ⟨hs,ConnectedComponent.sound rs⟩
    have one : 1 ≤ A.card := card_pos.mpr ⟨s,sa⟩
    have reach {v} (h : G.connectedComponentMk v = G.connectedComponentMk x) :
        G.Reachable v s := (ConnectedComponent.exact h).trans rs.symm
    by_cases edge : ∃ b, G.Adj s b
    · obtain ⟨b,sb⟩ := edge
      have dom {v} (h : G.connectedComponentMk v = G.connectedComponentMk x) :=
        edge_dominates G rect sb (reach h)
      by_cases two : 2 ≤ A.card
      · refine ⟨{s,b}, ?_, ?_⟩
        · simpa [sb.ne] using two
        · intro v h
          rcases dom h with adj | adj
          · exact Or.inr ⟨s, by simp, adj⟩
          · exact Or.inr ⟨b, by simp, adj⟩
      have only (u) (hu : u ∈ S) (r : G.Reachable u s) : u = s := by
        have ua : u ∈ A := mem_filter.mpr ⟨hu,ConnectedComponent.sound (r.trans rs)⟩
        apply Classical.byContradiction
        intro ne
        have sub : {u,s} ⊆ A := insert_subset ua (singleton_subset_iff.mpr sa)
        have lo := card_le_card sub
        simp [ne] at lo
        omega
      by_cases extraS : ∃ c, G.Adj s c ∧ b ≠ c
      · obtain ⟨c,sc,bc⟩ := extraS
        have singleB (a) (ba : G.Adj b a) : a = s := by
          apply Classical.byContradiction
          intro ne
          exact singleton_blocked G only sb sc bc ne (fun w sw => rect ba.symm sb.symm sw) ⟨n,all⟩
        refine ⟨{s}, by simpa using one, ?_⟩
        intro v h
        rcases dom h with sv | bv
        · exact Or.inr ⟨s,by simp,sv⟩
        · exact Or.inl (mem_singleton.mpr (singleB _ bv))
      · refine ⟨{b}, by simpa using one, ?_⟩
        intro v h
        rcases dom h with sv | bv
        · exact Or.inl (mem_singleton.mpr (by
            apply Classical.byContradiction
            intro ne
            exact extraS ⟨v,sv,fun e => ne e.symm⟩))
        · exact Or.inr ⟨b,by simp,bv⟩
    · refine ⟨{s}, by simpa using one, ?_⟩
      intro v h
      obtain ⟨p⟩ := (reach h).symm
      cases p with
      | nil => exact Or.inl (by simp)
      | cons e _ => exact (edge ⟨_,e⟩).elim

/-- Every PSD seed set in a bipartite cograph pays for an ordinary dominating set. -/
theorem dominating_of_psd [Fintype V] (rect : Rectangle G) {S : Finset V} (full : PSDSet G S) :
    ∃ D : Finset V, D.card ≤ S.card ∧ ∀ v, DominatesAt G D v := by
  classical
  let classes := (univ : Finset V).image G.connectedComponentMk
  choose D sizes dominates using local_dominating G rect full
  refine ⟨classes.biUnion D, card_biUnion_le.trans ((sum_le_sum (fun c _ => sizes c)).trans ?_), ?_⟩
  · exact (card_eq_sum_card_fiberwise (f := G.connectedComponentMk) (s := S) (t := classes)
      (fun v _ => mem_image_of_mem _ (mem_univ v))).symm.le
  · intro v
    have c := mem_image_of_mem G.connectedComponentMk (mem_univ v)
    rcases dominates (G.connectedComponentMk v) v rfl with here | ⟨s,hs,e⟩
    · exact Or.inl (mem_biUnion.mpr ⟨_,c,here⟩)
    · exact Or.inr ⟨s,mem_biUnion.mpr ⟨_,c,hs⟩,e⟩

private theorem power_le_psd [Fintype V] (rect : Rectangle G) : power G ≤ psd G := by
  classical
  have all : {n | ∃ S : Finset V, n = S.card ∧ PSDSet G S}.Nonempty :=
    ⟨_,univ,rfl,0,fun v => mem_univ v⟩
  obtain ⟨S,cost,full⟩ := Nat.sInf_mem all
  obtain ⟨D,le,dom⟩ := dominating_of_psd G rect full
  change psd G = S.card at cost
  rw [cost]
  apply le_trans _ le
  apply Nat.sInf_le
  refine ⟨D,rfl,?_⟩
  intro v
  rcases dom v with h | ⟨s,hs,e⟩
  · exact .root h
  · exact .neighbor hs e.symm

theorem row373 [Fintype V] (_nontrivial : 2 ≤ Fintype.card V)
    (bip : Nonempty (G →g (⊤ : SimpleGraph (Fin 2)))) (cg : Cograph G) :
    power G ≤ psd G :=
  power_le_psd G (rectangle_of_bipartite G bip cg)

#print axioms dominating_of_psd
#print axioms row373

/-- In a forest a black vertex cannot see two distinct white neighbors in the
same white component. Otherwise its edge to the first neighbor is not a bridge. -/
private theorem forest_unique (forest : G.IsAcyclic) {B : Set V} {v w u : V}
    (black : v ∈ B) (vw : G.Adj v w) (vu : G.Adj v u) (same : WhiteConnected G B w u) :
    u = w := by
  classical
  apply Classical.byContradiction
  intro different
  obtain ⟨hw,hu,ru⟩ := same
  let H := G \ fromEdgeSet {s(v,w)}
  have edge {a b : V} (ab : G.Adj a b) (ne : s(a,b) ≠ s(v,w)) : H.Adj a b := by
    exact ⟨ab,fun q => ne (((fromEdgeSet_adj _).mp q).1)⟩
  let embed : (G.induce Bᶜ) →g H :=
    ⟨Subtype.val, fun {a b} ab => edge ab (by
      intro eq
      rcases Sym2.eq_iff.mp eq with h | h
      · exact a.property (h.1.symm ▸ black)
      · exact b.property (h.2.symm ▸ black))⟩
  have other : H.Adj v u := edge vu (by
    intro eq
    rcases Sym2.eq_iff.mp eq with h | h
    · exact different h.2
    · exact vw.ne h.1)
  exact (isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp forest vw)).2
    (other.reachable.trans (ru.map embed).symm)

private theorem forest_adj_step (forest : G.IsAcyclic) {B : Set V} {v w : V}
    (black : v ∈ B) (vw : G.Adj v w) : w ∈ step G B := by
  classical
  by_cases hw : w ∈ B
  · exact Or.inl hw
  · exact Or.inr ⟨hw,v,black,vw,fun _ => forest_unique G forest black vw⟩

private theorem forest_reaches (forest : G.IsAcyclic) {S : Finset V} {s v : V}
    (hs : s ∈ S) (r : G.Reachable v s) : ∃ n, v ∈ round G S n := by
  have along {x y : V} (p : G.Walk x y) (hy : ∃ n, y ∈ round G S n) :
      ∃ n, x ∈ round G S n := by
    induction p with
    | nil => exact hy
    | cons e _ ih =>
      obtain ⟨n,h⟩ := ih hy
      exact ⟨n+1,forest_adj_step G forest h e.symm⟩
  exact along r.some ⟨0,hs⟩

private theorem uniform [Fintype V] {S : Finset V} (h : ∀ v, ∃ n, v ∈ round G S n) :
    PSDSet G S := by
  classical
  choose t ht using h
  have mono : Monotone (round G S) := monotone_nat_of_le_succ (fun _ _ hx => Or.inl hx)
  exact ⟨univ.sup t,fun v => mono (le_sup (s := univ) (f := t) (mem_univ v)) (ht v)⟩

/-- Barioli et al., Zero forcing parameters and minimum rank problems, §3:
every vertex by itself PSD-forces a finite tree. -/
theorem tree_psd_one [Fintype V] (tree : G.IsTree) : psd G = 1 := by
  classical
  obtain ⟨s⟩ := tree.isConnected.nonempty
  have full : PSDSet G {s} := uniform G (fun v =>
    forest_reaches G tree.IsAcyclic (mem_singleton_self s) (tree.isConnected.preconnected v s))
  have ex : {n | ∃ S : Finset V, n = S.card ∧ PSDSet G S}.Nonempty :=
    ⟨_,{s},rfl,full⟩
  obtain ⟨A,cost,n,all⟩ := Nat.sInf_mem ex
  change psd G = A.card at cost
  have pos : 1 ≤ psd G := by
    obtain ⟨a,ha,_⟩ := has_seed G (all s)
    rw [cost]
    exact card_pos.mpr ⟨a,ha⟩
  exact Nat.le_antisymm (Nat.sInf_le (show ∃ S : Finset V, 1 = S.card ∧ PSDSet G S
    from ⟨{s},by simp,full⟩)) pos

private theorem seed_of_observed {S : Finset V} {v : V} (h : Observed G S v) : S.Nonempty := by
  induction h with
  | root hv => exact ⟨_,hv⟩
  | neighbor hs _ => exact ⟨_,hs⟩
  | force _ _ _ h _ => exact h

/-- On the exact cograph-tree domain both parameters are one. -/
theorem cograph_tree_values [Fintype V] (cg : Cograph G) (tree : G.IsTree) :
    power G = 1 ∧ psd G = 1 := by
  classical
  have tri {a b c : V} (ab : G.Adj a b) (bc : G.Adj b c) (ac : G.Adj a c) : False := by
    let B : Set V := {b}
    have aw : a ∉ B := ab.ne
    have cw : c ∉ B := bc.ne'
    have same : WhiteConnected G B a c :=
      ⟨aw,cw,(show (G.induce Bᶜ).Adj ⟨a,aw⟩ ⟨c,cw⟩ from ac).reachable⟩
    exact ac.ne' (forest_unique G tree.IsAcyclic (B := B) rfl ab.symm bc same)
  have rect : Rectangle G := fun a b c d ab bc cd => cg a b c d ab bc cd (tri ab bc) (tri bc cd)
  have one := tree_psd_one G tree
  have hi := (power_le_psd G rect).trans one.le
  have ex : {n | ∃ S : Finset V, n = S.card ∧ ∀ v, Observed G S v}.Nonempty :=
    ⟨_,univ,rfl,fun v => .root (mem_univ v)⟩
  obtain ⟨S,cost,full⟩ := Nat.sInf_mem ex
  change power G = S.card at cost
  obtain ⟨v⟩ := tree.isConnected.nonempty
  exact ⟨Nat.le_antisymm hi (cost.symm ▸ card_pos.mpr (seed_of_observed G (full v))),one⟩

theorem row1221 [Fintype V] (_nontrivial : 2 ≤ Fintype.card V) (cg : Cograph G)
    (tree : G.IsTree) : psd G = power G := by
  obtain ⟨p,z⟩ := cograph_tree_values G cg tree
  exact z.trans p.symm

#print axioms tree_psd_one
#print axioms cograph_tree_values
#print axioms row1221

end
end AutoGraphForge373
