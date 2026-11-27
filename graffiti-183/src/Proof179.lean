import Short177
import Proof177
import Proof169

/-! # Graffiti.pc #179, displayed minimum-degree reading
The needed special cases of DeLaViña–Waller’s leaf bounds are formalized here. -/

/-! ## Domination bounds -/

namespace Graffiti179
open Finset SimpleGraph Short177
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def IsDom (S : Finset V) : Prop :=
  ∀ v, v ∈ S ∨ ∃ x ∈ S, G.Adj v x

noncomputable def gamma : ℕ := by
  classical
  exact ((univ : Finset (Finset V)).filter (IsDom G)).inf' ⟨univ, by
    simp [IsDom]⟩ Finset.card

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem gamma_le {S : Finset V} (hS : IsDom G S) : gamma G ≤ S.card := by
  classical
  exact inf'_le _ (mem_filter.mpr ⟨mem_univ _,hS⟩)

noncomputable def localInd (v : V) : ℕ := by
  classical
  exact ((G.neighborFinset v).powerset.filter (Indep G)).sup Finset.card

noncomputable def lambda : ℕ := univ.sup (localInd G)

/-- Closed domination using a vertex and all its nonneighbors. -/
theorem degree_add_gamma_le (v : V) :
    G.degree v + gamma G ≤ Fintype.card V := by
  let S := univ \ G.neighborFinset v
  have hv : v ∈ S := by simp [S]
  have hS : IsDom G S := by
    intro x
    by_cases h : x ∈ S
    · exact Or.inl h
    · exact Or.inr ⟨v,hv,((G.mem_neighborFinset v x).mp (by simpa [S] using h)).symm⟩
  have hh := gamma_le G hS
  have hc := card_sdiff_add_card_eq_card (subset_univ (G.neighborFinset v))
  rw [card_univ,card_neighborFinset_eq_degree] at hc
  change S.card + G.degree v = Fintype.card V at hc
  exact by omega

omit [DecidableEq V] in
/-- Independent neighbors charge against one adjacent vertex's disjoint
neighborhood; the neighboring pair dominates everything inside the union. -/
theorem local_budget {v : V} {A : Finset V} (sub : A ⊆ G.neighborFinset v)
    (ind : Indep G A) (nonempty : A.Nonempty) :
    G.minDegree + gamma G + A.card ≤ Fintype.card V + 2 := by
  classical
  obtain ⟨x,hx⟩ := nonempty
  let N := G.neighborFinset v ∪ G.neighborFinset x
  have hd : Disjoint A (G.neighborFinset x) := by
    refine disjoint_left.mpr ?_
    intro y hy h
    have e := (G.mem_neighborFinset x y).mp h
    exact ind x hx y hy e.ne e
  have incl : A ∪ G.neighborFinset x ⊆ N := union_subset_union sub Subset.rfl
  have size : A.card + G.degree x ≤ N.card := by
    have hh := card_le_card incl
    rwa [card_union_of_disjoint hd,card_neighborFinset_eq_degree] at hh
  let S := insert v (insert x (univ \ N))
  have hS : IsDom G S := by
    intro y
    by_cases h : y ∈ N
    · rcases mem_union.mp h with hh | hh
      · exact Or.inr ⟨v,by simp [S],((G.mem_neighborFinset v y).mp hh).symm⟩
      · exact Or.inr ⟨x,by simp [S],((G.mem_neighborFinset x y).mp hh).symm⟩
    · exact Or.inl (by simp [S,h])
  have ext := gamma_le G hS
  have hs : S.card ≤ (univ \ N).card+2 :=
    (card_insert_le _ _).trans (Nat.add_le_add_right (card_insert_le _ _) 1)
  have count := card_sdiff_add_card_eq_card (subset_univ N)
  rw [card_univ] at count
  have low := G.minDegree_le_degree x
  omega

/-- Upper bound on the exact displayed catalogue right-hand side. -/
theorem rhs_le_order_add_two (hc : G.Connected) :
    G.minDegree + gamma G + lambda G ≤ Fintype.card V + 2 := by
  classical
  by_cases p : lambda G = 0
  · letI := hc.nonempty
    let v : V := Classical.choice hc.nonempty
    have h := degree_add_gamma_le G v
    have d := G.minDegree_le_degree v
    omega
  · letI := hc.nonempty
    obtain ⟨v,_,hv⟩ := exists_max_image univ (localInd G) univ_nonempty
    have e : lambda G = localInd G v :=
      le_antisymm (Finset.sup_le hv) (le_sup (mem_univ v))
    let B := ((G.neighborFinset v).powerset.filter (Indep G))
    have b : B.Nonempty := ⟨∅,by simp [B,Indep]⟩
    obtain ⟨A,hA,hm⟩ := exists_max_image B Finset.card b
    have eq : localInd G v = A.card :=
      le_antisymm (Finset.sup_le hm) (le_sup hA)
    obtain ⟨sub,ind⟩ := mem_filter.mp hA
    have hn : A.Nonempty := card_pos.mp (by omega)
    rw [e,eq]
    exact local_budget G (mem_powerset.mp sub) ind hn

#print axioms degree_add_gamma_le
#print axioms rhs_le_order_add_two
end Graffiti179

/-! ## Equality case and final reduction -/

namespace Graffiti179
open SimpleGraph Finset Short177

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem full_degree (h : G.minDegree + gamma G = Fintype.card V) (v : V) :
    G.degree v = G.minDegree := by
  have p := degree_add_gamma_le G v
  have q := G.minDegree_le_degree v
  omega

/-- At equality in the domination budget, any two distinct nonneighbors
of a vertex are nonadjacent. -/
theorem tight_nonneighbors (h : G.minDegree + gamma G = Fintype.card V)
    {v x y : V} (xv : x ≠ v) (nx : ¬ G.Adj v x) (ny : ¬ G.Adj v y) :
    ¬ G.Adj x y := by
  intro xy
  let S := univ \ G.neighborFinset v
  have hx : x ∈ S := by simp [S,nx]
  have hy : y ∈ S := by simp [S,ny]
  have hv : v ∈ S := by simp [S]
  have hD : IsDom G (S.erase x) := by
    intro z
    by_cases hz : z = x
    · subst z
      exact Or.inr ⟨y,mem_erase.mpr ⟨xy.ne.symm,hy⟩,xy⟩
    · by_cases hs : z ∈ S
      · exact Or.inl (mem_erase.mpr ⟨hz,hs⟩)
      · have e : G.Adj v z := by simpa [S] using hs
        exact Or.inr ⟨v,mem_erase.mpr ⟨xv.symm,hv⟩,e.symm⟩
  have lg := gamma_le G hD
  rw [card_erase_of_mem hx] at lg
  have d := full_degree G h v
  have c := card_sdiff_add_card_eq_card (subset_univ (G.neighborFinset v))
  rw [card_univ,card_neighborFinset_eq_degree,d] at c
  change S.card + G.minDegree = Fintype.card V at c
  have p : 1 ≤ S.card := card_pos.mpr ⟨v,hv⟩
  omega

theorem adjacent_dominates (h : G.minDegree + gamma G = Fintype.card V)
    {u v : V} (uv : G.Adj u v) : IsDom G {u,v} := by
  intro z
  by_cases hz : z ∈ ({u,v} : Finset V)
  · exact Or.inl hz
  · right
    simp only [mem_insert,mem_singleton,not_or] at hz
    by_cases a : G.Adj z u
    · exact ⟨u,by simp,a⟩
    · by_cases b : G.Adj z v
      · exact ⟨v,by simp,b⟩
      · exact (tight_nonneighbors G h (Ne.symm hz.1) a b uv).elim

omit [Fintype V] [DecidableRel G.Adj] in
private theorem indep_pair {a b : V} (h : ¬ G.Adj a b) : Indep G {a,b} := by
  intro x hx y hy ne e
  simp only [mem_insert,mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact ne rfl
  · exact h e
  · exact h e.symm
  · exact ne rfl

/-- In the only budget-tight degree case requiring two extra units, the
dominating edge supplies the leaf budget and a four-cycle the color budget. -/
theorem extremal_leaf_bipartite (h : G.minDegree + gamma G = Fintype.card V)
    {v x y : V} (vx : G.Adj v x) (vy : G.Adj v y)
    (xy : x ≠ y) (nxy : ¬ G.Adj x y) :
    Fintype.card V + 2 ≤ maxLeaves G + bipartiteNum G := by
  classical
  let C (z : V) := univ \ G.neighborFinset z
  have count (z : V) : (C z).card + G.minDegree = Fintype.card V := by
    have q := card_sdiff_add_card_eq_card (subset_univ (G.neighborFinset z))
    rw [card_univ,card_neighborFinset_eq_degree,full_degree G h z] at q
    exact q
  have low : 2 ≤ (C x).card := by
    have q : ({x,y} : Finset V) ⊆ C x := by simp [C,nxy,insert_subset_iff]
    simpa [card_pair xy] using card_le_card q
  have vc : v ∈ C v := by simp [C]
  obtain ⟨w,wc,wv⟩ : ∃ w ∈ C v, w ≠ v := by
    by_contra! bad
    have le : C v ⊆ {v} := fun z hz => by simp [bad z hz]
    have l := card_le_card le
    have one := count x
    have two := count v
    simp at l
    omega
  have nvw : ¬ G.Adj v w := (mem_sdiff.mp wc).2 ∘ (G.mem_neighborFinset v w).mpr
  have wx : w ≠ x := fun e => nvw (e.symm ▸ vx)
  have wy : w ≠ y := fun e => nvw (e.symm ▸ vy)
  have dis : Disjoint ({v,w} : Finset V) {x,y} := by
    simp [disjoint_insert_left, vx.ne, vy.ne, wx, wy, vx.ne.symm, vy.ne.symm, wx.symm, wy.symm]
  let B := ({v,w} : Finset V) ∪ {x,y}
  have col : TwoColor G B := ⟨{v,w},{x,y},dis,rfl,indep_pair G nvw,indep_pair G nxy⟩
  have bc : B.card = 4 := by
    simp only [B,card_union_of_disjoint dis,card_pair wv.symm,card_pair xy]
  have bp : B.card ≤ bipartiteNum G :=
    le_sup (s := univ.filter (TwoColor G)) (f := Finset.card)
      (mem_filter.mpr ⟨mem_univ _,col⟩)
  let S : Finset V := {v,x}
  have cn : Graffiti177.Con G S := by
    have H := Graffiti177.con_insert G (Graffiti177.con_single G x) (by simp) vx
    simpa [S] using H
  have dom : ∀ z ∉ S, Graffiti177.Dominates G S z := by
    intro z zn
    exact (adjacent_dominates G h vx z).resolve_left zn
  have leaf := Graffiti177.conDom_leaves G S cn dom
  change (univ \ S).card ≤ maxLeaves G at leaf
  have eq := card_sdiff_add_card_eq_card (subset_univ S)
  have sz : S.card = 2 := card_pair vx.ne
  rw [card_univ,sz] at eq
  omega

/-- Integration of the exact minimum-degree statement with the two published
DeLaViña–Waller leaf bounds. These two lower bounds are hypotheses here. -/
theorem of_leaf_bounds (hc : G.Connected)
    (base : Fintype.card V + 1 ≤ maxLeaves G + bipartiteNum G)
    (claw : 3 ≤ lambda G → Fintype.card V + 2 ≤ maxLeaves G + bipartiteNum G) :
    G.minDegree + gamma G + lambda G ≤ maxLeaves G + bipartiteNum G := by
  classical
  letI := hc.nonempty
  let root : V := Classical.choice hc.nonempty
  have cg := degree_add_gamma_le G root
  have gd := G.minDegree_le_degree root
  by_cases h3 : 3 ≤ lambda G
  · exact (rhs_le_order_add_two G hc).trans (claw h3)
  by_cases h2 : lambda G = 2
  · by_cases eq : G.minDegree + gamma G = Fintype.card V
    · obtain ⟨v,_,hv⟩ := exists_max_image univ (localInd G) univ_nonempty
      have ev : lambda G = localInd G v :=
        le_antisymm (Finset.sup_le hv) (le_sup (mem_univ v))
      let B := ((G.neighborFinset v).powerset.filter (Indep G))
      have b : B.Nonempty := ⟨∅,by simp [B,Indep]⟩
      obtain ⟨A,hA,hm⟩ := exists_max_image B Finset.card b
      have ea : localInd G v = A.card :=
        le_antisymm (Finset.sup_le hm) (le_sup hA)
      obtain ⟨x,y,ne,eA⟩ := card_eq_two.mp (by omega : A.card = 2)
      obtain ⟨sub,ind⟩ := mem_filter.mp hA
      have hx : x ∈ A := by simp [eA]
      have hy : y ∈ A := by simp [eA]
      have vxs := (G.mem_neighborFinset v x).mp (mem_powerset.mp sub hx)
      have vys := (G.mem_neighborFinset v y).mp (mem_powerset.mp sub hy)
      have e := extremal_leaf_bipartite G eq vxs vys ne (ind _ hx _ hy ne)
      omega
    · omega
  · omega

#print axioms of_leaf_bounds
#print axioms tight_nonneighbors
#print axioms adjacent_dominates
#print axioms extremal_leaf_bipartite

end Graffiti179

/-! ## Maximal bipartite blocks -/

namespace Graffiti179
open Finset SimpleGraph Short177

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

structure Block (pool seed : Finset V) where
  A : Finset V
  B : Finset V
  disjoint : Disjoint A B
  indA : Indep G A
  indB : Indep G B
  conn : Graffiti177.Con G (A ∪ B)
  inside : A ∪ B ⊆ pool
  seeded : seed ⊆ A ∪ B
  maximal : ∀ {x}, x ∈ pool → x ∉ A ∪ B →
    (∃ y ∈ A ∪ B, G.Adj x y) →
    (∃ y ∈ A, G.Adj x y) ∧ (∃ y ∈ B, G.Adj x y)

omit [Fintype V] in
private theorem indep_insert_not_touch {S : Finset V} {x : V} (hs : Indep G S)
    (h : ∀ y ∈ S, ¬ G.Adj x y) : Indep G (insert x S) := by
  intro a ha b hb ne e
  rcases mem_insert.mp ha with rfl | aa <;> rcases mem_insert.mp hb with rfl | bb
  · exact ne rfl
  · exact h _ bb e
  · exact h _ aa e.symm
  · exact hs _ aa _ bb ne e

/-- A largest seeded connected bipartite set meets both colors at each
outside pool vertex that contacts it. -/
theorem exists_block {pool seed : Finset V} (sub : seed ⊆ pool)
    (hconn : Graffiti177.Con G seed) (hbip : TwoColor G seed) :
    Nonempty (Block G pool seed) := by
  classical
  let good (S : Finset V) := seed ⊆ S ∧ S ⊆ pool ∧
    Graffiti177.Con G S ∧ TwoColor G S
  let candidates := (univ : Finset (Finset V)).filter good
  have seed_mem : seed ∈ candidates :=
    mem_filter.mpr ⟨mem_univ _,Subset.rfl,sub,hconn,hbip⟩
  obtain ⟨S,hS,best⟩ := exists_max_image candidates Finset.card ⟨seed,seed_mem⟩
  obtain ⟨hsSeed,hsPool,hsConn,A,B,d,e,i,j⟩ := (mem_filter.mp hS).2
  subst S
  refine ⟨⟨A,B,d,i,j,hsConn,hsPool,hsSeed,?_⟩⟩
  intro x xp xn hx
  obtain ⟨y,ym,ey⟩ := hx
  have conn' := Graffiti177.con_insert G hsConn ym ey
  have hbig (colors : TwoColor G (insert x (A ∪ B))) : False := by
    have member : insert x (A ∪ B) ∈ candidates := mem_filter.mpr
      ⟨mem_univ _, hsSeed.trans (subset_insert _ _), insert_subset xp hsPool,conn',colors⟩
    have le := best _ member
    rw [card_insert_of_not_mem xn] at le
    omega
  constructor
  · by_contra! h
    have ds : Disjoint (insert x A) B := disjoint_insert_left.mpr
      ⟨fun xB => xn (mem_union_right _ xB),d⟩
    exact hbig ⟨insert x A,B,ds,insert_union _ _ _, indep_insert_not_touch G i h,j⟩
  · by_contra! h
    have ds : Disjoint A (insert x B) := disjoint_insert_right.mpr
      ⟨fun xA => xn (mem_union_left _ xA),d⟩
    exact hbig ⟨A,insert x B,ds,union_insert _ _ _,i,indep_insert_not_touch G j h⟩

#print axioms exists_block
end Graffiti179

/-! ## Connected domination invariant -/

namespace Graffiti179
open Finset SimpleGraph Short177
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable [DecidableRel G.Adj]

def closed (S : Finset V) : Finset V := S ∪ S.biUnion (fun v => G.neighborFinset v)

theorem mem_closed {S : Finset V} {x : V} :
    x ∈ closed G S ↔ x ∈ S ∨ ∃ y ∈ S, G.Adj x y := by
  simp only [closed,mem_union,mem_biUnion,mem_neighborFinset]
  constructor <;> rintro (hx | ⟨y,hy,ey⟩)
  · exact Or.inl hx
  · exact Or.inr ⟨y,hy,ey.symm⟩
  · exact Or.inl hx
  · exact Or.inr ⟨y,hy,ey.symm⟩

theorem closed_union (S T : Finset V) :
    closed G (S ∪ T) = closed G S ∪ closed G T := by
  ext x
  simp only [mem_closed,mem_union]
  constructor
  · rintro ((hs | ht) | ⟨y, (ys | yt), e⟩)
    · exact Or.inl (Or.inl hs)
    · exact Or.inr (Or.inl ht)
    · exact Or.inl (Or.inr ⟨y,ys,e⟩)
    · exact Or.inr (Or.inr ⟨y,yt,e⟩)
  · rintro ((hs | ⟨y,ys,e⟩) | (ht | ⟨y,yt,e⟩))
    · exact Or.inl (Or.inl hs)
    · exact Or.inr ⟨y,Or.inl ys,e⟩
    · exact Or.inl (Or.inr ht)
    · exact Or.inr ⟨y,Or.inr yt,e⟩

theorem closed_mono {S T : Finset V} (h : S ⊆ T) : closed G S ⊆ closed G T := by
  intro x hx
  rcases (mem_closed G).mp hx with m | ⟨y,ym,xy⟩
  · exact (mem_closed G).mpr (Or.inl (h m))
  · exact (mem_closed G).mpr (Or.inr ⟨y,h ym,xy⟩)

omit [Fintype V] [DecidableRel G.Adj] in
theorem walk_cross {S : Finset V} {x y : V} (p : G.Walk x y)
    (hx : x ∈ S) (hy : y ∉ S) : ∃ u ∈ S, ∃ v ∉ S, G.Adj u v := by
  induction p with
  | nil => contradiction
  | @cons u z y e p ih =>
    by_cases k : z ∈ S
    · exact ih k hy
    · exact ⟨u,hx,z,k,e⟩

/-- Two disjoint color classes chosen away from the closed neighborhood
of earlier blocks may be added without creating any forbidden edge. -/
theorem bip_union_closed {S T : Finset V}
    (hS : TwoColor G S) (hT : TwoColor G T)
    (h : ∀ x ∈ T, x ∉ closed G S) : TwoColor G (S ∪ T) := by
  obtain ⟨A,B,ab,rfl,ai,bi⟩ := hS
  obtain ⟨C,D,cd,rfl,ci,di⟩ := hT
  have sep (x : V) (hx : x ∈ A ∪ B) (y : V) (hy : y ∈ C ∪ D) :
      x ≠ y ∧ ¬ G.Adj x y := by
    refine ⟨?_,?_⟩
    · intro eq
      subst y
      exact h x hy ((mem_closed G).mpr (Or.inl hx))
    · intro adj
      exact h y hy ((mem_closed G).mpr (Or.inr ⟨x,hx,adj.symm⟩))
  refine ⟨A∪C,B∪D, ?_, ?_, ?_, ?_⟩
  · rw [disjoint_left]
    intro x ha hb
    rcases mem_union.mp ha with ha | ha <;> rcases mem_union.mp hb with hb | hb
    · exact (disjoint_left.mp ab) ha hb
    · exact (sep x (mem_union_left _ ha) x (mem_union_right _ hb)).1 rfl
    · exact (sep x (mem_union_right _ hb) x (mem_union_left _ ha)).1 rfl
    · exact (disjoint_left.mp cd) ha hb
  · ext x
    simp only [mem_union]
    tauto
  · intro x hx y hy ne e
    rcases mem_union.mp hx with ha | hc <;> rcases mem_union.mp hy with ha' | hc'
    · exact ai _ ha _ ha' ne e
    · exact (sep _ (mem_union_left _ ha) _ (mem_union_left _ hc')).2 e
    · exact (sep _ (mem_union_left _ ha') _ (mem_union_left _ hc)).2 e.symm
    · exact ci _ hc _ hc' ne e
  · intro x hx y hy ne e
    rcases mem_union.mp hx with hb | hd <;> rcases mem_union.mp hy with hb' | hd'
    · exact bi _ hb _ hb' ne e
    · exact (sep _ (mem_union_right _ hb) _ (mem_union_right _ hd')).2 e
    · exact (sep _ (mem_union_right _ hb') _ (mem_union_right _ hd)).2 e.symm
    · exact di _ hd _ hd' ne e

/-- A connected core meeting the old blocks' domination obligations. -/
structure State (gain : ℕ) (S D : Finset V) : Prop where
  bip : TwoColor G S
  conn : Graffiti177.Con G D
  budget : D.card + gain ≤ S.card
  dom : closed G S ⊆ closed G D

theorem State.cap {gain : ℕ} {S D : Finset V} (st : State G gain S D)
    (full : closed G S = univ) :
    Fintype.card V + gain ≤ maxLeaves G + bipartiteNum G := by
  classical
  have dom : ∀ v ∉ D, Graffiti177.Dominates G D v := by
    intro v miss
    have h : v ∈ closed G D := st.dom (by simp [full])
    exact ((mem_closed G).mp h).resolve_left miss
  have lf := Graffiti177.conDom_leaves G D st.conn dom
  change (univ \ D).card ≤ maxLeaves G at lf
  have b : S.card ≤ bipartiteNum G :=
    le_sup (s := univ.filter (TwoColor G)) (f := Finset.card)
      (mem_filter.mpr ⟨mem_univ _,st.bip⟩)
  have c := card_sdiff_add_card_eq_card (subset_univ D)
  rw [card_univ] at c
  have bud := st.budget
  omega

/-- A connector lies in the old dominating neighborhood, with its seed outside. -/
theorem connector {S : Finset V} (hc : G.Connected) (hs : S.Nonempty)
    (miss : closed G S ≠ univ) :
    ∃ c ∈ closed G S, ∃ x ∉ closed G S, G.Adj c x := by
  classical
  obtain ⟨q,qm⟩ := hs
  obtain ⟨u,um⟩ := nonempty_iff_ne_empty.mpr (show univ \ closed G S ≠ ∅ by
    intro e
    exact miss (Finset.sdiff_eq_empty_iff_subset.mp e |> fun h => Subset.antisymm (subset_univ _) h))
  obtain ⟨p⟩ := hc.preconnected q u
  exact walk_cross G p ((mem_closed G).mpr (Or.inl qm)) (mem_sdiff.mp um).2

#print axioms bip_union_closed
#print axioms State.cap
#print axioms connector
end Graffiti179

/-! ## Connector and finite growth -/

namespace Graffiti179
open Finset SimpleGraph Short177
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
private theorem con_union_edge {D R : Finset V} (hD : Graffiti177.Con G D)
    (hR : Graffiti177.Con G R) {c x : V} (cd : c ∈ D) (xr : x ∈ R) (cx : G.Adj c x) :
    Graffiti177.Con G (D ∪ R) := by
  let i : G.induce (D : Set V) →g G.induce (↑(D ∪ R) : Set V) :=
    (G.induceHomOfLE (show (D : Set V) ≤ ↑(D ∪ R) from fun _ h => mem_union_left _ h)).toHom
  let j : G.induce (R : Set V) →g G.induce (↑(D ∪ R) : Set V) :=
    (G.induceHomOfLE (show (R : Set V) ≤ ↑(D ∪ R) from fun _ h => mem_union_right _ h)).toHom
  have step : (G.induce (↑(D ∪ R) : Set V)).Adj (i ⟨c,cd⟩) (j ⟨x,xr⟩) := cx
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨i ⟨c,cd⟩,fun w => ?_⟩
  rcases mem_union.mp w.2 with wd | wr
  · exact (hD ⟨c,cd⟩ ⟨w.1,wd⟩).map i
  · exact step.reachable.trans ((hR ⟨x,xr⟩ ⟨w.1,wr⟩).map j)

theorem PreparedStep {gain : ℕ} {S D T R : Finset V} (st : State G gain S D)
    (bi : TwoColor G T) (pool : ∀ x ∈ T, x ∉ closed G S)
    {c x : V} (cS : c ∈ closed G S) (cx : G.Adj c x)
    (trim : R.card + 1 ≤ T.card)
    (reaches : R = ∅ ∨ (Graffiti177.Con G R ∧ x ∈ R))
    (covers : ∀ z ∈ closed G T, z ∈ closed G S ∨ z = x ∨ z ∈ closed G R) :
    State G gain (S ∪ T) (insert c D ∪ R) := by
  have dconn : Graffiti177.Con G (insert c D) := by
    rcases (mem_closed G).mp (st.dom cS) with d | ⟨y,yd,cy⟩
    · rw [insert_eq_of_mem d]
      exact st.conn
    · exact Graffiti177.con_insert G st.conn yd cy
  refine ⟨bip_union_closed G st.bip bi pool,?_,?_,?_⟩
  · rcases reaches with rfl | ⟨rcon,xr⟩
    · simpa using dconn
    · exact con_union_edge G dconn rcon (mem_insert_self _ _) xr cx
  · have dt : Disjoint S T := disjoint_left.mpr (fun q qs qt =>
      pool q qt ((mem_closed G).mpr (Or.inl qs)))
    have dcard := (card_union_le (insert c D) R).trans
      (Nat.add_le_add_right (card_insert_le c D) R.card)
    rw [card_union_of_disjoint dt]
    have b := st.budget
    omega
  · rw [closed_union]
    intro z hz
    have old : closed G S ⊆ closed G (insert c D ∪ R) :=
      st.dom.trans (closed_mono G ((subset_insert c D).trans subset_union_left))
    rcases mem_union.mp hz with h | h
    · exact old h
    rcases covers z h with h | rfl | h
    · exact old h
    · exact (mem_closed G).mpr (Or.inr ⟨c,mem_union_left _ (mem_insert_self _ _),cx.symm⟩)
    · exact closed_mono G subset_union_right h

structure Trim (pool T : Finset V) (seed : V) where
  keep : Finset V
  size : keep.card + 1 ≤ T.card
  connected : keep = ∅ ∨ (Graffiti177.Con G keep ∧ seed ∈ keep)
  covers : ∀ v ∈ closed G T, v ∉ pool ∨ v = seed ∨ v ∈ closed G keep

/-- Once one knows how to trim a maximal block at its incoming seed,
every partial state extends to a connected dominating core without
losing the original savings. -/
theorem complete_state (hc : G.Connected)
    (localTrim : ∀ (pool : Finset V) (x : V) (b : Block G pool {x}),
      Nonempty (Trim G pool (b.A ∪ b.B) x))
    (gain : ℕ) (S D : Finset V) (st : State G gain S D) (hs : S.Nonempty) :
    Fintype.card V + gain ≤ maxLeaves G + bipartiteNum G := by
  classical
  by_cases full : closed G S = univ
  · exact st.cap G full
  obtain ⟨c,cs,x,xs,cx⟩ := connector G hc hs full
  let pool := univ \ closed G S
  have seed : ({x} : Finset V) ⊆ pool := by simp [pool,xs]
  have col : TwoColor G {x} := by
    refine ⟨{x},∅,by simp,by simp,?_,?_⟩ <;> simp [Indep]
  obtain ⟨b⟩ := exists_block G seed (Graffiti177.con_single G x) col
  obtain ⟨trim⟩ := localTrim pool x b
  let T := b.A ∪ b.B
  have xt : x ∈ T := b.seeded (mem_singleton_self _)
  have sep : ∀ v ∈ T, v ∉ closed G S := fun v hv => (mem_sdiff.mp (b.inside hv)).2
  have bi : TwoColor G T := ⟨b.A,b.B,b.disjoint,rfl,b.indA,b.indB⟩
  have coverage : ∀ z ∈ closed G T, z ∈ closed G S ∨ z = x ∨ z ∈ closed G trim.keep := by
    intro z hz
    have h := trim.covers z hz
    simpa [pool] using h
  have grown := PreparedStep G st bi sep cs cx trim.size trim.connected coverage
  have sub : S ⊂ S ∪ T := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_left,?_⟩
    intro eq
    exact xs ((mem_closed G).mpr (Or.inl (eq.symm ▸ (mem_union_right S xt))))
  have lt := card_lt_card sub
  have le := card_le_univ (s := S ∪ T)
  exact complete_state hc localTrim gain (S ∪ T) (insert c D ∪ trim.keep) grown
    ⟨x,mem_union_right S xt⟩
termination_by Fintype.card V - S.card
decreasing_by
  change Fintype.card V - (S ∪ T).card < Fintype.card V - S.card
  omega

#print axioms complete_state
#print axioms PreparedStep
end Graffiti179

/-! ## One-vertex trim and the order-plus-one bound -/

namespace Graffiti179
open Finset SimpleGraph Short177
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
private theorem within_cross {D B : Finset V} (sub : D ⊆ B)
    (conn : Graffiti177.Con G B) (d : D.Nonempty) (pr : D ≠ B) :
    ∃ a ∈ D, ∃ b ∈ B, b ∉ D ∧ G.Adj a b := by
  classical
  obtain ⟨a,da⟩ := d
  obtain ⟨b,bb,bd⟩ : ∃ b ∈ B, b ∉ D := by
    by_contra! e
    exact pr (Subset.antisymm sub e)
  let D' : Finset (B : Set V) := univ.filter (fun x => x.val ∈ D)
  let u : (B : Set V) := ⟨a,sub da⟩
  let v : (B : Set V) := ⟨b,bb⟩
  obtain ⟨p⟩ := conn u v
  have uu : u ∈ D' := by simp [D',u,da]
  have vv : v ∉ D' := by simp [D',v,bd]
  obtain ⟨x,hx,y,hy,e⟩ := walk_cross (G.induce (B : Set V)) p uu vv
  exact ⟨x.val,(mem_filter.mp hx).2,y.val,y.property,by simpa [D'] using hy,e⟩

omit [DecidableRel G.Adj] in
private theorem trim_at_seed {B : Finset V} {s : V} (sb : s ∈ B)
    (co : Graffiti177.Con G B) (large : 1 < B.card) :
    ∃ x ∈ B, x ≠ s ∧ Graffiti177.Con G (B.erase x) ∧
      (∃ y ∈ B.erase x, G.Adj x y) := by
  classical
  let good (D : Finset V) := s ∈ D ∧ D ⊆ B ∧ D ≠ B ∧ Graffiti177.Con G D
  let all := (univ : Finset (Finset V)).filter good
  have cand : ({s} : Finset V) ∈ all := by
    apply mem_filter.mpr
    refine ⟨mem_univ _,by simp,singleton_subset_iff.mpr sb,?_,Graffiti177.con_single G s⟩
    intro e
    have eq := congrArg Finset.card e
    simp at eq
    omega
  obtain ⟨D,dm,maxD⟩ := exists_max_image all Finset.card ⟨{s},cand⟩
  obtain ⟨sd,sub,ne,dc⟩ := (mem_filter.mp dm).2
  obtain ⟨y,yd,x,xb,nxd,exy⟩ := within_cross G sub co ⟨s,sd⟩ ne
  have eq : insert x D = B := by
    by_contra no
    have mem : insert x D ∈ all := mem_filter.mpr ⟨mem_univ _,mem_insert_of_mem sd,
      insert_subset xb sub,no,Graffiti177.con_insert G dc yd exy.symm⟩
    have fin := maxD _ mem
    rw [card_insert_of_not_mem nxd] at fin
    omega
  have e : B.erase x = D := by rw [← eq, erase_insert nxd]
  refine ⟨x,xb,fun h => nxd (h.symm ▸ sd),?_,?_⟩
  · rw [e]; exact dc
  · exact ⟨y,e.symm ▸ yd,exy.symm⟩

/-- Prepare any noninitial block by taking out one vertex without
disconnecting its seed; for a singleton the connector covers the seed. -/
theorem trim_one_preserves_seed (pool : Finset V) (s : V) (b : Block G pool {s}) :
    ∃ t : Trim G pool (b.A ∪ b.B) s, 1 < (b.A ∪ b.B).card → s ∈ t.keep := by
  classical
  let T := b.A ∪ b.B
  have sb : s ∈ T := b.seeded (mem_singleton_self _)
  by_cases large : 1 < T.card
  · obtain ⟨x,xb,xs,conn,ydom⟩ := trim_at_seed G sb b.conn large
    refine ⟨⟨T.erase x,?_,Or.inr ⟨conn,mem_erase.mpr ⟨xs.symm,sb⟩⟩,?_⟩,?_⟩
    · change (T.erase x).card + 1 ≤ T.card
      rw [card_erase_of_mem xb]
      omega
    · intro z hz
      by_cases zp : z ∈ pool
      · right; right
        by_cases zT : z ∈ T
        · by_cases zx : z = x
          · subst z
            exact (mem_closed G).mpr (Or.inr ydom)
          · exact (mem_closed G).mpr (Or.inl (mem_erase.mpr ⟨zx,zT⟩))
        · have h := ((mem_closed G).mp hz).resolve_left zT
          obtain ⟨ha,hb⟩ := b.maximal zp zT h
          rcases mem_union.mp xb with xa | xbb
          · obtain ⟨y,yb,e⟩ := hb
            have ne : y ≠ x := fun eq => (disjoint_left.mp b.disjoint) xa (eq ▸ yb)
            exact (mem_closed G).mpr (Or.inr ⟨y,mem_erase.mpr ⟨ne,mem_union_right _ yb⟩,e⟩)
          · obtain ⟨y,ya,e⟩ := ha
            have ne : y ≠ x := fun eq => (disjoint_left.mp b.disjoint) (eq ▸ ya) xbb
            exact (mem_closed G).mpr (Or.inr ⟨y,mem_erase.mpr ⟨ne,mem_union_left _ ya⟩,e⟩)
      · exact Or.inl zp
    · exact fun _ => mem_erase.mpr ⟨xs.symm,sb⟩
  · have sz : T.card = 1 := by have := card_pos.mpr ⟨s,sb⟩; omega
    have eq : T = {s} :=
      Finset.eq_of_subset_of_card_le (singleton_subset_iff.mpr sb) (by simp [sz]) |>.symm
    refine ⟨⟨∅,?_,Or.inl rfl,?_⟩,?_⟩
    · change (∅ : Finset V).card + 1 ≤ T.card
      simpa only [card_empty,zero_add] using sz.ge
    · intro z hz
      by_cases zp : z ∈ pool
      · by_cases ze : z = s
        · exact Or.inr (Or.inl ze)
        exfalso
        have nT : z ∉ T := by simpa only [eq,mem_singleton] using ze
        have h := ((mem_closed G).mp hz).resolve_left nT
        obtain ⟨⟨a,aa,_⟩,⟨c,cb,_⟩⟩ := b.maximal zp nT h
        have ae : a = s := mem_singleton.mp (eq ▸ mem_union_left b.B aa)
        have ce : c = s := mem_singleton.mp (eq ▸ mem_union_right b.A cb)
        subst a; subst c
        exact (disjoint_left.mp b.disjoint) aa cb
      · exact Or.inl zp
    · intro h
      exact (large h).elim

theorem trim_one (pool : Finset V) (s : V) (b : Block G pool {s}) :
    Nonempty (Trim G pool (b.A ∪ b.B) s) := by
  obtain ⟨t,_⟩ := trim_one_preserves_seed G pool s b
  exact ⟨t⟩

/-- DeLaViña–Waller Theorem 4, using incremental bipartite blocks. -/
theorem order_add_one (hc : G.Connected) (hn : 1 < Fintype.card V) :
    Fintype.card V + 1 ≤ maxLeaves G + bipartiteNum G := by
  classical
  let x := Classical.choice hc.nonempty
  obtain ⟨y,xy⟩ := Graffiti177.exists_adj G hc hn x
  let U : Finset V := {x,y}
  have co : Graffiti177.Con G U := Graffiti177.con_insert G (Graffiti177.con_single G y) (by simp) xy
  have col : TwoColor G U := by
    refine ⟨{x},{y},by simp [xy.ne.symm],by ext q; simp [U],?_,?_⟩ <;> simp [Indep]
  obtain ⟨b⟩ := exists_block G (subset_univ U) co col
  let b' : Block G univ {x} :=
    ⟨b.A,b.B,b.disjoint,b.indA,b.indB,b.conn,b.inside,
      (singleton_subset_iff.mpr (show x ∈ U from by simp [U])).trans b.seeded,b.maximal⟩
  let T := b'.A ∪ b'.B
  have u2 : 2 ≤ T.card :=
    (card_pair xy.ne).symm.le.trans (card_le_card b.seeded)
  obtain ⟨t,kt⟩ := trim_one_preserves_seed G univ x b'
  have xk := kt u2
  have con : Graffiti177.Con G t.keep := by
    rcases t.connected with e | ⟨c,_⟩
    · rw [e] at xk
      exact (not_mem_empty _ xk).elim
    · exact c
  have dom : closed G T ⊆ closed G t.keep := by
    intro z hz
    rcases t.covers z hz with bad | rfl | hh
    · exact (bad (mem_univ _)).elim
    · exact (mem_closed G).mpr (Or.inl xk)
    · exact hh
  have blank : State G 1 T t.keep :=
    ⟨⟨b'.A,b'.B,b'.disjoint,rfl,b'.indA,b'.indB⟩,con,t.size,dom⟩
  exact complete_state G hc (trim_one G) 1 T t.keep blank
    ⟨x,b'.seeded (mem_singleton_self _)⟩

#print axioms order_add_one

#print axioms trim_one
end Graffiti179

/-! ## Two leaves of one color in a rooted block -/

namespace Graffiti179.Rooted
open Finset SimpleGraph
variable {W : Type*}

structure Parent (H : SimpleGraph W) (r : W) where
  next : W → W
  step : ∀ x, x ≠ r → H.Adj x (next x) ∧ H.dist x r = H.dist (next x) r + 1

noncomputable def chooseParent {H : SimpleGraph W} (hc : H.Connected) (r : W) :
    Parent H r := by
  classical
  let p (x : W) := if h : x ≠ r then (Graffiti169.exists_predecessor H hc r x h).choose else r
  exact ⟨p,fun x h => by simpa [p,h] using (Graffiti169.exists_predecessor H hc r x h).choose_spec⟩

namespace Parent
variable {H : SimpleGraph W} {r : W} (p : Parent H r)

noncomputable def tag (x : W) : W := (p.next^[H.dist x r - 1]) x

def End (x : W) : Prop := x ≠ r ∧ ∀ y, y ≠ r → p.next y ≠ x

theorem tag_child {x : W} (hne : x ≠ r) (pos : 1 ≤ H.dist (p.next x) r) :
    p.tag x = p.tag (p.next x) := by
  unfold tag
  have h := (p.step x hne).2
  rw [show H.dist x r - 1 = (H.dist (p.next x) r - 1) + 1 by omega]
  rw [Function.iterate_succ_apply]

/-- Every root-neighbor branch has a terminal vertex for the BFS parent map. -/
theorem end_in_branch [Fintype W] (hc : H.Connected) {a : W} (ar : H.Adj a r) :
    ∃ z, p.tag z = a ∧ p.End z := by
  classical
  let B : Finset W := univ.filter (fun z => p.tag z = a)
  have am : a ∈ B := by simp [B,tag,dist_eq_one_iff_adj.mpr ar]
  obtain ⟨z,zm,best⟩ := exists_max_image B (fun x => H.dist x r) ⟨a,am⟩
  have tz : p.tag z = a := (mem_filter.mp zm).2
  have zr : z ≠ r := by
    intro e
    subst z
    exact ar.ne (by simpa [tag,dist_self] using tz.symm)
  refine ⟨z,tz,zr,?_⟩
  intro y yr e
  have pos := hc.pos_dist_of_ne zr
  have level := (p.step y yr).2
  have ye : p.tag y = a := (p.tag_child yr (by rw [e]; omega)).trans (e.symm ▸ tz)
  have le := best y (mem_filter.mpr ⟨mem_univ _,ye⟩)
  rw [e] at level
  omega

theorem two_ends_same_color [Fintype W] (hc : H.Connected) (χ : W → Bool)
    {a b c : W} (ha : H.Adj a r) (hb : H.Adj b r) (hh : H.Adj c r)
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
    ∃ x y, x ≠ y ∧ p.End x ∧ p.End y ∧ χ x = χ y := by
  obtain ⟨x,tx,hx⟩ := p.end_in_branch hc ha
  obtain ⟨y,ty,hy⟩ := p.end_in_branch hc hb
  obtain ⟨z,tz,hz⟩ := p.end_in_branch hc hh
  have xy : x ≠ y := fun e => ab (tx.symm.trans ((congrArg p.tag e).trans ty))
  have xz : x ≠ z := fun e => ac (tx.symm.trans ((congrArg p.tag e).trans tz))
  have yz : y ≠ z := fun e => bc (ty.symm.trans ((congrArg p.tag e).trans tz))
  by_cases e : χ x = χ y
  · exact ⟨x,y,xy,hx,hy,e⟩
  by_cases f : χ x = χ z
  · exact ⟨x,z,xz,hx,hz,f⟩
  exact ⟨y,z,yz,hy,hz,by revert e f; cases χ x <;> cases χ y <;> cases χ z <;> simp⟩

/-- Discarding any set of terminal nonroot vertices preserves reachability to the root. -/
theorem reach_keep (R : Set W) (ends : ∀ x ∈ R, p.End x)
    (x : W) (xr : x ∉ R) :
    (H.induce Rᶜ).Reachable ⟨x,xr⟩
      ⟨r,fun rr => (ends r rr).1 rfl⟩ := by
  classical
  by_cases e : x = r
  · subst x
    exact Reachable.refl _
  have h := p.step x e
  have nxt : p.next x ∉ R := fun m => (ends _ m).2 x e rfl
  have a : (H.induce Rᶜ).Adj ⟨x,xr⟩ ⟨p.next x,nxt⟩ := h.1
  exact a.reachable.trans (reach_keep R ends (p.next x) nxt)
termination_by H.dist x r
decreasing_by omega

#print axioms two_ends_same_color
#print axioms reach_keep
end Parent
end Graffiti179.Rooted

/-! ## Induced claw and exact final theorem -/

namespace Graffiti179
open Finset SimpleGraph Short177
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable [DecidableRel G.Adj]

/-- The initial maximal bipartite block can save two vertices if one point
has three neighbors in the block. -/
theorem claw_state {s : Finset V} (b : Block G univ s)
    {r a₁ a₂ a₃ : V} (hr : r ∈ b.A ∪ b.B)
    (a₁m : a₁ ∈ b.A ∪ b.B) (a₂m : a₂ ∈ b.A ∪ b.B) (a₃m : a₃ ∈ b.A ∪ b.B)
    (ar₁ : G.Adj a₁ r) (ar₂ : G.Adj a₂ r) (ar₃ : G.Adj a₃ r)
    (ne₁₂ : a₁ ≠ a₂) (ne₁₃ : a₁ ≠ a₃) (ne₂₃ : a₂ ≠ a₃) :
    ∃ D, State G 2 (b.A ∪ b.B) D := by
  classical
  let T := b.A ∪ b.B
  let W := (T : Set V)
  let H := G.induce W
  let o : W := ⟨r,hr⟩
  let p := Rooted.chooseParent (show H.Connected from b.conn) o
  let χ (x : W) := decide (x.val ∈ b.A)
  obtain ⟨x,y,xy,xe,ye,same⟩ :=
    p.two_ends_same_color (show H.Connected from b.conn) χ
      (a:=⟨a₁,a₁m⟩) (b:=⟨a₂,a₂m⟩) (c:=⟨a₃,a₃m⟩)
      ar₁ ar₂ ar₃
      (fun h => ne₁₂ (congrArg Subtype.val h))
      (fun h => ne₁₃ (congrArg Subtype.val h))
      (fun h => ne₂₃ (congrArg Subtype.val h))
  let R : Set W := {w | w = x ∨ w = y}
  let K : Finset V := T \ {x.val,y.val}
  have es : ∀ v ∈ R, p.End v := by
    rintro z (rfl | rfl)
    · exact xe
    · exact ye
  have mem (v : W) : v ∉ R ↔ v.val ∈ K := by
    simp [R,K,v.property,Subtype.ext_iff,not_or]
  have rm : o ∉ R := fun rr => (es _ rr).1 rfl
  let inc : H.induce Rᶜ →g G.induce (K : Set V) :=
    { toFun := fun z => ⟨z.val.val,(mem z.val).mp z.property⟩
      map_rel' := fun e => e }
  have conn : Graffiti177.Con G K := by
    apply (connected_iff_exists_forall_reachable _).mpr
    refine ⟨inc ⟨o,rm⟩,fun z => ?_⟩
    have zm : z.val ∈ T := (mem_sdiff.mp z.property).1
    let z' : W := ⟨z.val,zm⟩
    have ok : z' ∉ R := (mem z').mpr z.property
    exact ((p.reach_keep R es z' ok).map inc).symm
  have parents {u : W} (ur : u ∈ R) : u.val ∈ closed G K := by
    have no : p.next u ∉ R := fun emp => (es _ emp).2 u (es u ur).1 rfl
    exact (mem_closed G).mpr (Or.inr ⟨(p.next u).val,(mem (p.next u)).mp no,(p.step u (es u ur).1).1⟩)
  have sameA : x.val ∈ b.A ↔ y.val ∈ b.A := by
    change decide (x.val ∈ b.A) = decide (y.val ∈ b.A) at same
    constructor <;> intro h
    · simpa [h] using same.symm
    · simpa [h] using same
  have act : (x.val ∈ b.A ∧ y.val ∈ b.A) ∨ (x.val ∈ b.B ∧ y.val ∈ b.B) := by
    by_cases h : x.val ∈ b.A
    · exact Or.inl ⟨h,sameA.mp h⟩
    · exact Or.inr ⟨(mem_union.mp x.property).resolve_left h,
        (mem_union.mp y.property).resolve_left (fun yy => h (sameA.mpr yy))⟩
  have dom : closed G T ⊆ closed G K := by
    intro z hz
    by_cases za : z = x.val
    · subst z
      exact parents (show x ∈ R from Or.inl rfl)
    by_cases zb : z = y.val
    · subst z
      exact parents (show y ∈ R from Or.inr rfl)
    by_cases havez : z ∈ T
    · exact (mem_closed G).mpr (Or.inl (by simp [K,havez,za,zb]))
    obtain ⟨A,B⟩ := b.maximal (mem_univ z) havez (((mem_closed G).mp hz).resolve_left havez)
    rcases act with ⟨xa,ya⟩ | ⟨xb,yb⟩
    · obtain ⟨v,vb,e⟩ := B
      have xn : v ≠ x.val := fun h => (disjoint_left.mp b.disjoint) xa (h ▸ vb)
      have yn : v ≠ y.val := fun h => (disjoint_left.mp b.disjoint) ya (h ▸ vb)
      exact (mem_closed G).mpr (Or.inr ⟨v,by simp [K,T,mem_union_right _ vb,xn,yn],e⟩)
    · obtain ⟨v,va,e⟩ := A
      have xn : v ≠ x.val := fun h => (disjoint_left.mp b.disjoint) (h ▸ va) xb
      have yn : v ≠ y.val := fun h => (disjoint_left.mp b.disjoint) (h ▸ va) yb
      exact (mem_closed G).mpr (Or.inr ⟨v,by simp [K,T,mem_union_left _ va,xn,yn],e⟩)
  have sub : ({x.val,y.val} : Finset V) ⊆ T := by simp [insert_subset_iff,x.property,y.property]
  have cnt := card_sdiff_add_card_eq_card sub
  rw [card_pair (fun h => xy (Subtype.ext h))] at cnt
  exact ⟨K,⟨⟨b.A,b.B,b.disjoint,rfl,b.indA,b.indB⟩,conn,cnt.le,dom⟩⟩

/-- DeLaViña–Waller Theorem 5 in the induced-claw case. -/
theorem order_add_two (hc : G.Connected) (large : 3 ≤ lambda G) :
    Fintype.card V + 2 ≤ maxLeaves G + bipartiteNum G := by
  classical
  letI := hc.nonempty
  obtain ⟨r,_,hr⟩ := exists_max_image univ (localInd G) univ_nonempty
  have le : lambda G ≤ localInd G r := Finset.sup_le hr
  let choices := (G.neighborFinset r).powerset.filter (Indep G)
  have ready : choices.Nonempty := ⟨∅,by simp [choices,Indep]⟩
  obtain ⟨A,aM,amax⟩ := exists_max_image choices Finset.card ready
  have leA : localInd G r ≤ A.card := Finset.sup_le amax
  obtain ⟨T,tA,tc⟩ := Finset.exists_subset_card_eq (large.trans (le.trans leA))
  obtain ⟨nA,iA⟩ := mem_filter.mp aM
  have nT : T ⊆ G.neighborFinset r := tA.trans (mem_powerset.mp nA)
  have iT : Indep G T := fun a ha b hb => iA a (tA ha) b (tA hb)
  have notR : r ∉ T := fun h => G.not_mem_neighborFinset_self r (nT h)
  let S := insert r T
  have sc : Graffiti177.Con G S :=
    Graffiti177.con_of_neighbors G (Graffiti177.con_single G r) (by simp [S]) (by
      intro v hv miss
      have ne : v ≠ r := by simpa using miss
      have nv := nT ((mem_insert.mp hv).resolve_left ne)
      exact ⟨r,by simp,((G.mem_neighborFinset r _).mp nv).symm⟩)
  have bc : TwoColor G S := by
    refine ⟨{r},T,disjoint_singleton_left.mpr notR,?_,?_,iT⟩
    · ext v; simp [S]
    · simp [Indep]
  obtain ⟨b⟩ := exists_block G (subset_univ S) sc bc
  obtain ⟨a₁,a₂,a₃,ne₁₂,ne₁₃,ne₂₃,e⟩ := card_eq_three.mp tc
  have inc : ∀ v ∈ T, v ∈ b.A ∪ b.B := fun v h => b.seeded (mem_insert_of_mem h)
  have R := b.seeded (mem_insert_self r T)
  have h1 : a₁ ∈ T := by simp [e]
  have h2 : a₂ ∈ T := by simp [e]
  have h3 : a₃ ∈ T := by simp [e]
  obtain ⟨D,st⟩ := claw_state G b R (inc _ h1) (inc _ h2) (inc _ h3)
    ((G.mem_neighborFinset r _).mp (nT h1)).symm
    ((G.mem_neighborFinset r _).mp (nT h2)).symm
    ((G.mem_neighborFinset r _).mp (nT h3)).symm ne₁₂ ne₁₃ ne₂₃
  exact complete_state G hc (trim_one G) 2 (b.A ∪ b.B) D st ⟨r,R⟩

/-- Graffiti.pc #179 as displayed in the official catalogue: minimum degree. -/
theorem conjecture179 (hc : G.Connected) (hn : 1 < Fintype.card V) :
    G.minDegree + gamma G + lambda G ≤ maxLeaves G + bipartiteNum G :=
  of_leaf_bounds G hc (order_add_one G hc hn) (order_add_two G hc)

#print axioms conjecture179
#print axioms claw_state
end Graffiti179
