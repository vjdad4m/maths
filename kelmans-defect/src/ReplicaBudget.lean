import Substitute

open Finset
namespace KelmansCactus.ReplicaBudget
open ThreePort Substitute
variable {V I : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] in
/-- Each tile on a divisible region has three vertices; more generally
every explicitly factored region has order divisible by three. -/
theorem closed_card {S : Finset V} (h : Closed G S) : 3 ∣ S.card := by
  obtain ⟨P,hP⟩ := h
  have d : (P : Set (Finset V)).PairwiseDisjoint id :=
    fun u hu v hv ne => hP.disj _ hu _ hv ne
  rw [← hP.cover,card_biUnion d]
  apply Finset.dvd_sum
  intro t ht
  change 3 ∣ t.card
  rw [(hP.tile t ht).1]

private theorem rest_closed {P : Finset (Finset V)} (hf : Factor G P)
    (D W : Finset V) (ex : ∀ u ∈ D, ∀ v ∉ D, G.Adj u v → v ∈ W) :
    Closed G (D \ (P.filter fun t => ¬Disjoint t W).biUnion id) := by
  classical
  let E := P.filter (fun t => ¬Disjoint t W)
  let Q := P.filter (fun t => t ⊆ D ∧ Disjoint t W)
  have sub : Q ⊆ P := filter_subset _ _
  refine ⟨Q,⟨fun t ht => hf.tile t (sub ht),fun u hu v hv ne => hf.disj u (sub hu) v (sub hv) ne,?_⟩⟩
  ext x
  change x ∈ Q.biUnion id ↔ x ∈ D \ E.biUnion id
  constructor
  · intro hx
    obtain ⟨t,ht,tx⟩ := mem_biUnion.mp hx
    obtain ⟨tp,ts,tn⟩ := mem_filter.mp ht
    refine mem_sdiff.mpr ⟨ts tx,?_⟩
    intro hxE
    obtain ⟨r,hr,rx⟩ := mem_biUnion.mp hxE
    obtain ⟨rp,rn⟩ := mem_filter.mp hr
    by_cases he : t = r
    · exact rn (he ▸ tn)
    · exact disjoint_left.mp (hf.disj _ tp _ rp he) tx rx
  · intro hx
    obtain ⟨xd,xn⟩ := mem_sdiff.mp hx
    have exP : x ∈ P.biUnion id := hf.cover.symm ▸ mem_univ _
    obtain ⟨t,tp,tx⟩ := mem_biUnion.mp exP
    have td : Disjoint t W := by
      by_contra tn
      exact xn (mem_biUnion.mpr ⟨t,mem_filter.mpr ⟨tp,tn⟩,tx⟩)
    have ts : t ⊆ D := by
      intro v vt
      by_contra vd
      obtain ⟨w,wt,ww⟩ := SpareChord.mixed_has_port G ex (hf.tile t tp)
        ⟨⟨x,tx,xd⟩,⟨v,vt,vd⟩⟩
      exact disjoint_left.mp td wt ww
    exact mem_biUnion.mpr ⟨t,mem_filter.mpr ⟨tp,ts,td⟩,tx⟩

/-- Boundary capacity: with three-vertex tiles, each selected boundary
tile covers at least one of the h boundary vertices and offers at most two
outside vertices. Every nonfactorable divisible cell must use at least
three such outside vertices. Thus 3*k ≤ 2*h for k disjoint bad cells.
The cells need not be connected or have matching seams. -/
theorem defect_budget (J : Finset I) (D : I → Finset V) (W : Finset V)
    (cells : (J : Set I).PairwiseDisjoint D)
    (outside : ∀ i ∈ J, Disjoint (D i) W)
    (exits : ∀ i ∈ J, ∀ u ∈ D i, ∀ v ∉ D i, G.Adj u v → v ∈ W)
    (div : ∀ i ∈ J, 3 ∣ (D i).card)
    (bad : ∀ i ∈ J, ¬ Closed G (D i))
    (has : KelmansStarter.HasP3Factor G) :
    3*J.card ≤ 2*W.card := by
  classical
  obtain ⟨P,ht,hd,hc⟩ := has
  have hf : Factor G P := ⟨ht,hd,hc⟩
  let E := P.filter (fun t => ¬Disjoint t W)
  let T := E.biUnion id
  have Esub : E ⊆ P := filter_subset _ _
  have Edis : (E : Set (Finset V)).PairwiseDisjoint id :=
    fun s hs t ht' ne => hf.disj _ (Esub hs) _ (Esub ht') ne
  have Wsub : W ⊆ T := by
    intro v vw
    have h := hf.cover.symm ▸ (mem_univ v)
    obtain ⟨t,tp,tv⟩ := mem_biUnion.mp h
    have en : ¬Disjoint t W := fun h => disjoint_left.mp h tv vw
    exact mem_biUnion.mpr ⟨t,mem_filter.mpr ⟨tp,en⟩,tv⟩
  have Et : T.card = E.card * 3 := by
    change (E.biUnion id).card = E.card*3
    rw [card_biUnion Edis]
    calc
      _ = ∑ t ∈ E, 3 := Finset.sum_congr rfl (fun t ht' => (hf.tile t (Esub ht')).1)
      _ = _ := by simp
  have intersect_dis : (E : Set (Finset V)).PairwiseDisjoint (fun t => t ∩ W) :=
    fun s hs t ht' ne => (Edis hs ht' ne).mono inter_subset_left inter_subset_left
  have se : E.biUnion (fun t => t ∩ W) = W := by
    ext v
    rw [← Finset.biUnion_inter]
    constructor
    · intro hv
      exact (mem_inter.mp hv).2
    · intro hv
      exact mem_inter.mpr ⟨Wsub hv,hv⟩
  have E_le_W : E.card ≤ W.card := by
    rw [← se,card_biUnion intersect_dis]
    calc
      E.card = ∑ _ ∈ E, 1 := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro t ht'
        have ne := (mem_filter.mp ht').2
        apply card_pos.mpr
        by_contra no
        apply ne
        apply disjoint_left.mpr
        intro v tv vw
        exact no ⟨v,mem_inter.mpr ⟨tv,vw⟩⟩
  have cap : (T \ W).card ≤ 2*W.card := by
    have eq := card_sdiff_add_card_eq_card Wsub
    omega
  have need (i : I) (hi : i ∈ J) : 3 ≤ ((D i) ∩ T).card := by
    have hlocal : Closed G ((D i) \ T) := rest_closed hf _ _ (exits i hi)
    have r := closed_card hlocal
    have b := div i hi
    have t_sum := card_sdiff_add_card_inter (D i) T
    have nz : ((D i) ∩ T).card ≠ 0 := by
      intro hz
      have eq : D i \ T = D i := by
        ext v
        constructor
        · exact fun h => (mem_sdiff.mp h).1
        · intro hd
          apply mem_sdiff.mpr
          refine ⟨hd,?_⟩
          intro ht
          have e := Finset.card_eq_zero.mp hz
          have m : v ∈ D i ∩ T := mem_inter.mpr ⟨hd,ht⟩
          rw [e] at m
          exact (not_mem_empty _ m)
      exact bad i hi (eq ▸ hlocal)
    omega
  have rank : (J : Set I).PairwiseDisjoint (fun i => (D i) ∩ T) :=
    fun i hi j hj ne => (cells hi hj ne).mono inter_subset_left inter_subset_left
  calc
    3*J.card = ∑ i ∈ J, 3 := by simp [mul_comm]
    _ ≤ ∑ i ∈ J, ((D i) ∩ T).card := sum_le_sum need
    _ = (J.biUnion (fun i => (D i) ∩ T)).card := (card_biUnion rank).symm
    _ ≤ (T \ W).card := by
      apply card_le_card
      intro v hv
      obtain ⟨i,hi,vi⟩ := mem_biUnion.mp hv
      obtain ⟨dv,tv⟩ := mem_inter.mp vi
      exact mem_sdiff.mpr ⟨tv,fun vw => disjoint_left.mp (outside i hi) dv vw⟩
    _ ≤ 2*W.card := cap

theorem three_replica_obstruction (D : Fin 3 → Finset V) (W : Finset V)
    (cells : (↑(univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint D)
    (outside : ∀ i, Disjoint (D i) W)
    (exits : ∀ i, ∀ u ∈ D i, ∀ v ∉ D i, G.Adj u v → v ∈ W)
    (div : ∀ i, 3 ∣ (D i).card)
    (bad : ∀ i, ¬ Closed G (D i))
    (hW : W.card = 3) :
    ¬ KelmansStarter.HasP3Factor G := by
  intro has
  have b := defect_budget univ D W cells (fun i _ => outside i) (fun i _ => exits i)
    (fun i _ => div i) (fun i _ => bad i) has
  simp [hW] at b

#print axioms defect_budget
#print axioms three_replica_obstruction
end KelmansCactus.ReplicaBudget
