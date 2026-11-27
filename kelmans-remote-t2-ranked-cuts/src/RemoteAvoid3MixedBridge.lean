import RemoteAvoid3PortProfiles

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteAvoid3MixedBridge
open SquareCap (FactorOn HasFactor IsTile Port attach cap coord SmallTrivial factor_map)
open RemoteT2CompletionTransfer (eraseEdge SmallerIsolatedAvoid3)
open RemoteAvoid3PortProfiles (SingleReady PairReady four_ports single_ready_of_cap_avoid3 pair_ready_of_cap_root_avoid)

universe u

/-- What the two-edge-handle transport supplies from Avoid3, with the
necessary two-vertex budget included. Only nonincident omitted edges
are needed on the order-four cap. -/
def SmallerRootOmit (n : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V+2<n → Fintype.card V%6=4 →
    (∀ z,G.degree z=3) → SmallTrivial G →
    ∀ x a b : V,G.Adj a b → x≠a → x≠b → FactorOn (eraseEdge G a b) (univ.erase x)

/-- A good cyclic-four cap can supply the residue-four profile at
every marked bridge port. The actual exterior four-port decomposition
is input; the cap coordinate is allowed to choose either valid pairing. -/
theorem single_from_original_shore {V O : Type u} [Fintype V] [Fintype O]
    [DecidableEq V] [DecidableEq O] {G : SimpleGraph V} {J : SimpleGraph O}
    [DecidableRel G.Adj] (p : Port↪V) (r : Port→O) [DecidableRel (attach G J p r).Adj]
    (cub : ∀ u,(attach G J p r).degree u=3) (c4 : SmallTrivial (attach G J p r))
    (large : 4<Fintype.card V) (outside : 1<Fintype.card O) (order : Fintype.card V%6=4)
    (n : ℕ) (less : Fintype.card V+2<n) (smaller : SmallerIsolatedAvoid3.{u} n) (i : Port) :
    SingleReady G (p i) := by
  classical
  obtain ⟨k,ks,_⟩ := SquareCap.cubic_good_cap outside large cub c4
  have orderK : Fintype.card (V⊕Bool)=Fintype.card V+2 := by simp
  have cubK := SquareCap.cap_cubic (fun w=>cub (Sum.inl w)) k
  exact single_ready_of_cap_avoid3 G p k i n (orderK.symm ▸ less) order cubK ks smaller

/-- A good cyclic-four cap can supply the residue-two profile at the
marked bridge port via the specified nonincident root-omission promise.
The domain's two new handle vertices are counted in the strict bound. -/
theorem pair_from_original_shore {V O : Type u} [Fintype V] [Fintype O]
    [DecidableEq V] [DecidableEq O] {G : SimpleGraph V} {J : SimpleGraph O}
    [DecidableRel G.Adj] (p : Port↪V) (r : Port→O) [DecidableRel (attach G J p r).Adj]
    (cub : ∀ u,(attach G J p r).degree u=3) (c4 : SmallTrivial (attach G J p r))
    (large : 4<Fintype.card V) (outside : 1<Fintype.card O) (order : Fintype.card V%6=2)
    (n : ℕ) (less : Fintype.card V+4<n) (smaller : SmallerRootOmit.{u} n) (i : Port) :
    PairReady G (p i) := by
  classical
  obtain ⟨k,ks,_⟩ := SquareCap.cubic_good_cap outside large cub c4
  obtain ⟨j,t,r,ji,_,_,_,_,_,bp,_⟩ := four_ports k i
  let A : V⊕Bool := Sum.inr (!(coord k i))
  let B : V⊕Bool := Sum.inr (coord k i)
  have ab : A≠B := by
    intro e
    have h : (!(coord k i))=coord k i := Sum.inr.inj e
    cases hc : coord k i <;> simp [hc] at h
  have w : (cap G p k).Adj B (Sum.inl (p j)) := by
    change ∃ v,p v=p j∧coord k v=coord k i
    exact ⟨j,rfl,(bp j).mpr (Or.inr rfl)⟩
  have ord : Fintype.card (V⊕Bool)=Fintype.card V+2 := by simp
  have remain := smaller (V⊕Bool) (cap G p k) (by omega) (by omega)
    (SquareCap.cap_cubic (fun w=>cub (Sum.inl w)) k) ks A B (Sum.inl (p j)) w ab Sum.noConfusion
  exact pair_ready_of_cap_root_avoid G p k i j ji bp remain

variable {W : Type*} [DecidableEq W]

private theorem factor_union {G : SimpleGraph W} {S T : Finset W}
    (hs : FactorOn G S) (ht : FactorOn G T) (d : Disjoint S T) :
    FactorOn G (S∪T) := by
  obtain ⟨P,p,q,s⟩ := hs
  obtain ⟨Q,u,v,w⟩ := ht
  have pq {A B : Finset W} (ha : A∈P) (hb : B∈Q) : Disjoint A B := by
    apply disjoint_left.mpr
    intro x xa xb
    exact disjoint_left.mp d (s ▸ mem_biUnion.mpr ⟨A,ha,xa⟩) (w ▸ mem_biUnion.mpr ⟨B,hb,xb⟩)
  refine ⟨P∪Q,?_,?_,?_⟩
  · intro A ha
    exact (mem_union.mp ha).elim (p A) (u A)
  · intro A ha B hb ne
    rcases mem_union.mp ha with hp|hq <;> rcases mem_union.mp hb with kp|kq
    · exact q A hp B kp ne
    · exact pq hp kq
    · exact (pq kp hq).symm
    · exact v A hq B kq ne
  · ext x
    rw [←s,←w,mem_union]
    constructor
    · intro hx
      obtain ⟨A,ha,hax⟩ := mem_biUnion.mp hx
      exact (mem_union.mp ha).elim (fun hp => Or.inl (mem_biUnion.mpr ⟨A,hp,hax⟩))
        (fun hq => Or.inr (mem_biUnion.mpr ⟨A,hq,hax⟩))
    · intro hx
      rcases hx with hp|hq
      · obtain ⟨A,ha,hm⟩ := mem_biUnion.mp hp
        exact mem_biUnion.mpr ⟨A,mem_union_left _ ha,hm⟩
      · obtain ⟨A,ha,hm⟩ := mem_biUnion.mp hq
        exact mem_biUnion.mpr ⟨A,mem_union_right _ ha,hm⟩

private theorem factor_one {G : SimpleGraph W} {S : Finset W} (t : IsTile G S) :
    FactorOn G S := by
  refine ⟨{S},?_,?_,by simp⟩
  · intro A a
    exact (mem_singleton.mp a).symm ▸ t
  · intro A a B b ne
    exact (ne ((mem_singleton.mp a).trans (mem_singleton.mp b).symm)).elim

/-- A marked single-ready shore and a marked pair-ready shore glue
with one crossing P3 centered at the pair-ready endpoint. The only
edge joining the two shores needed for this deduction is q-r. -/
theorem glue_mixed_profiles {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    {G : SimpleGraph L} {H : SimpleGraph R} (X : SimpleGraph (L⊕R))
    (LG : ∀ a b,G.Adj a b → X.Adj (Sum.inl a) (Sum.inl b))
    (RH : ∀ a b,H.Adj a b → X.Adj (Sum.inr a) (Sum.inr b))
    (q : L) (r : R) (bridge : X.Adj (Sum.inl q) (Sum.inr r))
    (single : SingleReady G q) (pair : PairReady H r) : HasFactor X := by
  classical
  obtain ⟨w,rw,rest⟩ := pair
  let l : L↪L⊕R := ⟨Sum.inl,Sum.inl_injective⟩
  let j : R↪L⊕R := ⟨Sum.inr,Sum.inr_injective⟩
  let S := (univ.erase q).map l
  let T := ((univ.erase r).erase w).map j
  let U : Finset (L⊕R) := {Sum.inl q,Sum.inr r,Sum.inr w}
  have d : Disjoint S T := by
    apply disjoint_left.mpr
    intro z zs zt
    obtain ⟨v,_,rfl⟩ := mem_map.mp zs
    obtain ⟨u,_,h⟩ := mem_map.mp zt
    exact Sum.noConfusion h
  have tile : IsTile X U := by
    refine ⟨by simp [U,rw.ne],Sum.inr r,by simp [U],?_⟩
    intro z zm ne
    simp only [U,mem_insert,mem_singleton] at zm
    rcases zm with rfl|rfl|rfl
    · exact bridge.symm
    · contradiction
    · exact RH r w rw
  have restD : Disjoint (S∪T) U := by
    apply disjoint_left.mpr
    intro z zm zu
    simp only [U,mem_insert,mem_singleton] at zu
    rcases mem_union.mp zm with sm|tm
    · obtain ⟨a,az,rfl⟩ := mem_map.mp sm
      have az' : a≠q := (mem_erase.mp az).1
      rcases zu with h|h|h
      · exact az' (Sum.inl.inj h)
      · exact Sum.noConfusion h
      · exact Sum.noConfusion h
    · obtain ⟨a,az,rfl⟩ := mem_map.mp tm
      have wr : a≠w ∧ a≠r := by simpa using az
      rcases zu with h|h|h
      · exact Sum.noConfusion h
      · exact wr.2 (Sum.inr.inj h)
      · exact wr.1 (Sum.inr.inj h)
  have cover : (S∪T)∪U=univ := by
    ext z
    cases z with
    | inl a =>
      by_cases aq : a=q
      · subst a
        simp [U]
      · have hs : (Sum.inl a : L⊕R)∈S := mem_map.mpr ⟨a,by simp [aq],rfl⟩
        simp [hs]
    | inr a =>
      by_cases ar : a=r
      · subst a
        simp [U]
      · by_cases aw : a=w
        · subst a
          simp [U]
        · have ht : (Sum.inr a : L⊕R)∈T := mem_map.mpr ⟨a,by simp [ar,aw],rfl⟩
          simp [ht]
  change FactorOn X univ
  rw [←cover]
  exact factor_union (factor_union (factor_map l LG single) (factor_map j RH rest) d)
    (factor_one tile) restD


/-- A four-vertex 2-regular shore is single-ready at every vertex.
Its nonneighbor has exactly the two other surviving vertices as neighbors. -/
theorem four_vertex_single {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : Fintype.card V=4)
    (deg : ∀ z,G.degree z=2) (q : V) : SingleReady G q := by
  classical
  let F := insert q (G.neighborFinset q)
  have fq : q∉G.neighborFinset q := fun h=>G.loopless q ((mem_neighborFinset _ _ _).mp h)
  have hF : F.card=3 := by rw [show F=insert q (G.neighborFinset q) from rfl,
    card_insert_of_not_mem fq,card_neighborFinset_eq_degree,deg]
  have g : ∃ w : V,w∉F := by
    by_contra! all
    have eq : F=univ := eq_univ_of_forall all
    rw [eq,card_univ,n] at hF
    omega
  obtain ⟨w,hw⟩ := g
  have wq : w≠q := fun h=>hw (mem_insert.mpr (Or.inl h))
  have no : ¬G.Adj w q := fun h=>hw (mem_insert.mpr (Or.inr ((mem_neighborFinset _ _ _).mpr h.symm)))
  let T : Finset V := univ.erase q
  let S := T.erase w
  have wt : w∈T := by simp [T,wq]
  have hcT : T.card=3 := by rw [show T=univ.erase q from rfl,
    card_erase_of_mem (mem_univ _),card_univ,n]
  have hcS : S.card=2 := by rw [show S=T.erase w from rfl,card_erase_of_mem wt,hcT]
  have inc : G.neighborFinset w ⊆ S := by
    intro z zG
    have wz := (mem_neighborFinset _ _ _).mp zG
    have zq : z≠q := fun h=>no (h ▸ wz)
    exact mem_erase.mpr ⟨wz.ne.symm,mem_erase.mpr ⟨zq,mem_univ _⟩⟩
  have eq : G.neighborFinset w = S := Finset.eq_of_subset_of_card_le inc (by
    rw [hcS,card_neighborFinset_eq_degree,deg])
  apply factor_one
  refine ⟨hcT,w,wt,?_⟩
  intro z zt zw
  apply (mem_neighborFinset _ _ _).mp
  rw [eq]
  exact mem_erase.mpr ⟨zw,zt⟩

/-- The four-port reflection supplies the small residue-four case too:
the embedding is onto on four vertices, hence cubicity of the original
attachment makes every vertex degree two inside this shore. -/
theorem tiny_from_original_shore {V O : Type u} [Fintype V] [Fintype O]
    [DecidableEq V] [DecidableEq O] {G : SimpleGraph V} {J : SimpleGraph O}
    [DecidableRel G.Adj] (p : Port↪V) (r : Port→O) [DecidableRel (attach G J p r).Adj]
    (cub : ∀ u,(attach G J p r).degree u=3) (ord : Fintype.card V=4) (q : V) :
    SingleReady G q := by
  classical
  apply four_vertex_single G ord
  have pn : Fintype.card Port=4 := by simp [SquareCap.Port]
  have onto := ((Fintype.bijective_iff_injective_and_card p).mpr ⟨p.injective,pn.trans ord.symm⟩).2
  intro z
  obtain ⟨i,hi⟩ := onto z
  have e : ((univ : Finset Port).filter (fun u=>p u=z))={i} := by
    ext v
    simp only [mem_filter,mem_univ,true_and,mem_singleton,←hi,EmbeddingLike.apply_eq_iff_eq]
  have d := cub (Sum.inl z)
  rw [SquareCap.attach_degree_outside,e,card_singleton] at d
  omega

/-- End-to-end mixed-residue stitching with checked four-port
attachments supplied for both shores. The residue-four shore
may be the four-vertex minimum. The two-vertex shortfall in the
ambient order pays for the extra root-handle vertices. -/
theorem mixed_from_original_shores {L R OL OR : Type u}
    [Fintype L] [Fintype R] [Fintype OL] [Fintype OR]
    [DecidableEq L] [DecidableEq R] [DecidableEq OL] [DecidableEq OR]
    {G : SimpleGraph L} {H : SimpleGraph R} {JL : SimpleGraph OL} {JR : SimpleGraph OR}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (pL : Port↪L) (rL : Port→OL) (pR : Port↪R) (rR : Port→OR)
    [DecidableRel (attach G JL pL rL).Adj] [DecidableRel (attach H JR pR rR).Adj]
    (cL : ∀ x,(attach G JL pL rL).degree x=3)
    (cR : ∀ x,(attach H JR pR rR).degree x=3)
    (sL : SmallTrivial (attach G JL pL rL)) (sR : SmallTrivial (attach H JR pR rR))
    (oL : Fintype.card L%6=4) (oR : Fintype.card R%6=2)
    (outL : 1<Fintype.card OL) (outR : 1<Fintype.card OR)
    (n : ℕ) (esize : Fintype.card L+Fintype.card R+2≤n)
    (avo : SmallerIsolatedAvoid3.{u} n) (rt : SmallerRootOmit.{u} n)
    (X : SimpleGraph (L⊕R))
    (LG : ∀ a b,G.Adj a b → X.Adj (Sum.inl a) (Sum.inl b))
    (RH : ∀ a b,H.Adj a b → X.Adj (Sum.inr a) (Sum.inr b))
    (i j : Port) (bridge : X.Adj (Sum.inl (pL i)) (Sum.inr (pR j))) :
    HasFactor X := by
  have pn : Fintype.card Port=4 := by simp [SquareCap.Port]
  have LL := Fintype.card_le_of_injective pL pL.injective
  have RR := Fintype.card_le_of_injective pR pR.injective
  rw [pn] at LL RR
  have single : SingleReady G (pL i) := by
    by_cases hl : Fintype.card L=4
    · exact tiny_from_original_shore pL rL cL hl (pL i)
    · exact single_from_original_shore pL rL cL sL (by omega) outL oL n (by omega) avo i
  have pair := pair_from_original_shore pR rR cR sR (by omega) outR oR n (by omega) rt j
  exact glue_mixed_profiles X LG RH (pL i) (pR j) bridge single pair

#print axioms mixed_from_original_shores
#print axioms tiny_from_original_shore

#print axioms single_from_original_shore
#print axioms pair_from_original_shore
#print axioms glue_mixed_profiles
end KelmansCactus.AtomicBridge.RemoteAvoid3MixedBridge
