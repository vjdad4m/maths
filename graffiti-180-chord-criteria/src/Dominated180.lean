import Mandatory180

set_option warningAsError true
namespace Assembly180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- Every spanning tree of order at least three has an internal vertex in
the graph's closed neighborhood of any specified vertex. -/
private theorem internal_near (T : SimpleGraph V) (tr : T.IsTree) (hn : 2<Fintype.card V)
    (y : V) : ∃ w, (w=y ∨ T.Adj y w) ∧ w∉leaves T := by
  classical
  by_cases yl : y∈leaves T
  · obtain ⟨w,yw⟩ := exists_adj T tr.isConnected (by omega) y
    obtain ⟨k,kn⟩ : ∃ k, k∉({y,w} : Finset V) := by
      by_contra! no
      have h := card_le_card (show univ ⊆ ({y,w}:Finset V) from fun v _ => no v)
      rw [card_univ,card_pair yw.ne] at h
      omega
    have ky : y≠k := fun h => kn (h ▸ mem_insert_self _ _)
    have kw : w≠k := fun h => kn (h ▸ mem_insert_of_mem (mem_singleton_self _))
    obtain ⟨a,ya,da⟩ := Graffiti169.exists_predecessor T tr.isConnected k y ky
    obtain ⟨b,wb,db⟩ := Graffiti169.exists_predecessor T tr.isConnected k w kw
    have e := leaf_unique T yl ya yw
    refine ⟨w,Or.inr yw,fun wl => ?_⟩
    have e' := leaf_unique T wl wb yw.symm
    rw [e] at da
    rw [e'] at db
    omega
  · exact ⟨y,Or.inl rfl,yl⟩

/-- The eligible new vertex can be hung from an internal old vertex,
preserving all the old optimum's eligible leaves. -/
theorem gain_at (hc : G.Connected) (hn : 2<Fintype.card V) (N U : Finset V)
    (x : V) (xn : x∈N) :
    weightedLeaves G (U.erase x)+1 ≤ weightedLeaves (ear G N) (U.disjSum univ) := by
  classical
  obtain ⟨T,ts,tr,eq⟩ := tree_opt G hc (U.erase x)
  obtain ⟨K,ks,kt⟩ := (ear_connected T tr.isConnected {x} (singleton_nonempty _)).exists_isTree_le
  have sub : K ≤ ear G N := by
    rintro (a|a) (b|b) e
    all_goals have h := ks e
    · exact ts h
    · exact (mem_singleton.mp (show a∈({x}:Finset V) from h)) ▸ xn
    · exact (mem_singleton.mp (show b∈({x}:Finset V) from h)) ▸ xn
    · exact h.elim
  have size : 1<Fintype.card (V ⊕ Unit) := by simp [Fintype.card_sum]; omega
  have inc : (U.erase x ∩ leaves T).disjSum (univ : Finset Unit) ⊆ (U.disjSum univ) ∩ leaves K := by
    rintro (v|v) h
    · obtain ⟨vu,vl⟩ := mem_inter.mp (inl_mem_disjSum.mp h)
      have ne : v≠x := (mem_erase.mp vu).1
      apply mem_inter.mpr
      refine ⟨inl_mem_disjSum.mpr (mem_of_mem_erase vu),leaf_of_unique K kt.isConnected size _ ?_⟩
      rintro (a|a) (b|b) ea eb
      all_goals have ha := ks ea
      all_goals have hb := ks eb
      · exact congrArg Sum.inl (leaf_unique T vl ha hb)
      · exact (ne (mem_singleton.mp (show v∈({x}:Finset V) from hb))).elim
      · exact (ne (mem_singleton.mp (show v∈({x}:Finset V) from ha))).elim
      · exact congrArg Sum.inr (Subsingleton.elim _ _)
    · refine mem_inter.mpr ⟨inr_mem_disjSum.mpr (mem_univ _),leaf_of_unique K kt.isConnected size _ ?_⟩
      rintro (a|a) (b|b) ea eb
      all_goals have ha := ks ea
      all_goals have hb := ks eb
      · exact congrArg Sum.inl ((mem_singleton.mp (show a∈({x}:Finset V) from ha)).trans
          (mem_singleton.mp (show b∈({x}:Finset V) from hb)).symm)
      · exact hb.elim
      · exact ha.elim
      · exact ha.elim
  have b := (card_le_card inc).trans (le_sup (f:=fun M => ((U.disjSum (univ : Finset Unit)) ∩ leaves M).card)
    (s:=univ.filter (fun M : SimpleGraph (V ⊕ Unit) => M≤ear G N ∧ M.IsTree)) (mem_filter.mpr ⟨mem_univ _,sub,kt⟩))
  change _ ≤ weightedLeaves (ear G N) (U.disjSum univ) at b
  simpa only [card_disjSum,card_univ,Fintype.card_unit,eq] using b

theorem gain_of_internal (hn : 2<Fintype.card V) (N U : Finset V)
    (T : SimpleGraph V) (ts : T ≤ G) (tr : T.IsTree) (eq : (U ∩ leaves T).card=weightedLeaves G U)
    (x : V) (xn : x∈N) (xl : x∉leaves T) :
    weightedLeaves G U+1 ≤ weightedLeaves (ear G N) (U.disjSum univ) := by
  classical
  have score : (U.erase x ∩ leaves T).card ≤ weightedLeaves G (U.erase x) :=
    le_sup (f:=fun K => (U.erase x ∩ leaves K).card) (mem_filter.mpr ⟨mem_univ _,ts,tr⟩)
  rw [erase_inter,erase_eq_of_not_mem (fun h => xl (mem_inter.mp h).2),eq] at score
  exact (Nat.add_le_add_right score 1).trans (gain_at G (tr.isConnected.mono ts) hn N U x xn)

theorem dominated_gain (hc : G.Connected) (hn : 2<Fintype.card V) (N U : Finset V)
    (y : V) (yn : y∈N) (dom : ∀ w, G.Adj y w → w∈N) :
    weightedLeaves G U+1 ≤ weightedLeaves (ear G N) (U.disjSum univ) := by
  classical
  obtain ⟨T,ts,tr,eq⟩ := tree_opt G hc U
  obtain ⟨x,xp,xl⟩ := internal_near T tr hn y
  have xn : x∈N := xp.elim (fun h => h ▸ yn) (fun e => dom x (ts e))
  exact gain_of_internal G hn N U T ts tr eq x xn xl

theorem without_new (N : Finset V) :
    bipartiteNum G ≤ without (ear G N) (.inr ()) := by
  classical
  apply Finset.sup_le
  intro S h
  obtain ⟨A,B,dis,eq,ai,bi⟩ := (mem_filter.mp h).2
  let lift (F : Finset V) := F.disjSum (∅ : Finset Unit)
  have ind (F : Finset V) (i : Indep G F) : Indep (ear G N) (lift F) := by
    rintro (a|a) ha (b|b) hb ne e
    · exact i _ (inl_mem_disjSum.mp ha) _ (inl_mem_disjSum.mp hb) (fun eq => ne (congrArg Sum.inl eq)) e
    · simp [lift] at hb
    · simp [lift] at ha
    · simp [lift] at ha
  have ok : TwoColor (ear G N) (lift S) := by
    refine ⟨lift A,lift B,?_,?_,ind _ ai,ind _ bi⟩
    · apply disjoint_left.mpr
      rintro (a|a) h k
      · exact disjoint_left.mp dis (inl_mem_disjSum.mp h) (inl_mem_disjSum.mp k)
      · simp [lift] at h
    · rw [← eq]
      ext v; cases v <;> simp [lift]
  have bound : (lift S).card ≤ without (ear G N) (.inr ()) := by
    apply le_sup (f:=card)
    refine mem_filter.mpr ⟨mem_powerset.mpr ?_,ok⟩
    rintro (a|a) h
    · exact mem_erase.mpr ⟨fun e => Sum.noConfusion e,mem_univ _⟩
    · simp [lift] at h
  simpa [lift] using bound

theorem new_vertex_counts (N : Finset V) (r : V) (odd : Bool) (A : Finset (V ⊕ Unit))
    (par : pull Sum.inl (parity (ear G N) (.inl r) odd)=parity G r odd)
    (once : let P := parity (ear G N) (.inl r) odd
            (.inr ()∈A ∨ .inr ()∈P) ∧ ¬(.inr ()∈A ∧ .inr ()∈P)) :
    let P := parity (ear G N) (.inl r) odd
    let B := pull Sum.inl A
    let Q := parity G r odd
    eligible A P (.inl r)=(eligible B Q r).disjSum (univ : Finset Unit) ∧
      A.card+P.card=B.card+Q.card+1 := by
  classical
  let H := ear G N
  let P := parity H (.inl r) odd
  let B := pull Sum.inl A
  let Q := parity G r odd
  let U := eligible B Q r
  have pi (v : V) : Sum.inl v∈P ↔ v∈Q := by
    change _ ↔ v∈parity G r odd
    rw [← par]
    exact mem_pull.symm
  have sel : eligible A P (.inl r) = U.disjSum (univ : Finset Unit) := by
    ext v
    rcases v with a|i
    · simp only [inl_mem_disjSum,U,eligible_iff,pi,B,mem_pull,Sum.inl.injEq]
      rw [show ((Sum.inl a : V ⊕ Unit) ≠ Sum.inl r) ↔ a≠r from not_congr Sum.inl.inj_iff]
    · cases i
      simp only [inr_mem_disjSum,mem_univ,iff_true,eligible_iff,Sum.inr_ne_inl,not_false_eq_true,true_or,and_true]
      exact ⟨once.1,Or.inl (fun e => Sum.noConfusion e)⟩
  have ca := split_card A
  have cp := split_card P
  change A.card=B.card+_ at ca
  change pull Sum.inl P=Q at par
  rw [par] at cp
  have one (K : Finset (V ⊕ Unit)) : (pull Sum.inr K).card=weight (Sum.inr ()) K := by
    by_cases h : Sum.inr ()∈K
    · have full : pull Sum.inr K=univ := by ext i; cases i; simp [h]
      simp [full,weight,h]
    · have nil : pull Sum.inr K=∅ := by ext i; cases i; simp [h]
      simp [nil,weight,h]
  rw [one] at ca cp
  have sum : weight (.inr ()) A+weight (.inr ()) P=1 := by
    change (Sum.inr ()∈A ∨ Sum.inr ()∈P) ∧ ¬(Sum.inr ()∈A ∧ Sum.inr ()∈P) at once
    rcases once with ⟨h,no⟩
    rcases h with h|h
    · simp [weight,h,show Sum.inr ()∉P from fun p => no ⟨h,p⟩]
    · simp [weight,h,show Sum.inr ()∉A from fun a => no ⟨a,h⟩]
  refine ⟨sel,?_⟩
  change A.card+P.card=B.card+Q.card+1
  omega

/-- A tight state with an eligible terminal outside the overlap cannot
also require that terminal in every maximum bipartite set if the unchanged
old parity satisfies the local bound. The next triangle on *any* edge at
that terminal increases bipartite order. -/
theorem rank_grows_of_optimum (hn : 2<Fintype.card V) (N : Finset V)
    (r : V) (odd : Bool) (A : Finset (V ⊕ Unit)) (ai : Indep (ear G N) A)
    (par : pull Sum.inl (parity (ear G N) (.inl r) odd) = parity G r odd)
    (old : localBound G r (parity G r odd))
    (once : let P := parity (ear G N) (.inl r) odd
            (.inr ()∈A ∨ .inr ()∈P) ∧ ¬(.inr ()∈A ∧ .inr ()∈P))
    (tight : let P := parity (ear G N) (.inl r) odd
             weightedLeaves (ear G N) (eligible A P (.inl r))+bipartiteNum (ear G N)=1+A.card+P.card)
    (internal : let U := eligible (pull Sum.inl A) (parity G r odd) r
                ∃ T ≤ G, T.IsTree ∧ (U ∩ leaves T).card=weightedLeaves G U ∧
                  ∃ x∈N, x∉leaves T)
    (w : V) (wn : w∈N) :
    let H := ear G N
    bipartiteNum (ear H {Sum.inl w,Sum.inr ()})=bipartiteNum H+1 := by
  classical
  let H := ear G N
  let P := parity H (.inl r) odd
  let B := pull Sum.inl A
  let Q := parity G r odd
  let U := eligible B Q r
  obtain ⟨sel,count⟩ := new_vertex_counts G N r odd A par once
  change eligible A P (.inl r)=U.disjSum univ at sel
  change A.card+P.card=B.card+Q.card+1 at count
  have ib : Indep G B := fun v hv a ha ne e =>
    ai _ (mem_pull.mp hv) _ (mem_pull.mp ha) (fun eq => ne (Sum.inl.inj eq)) e
  have o := old B ib
  change 1+B.card+Q.card ≤ weightedLeaves G U+bipartiteNum G at o
  obtain ⟨K,ks,kt,eq,x,xn,xl⟩ := internal
  have leaf := gain_of_internal G hn N U K ks kt eq x xn xl
  change weightedLeaves H (eligible A P (.inl r))+bipartiteNum H=1+A.card+P.card at tight
  rw [sel] at tight
  change _ ≤ weightedLeaves H _ at leaf
  have rank := without_new G N
  change bipartiteNum G ≤ without H (.inr ()) at rank
  have le (a) : without H a ≤ bipartiteNum H := by
    apply Finset.sup_le
    intro X hx
    exact le_sup (f:=card) (mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩)
  have rankx := le (Sum.inr ())
  have rankw := le (Sum.inl w)
  have step := triangle_rank_exchange H (.inl w) (.inr ()) wn
  dsimp only
  change bipartiteNum (ear H {Sum.inl w,Sum.inr ()})=bipartiteNum H+1
  omega

/-- A closed neighborhood contained in N supplies the required internal
neighbor in every old spanning tree. -/
theorem rank_grows (hc : G.Connected) (hn : 2<Fintype.card V) (N : Finset V)
    (y : V) (yn : y∈N) (dom : ∀ w, G.Adj y w → w∈N)
    (r : V) (odd : Bool) (A : Finset (V ⊕ Unit)) (ai : Indep (ear G N) A)
    (par : pull Sum.inl (parity (ear G N) (.inl r) odd) = parity G r odd)
    (old : localBound G r (parity G r odd))
    (once : let P := parity (ear G N) (.inl r) odd
            (.inr ()∈A ∨ .inr ()∈P) ∧ ¬(.inr ()∈A ∧ .inr ()∈P))
    (tight : let P := parity (ear G N) (.inl r) odd
             weightedLeaves (ear G N) (eligible A P (.inl r))+bipartiteNum (ear G N)=1+A.card+P.card)
    (w : V) (wn : w∈N) :
    let H := ear G N
    bipartiteNum (ear H {Sum.inl w,Sum.inr ()})=bipartiteNum H+1 := by
  apply rank_grows_of_optimum G hn N r odd A ai par old once tight _ w wn
  let U := eligible (pull Sum.inl A) (parity G r odd) r
  obtain ⟨K,ks,kt,eq⟩ := tree_opt G hc U
  obtain ⟨x,xp,xl⟩ := internal_near K kt hn y
  exact ⟨K,ks,kt,eq,x,xp.elim (fun h => h ▸ yn) (fun e => dom x (ks e)),xl⟩

#print axioms gain_at
#print axioms gain_of_internal
#print axioms rank_grows_of_optimum
#print axioms dominated_gain
#print axioms rank_grows
end Assembly180
