import CreditSampling31

namespace Graffiti384b.EarCredit
open SimpleGraph Finset EarAnchor HighEar
open private TrianglePrune.triangle_iff from TrianglePrune384b
open private Repair.full_nbr Repair.triangles_le_choose from Repair384b
open private FiniteRange.bad from FiniteRange384b
open private ThreeChoice.balance from ThreeBudget33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

private theorem necessary_mass {e a b : V} (ea : H.Adj e a) (eb : H.Adj e b) (ab : a≠b)
    (ear : H.neighborFinset e={a,b}) (hi : 15≤gamma H) (ws : (outside e a b).card=27) :
    let W := outside e a b
    4*(27:ℕ).choose 9≤∑ v∈W,((W.powersetCard 9).filter (fun k => v∈FiniteRange.bad H W k)).card := by
  classical
  let W := outside e a b
  let A : Finset V := {a,b}
  let K := W.powersetCard 9
  let F := FiniteRange.bad H W
  have cnt (k : Finset V) (km : k∈K) : 4≤(F k).card := by
    let D := A∪k∪F k
    have am : a∈D := mem_union_left _ (mem_union_left _ (mem_insert_self ..))
    have bm : b∈D := mem_union_left _ (mem_union_left _ (mem_insert_of_mem (mem_singleton_self _)))
    have dom : TwoDominates H D := by
      intro v out
      by_cases ve : v=e
      · exact ve ▸ PinnedColor34.two H ab ea eb am bm
      have va : v≠a := fun h => out (h ▸ am)
      have vb : v≠b := fun h => out (h ▸ bm)
      have vm : v∈W := outside_mem.mpr ⟨ve,va,vb⟩
      have vk : v∉k := fun m => out (mem_union_left _ (mem_union_right _ m))
      have good : 2≤nbr H v (Wᶜ∪k) := Nat.le_of_not_gt (fun low => out
        (mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨vm,vk⟩,low⟩)))
      apply good.trans (card_le_card ?_)
      intro y ym; obtain ⟨m,vy⟩ := mem_filter.mp ym; refine mem_filter.mpr ⟨?_,vy⟩
      rcases mem_union.mp m with off|yk
      · have z : y=e ∨ y=a ∨ y=b := by simpa [W,outside] using off
        rcases z with rfl|rfl|rfl
        · have h := (H.mem_neighborFinset ..).mpr vy.symm
          rw [ear,mem_insert,mem_singleton] at h; exact (h.elim va vb).elim
        · exact am
        · exact bm
      · exact mem_union_left _ (mem_union_right _ yk)
    have lb := hi.trans (show gamma H≤D.card from Nat.sInf_le ⟨_,dom,rfl⟩)
    have h := card_union_le (A∪k) (F k); have h' := card_union_le A k
    have sz : A.card=2 := card_pair ab
    have ks := (mem_powersetCard.mp km).2
    change D.card≤_ at h; omega
  have low := sum_le_sum cnt
  have sub (k : Finset V) : F k⊆W := (filter_subset ..).trans sdiff_subset
  have eq : (∑ k∈K,(F k).card)=∑ v∈W,(K.filter (fun k => v∈F k)).card := by
    calc _ = ∑ k∈K,∑ w∈W,if w∈F k then 1 else 0 := by
           apply sum_congr rfl; intro k _; simp [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (sub k)]
         _ = _ := by rw [sum_comm]; simp [sum_boole]
  have ks : K.card=(27:ℕ).choose 9 := by change (W.powersetCard 9).card=_; rw [card_powersetCard,show W.card=27 from ws]
  rw [eq,sum_const,nsmul_eq_mul,Nat.cast_id,ks,Nat.mul_comm] at low; exact low

/-- A five-clique-free order-30 core with distinct positive triangle counts,
a triangular ear and the degree-four score-five pivot saves one vertex. -/
theorem core_bound (n : Fintype.card V=30) (free : H.CliqueFree 5)
    (pos : ∀ v,0<trianglesAt H v) (fi : Function.Injective (trianglesAt H))
    {e x : V} (de : H.degree e=2) (one : trianglesAt H e=1) (dx : H.degree x=4)
    (sx : trianglesAt H x=5) (rest : ∀ w,w≠e → 3≤H.degree w) : gamma H≤14 := by
  classical
  by_contra! hi
  have half : Fintype.card V≤2*gamma H := by omega
  obtain ⟨a,b,ea,eb,ab⟩ := (TrianglePrune.triangle_iff H e).mp (pos e)
  have ear : H.neighborFinset e={a,b} := (eq_of_subset_of_card_le (insert_subset
    ((H.mem_neighborFinset ..).mpr ea) (singleton_subset_iff.mpr ((H.mem_neighborFinset ..).mpr eb)))
    (by rw [card_pair ab.ne,card_neighborFinset_eq_degree,de])).symm
  obtain ⟨r,L⟩ := ledger H n de one pos fi free hi
  obtain ⟨da,db,ds⟩ := L.degree_sum de ea eb ab.ne
  let W := outside e a b
  let A : Finset V := {a,b}
  let C := additional H e a b
  let j (v : V) := nbr H v A
  let bill (v : V) := ((W.powersetCard 9).filter (fun k => v∈FiniteRange.bad H W k)).card
  have ws : W.card=27 := by simp [W,outside,card_compl,ea.ne,eb.ne,ab.ne,n]
  have aw : Disjoint A W := disjoint_left.mpr (by
    intro v am wm; have z := outside_mem.mp wm
    exact (mem_insert.mp am).elim z.2.1 (fun s => z.2.2 (mem_singleton.mp s)))
  have xa : x≠a := fun h => by subst x; omega
  have xb : x≠b := fun h => by subst x; omega
  have xne : x≠e := fun h => by subst x; omega
  have xm : x∈W := outside_mem.mpr ⟨xne,xa,xb⟩
  have xe : ¬H.Adj x e := by
    intro edge; have z := (H.mem_neighborFinset ..).mpr edge.symm
    rw [ear,mem_insert,mem_singleton] at z; exact z.elim xa xb
  obtain ⟨touch,both⟩ := pivot_contacts H ea eb ab.ne xe xa xb xne dx sx rest half
  have jlim (v : V) : j v≤2 := (card_filter_le ..).trans_eq (card_pair ab.ne)
  have two (v : V) : j v=2 ↔ H.Adj v a ∧ H.Adj v b := by
    by_cases aa : H.Adj v a <;> by_cases bb : H.Adj v b <;> simp [j,A,nbr,filter_insert,filter_singleton,aa,bb,ab.ne]
  have seen {v : V} (h : H.Adj v a ∨ H.Adj v b) : 1≤j v := by
    rcases h with h|h
    · exact card_pos.mpr ⟨a,mem_filter.mpr ⟨mem_insert_self ..,h⟩⟩
    · exact card_pos.mpr ⟨b,mem_filter.mpr ⟨mem_insert_of_mem (mem_singleton_self _),h⟩⟩
  have ceq : W.filter (fun v => j v=2)=C := by
    ext v; rw [mem_filter,two,show v∈C ↔ _ from additional_mem H]
    exact ⟨fun ⟨wm,h,g⟩ => ⟨(outside_mem.mp wm).1,h.symm,g.symm⟩,fun ⟨ne,h,g⟩ =>
      ⟨outside_mem.mpr ⟨ne,h.ne.symm,g.ne.symm⟩,h.symm,g.symm⟩⟩
  obtain ⟨mode,zero,mono,many⟩ : ∃ mode : Fin 3,(mode.val=0 → C=∅) ∧
      (mode.val=1 → C.card=1) ∧ (mode.val=2 → 2≤C.card) := by
    by_cases z : C=∅
    · exact ⟨0,fun _ => z,by simp,by simp⟩
    have non := card_pos.mpr (nonempty_iff_ne_empty.mpr z)
    by_cases z1 : C.card=1
    · exact ⟨1,by simp,fun _ => z1,by simp⟩
    · exact ⟨2,by simp,by simp,fun _ => by omega⟩
  have scores (v : V) (vm : v∈W) : 2≤trianglesAt H v := by
    have ne := (outside_mem.mp vm).1
    have no : trianglesAt H v≠1 := fun h => ne (fi (h.trans one.symm))
    have := pos v; omega
  have low (v : V) (vm : v∈W) (sc : 3≤trianglesAt H v) (z : j v=0) : 4≤H.degree v := by
    by_cases enough : 4≤H.degree v
    · exact enough
    have minimum := rest v (outside_mem.mp vm).1
    have cap := Repair.triangles_le_choose H v
    have d : H.degree v=3 := by omega
    rw [d] at cap; change trianglesAt H v≤3 at cap
    obtain ⟨w,ew,vw⟩ := L.meets (s:=v) (mem_filter.mpr ⟨mem_univ _,d,by omega⟩) de
    have wn := (H.mem_neighborFinset ..).mpr ew
    rw [ear,mem_insert,mem_singleton] at wn
    have h := seen (v:=v) (wn.elim (fun eq => Or.inl (eq ▸ vw)) (fun eq => Or.inr (eq ▸ vw)))
    omega
  have single (h : mode.val=0) (v : V) (vm : v∈W) : j v≠2 := by
    intro eq; have c : v∈C := ceq ▸ mem_filter.mpr ⟨vm,eq⟩
    rw [zero h] at c; simp at c
  have over : (∑ v∈W,Pair.rebate mode (j v))≤Pair.penalty mode := by
    have eq : (∑ v∈W,Pair.rebate mode (j v))=C.card*Pair.penalty mode := by
      calc _ = ∑ _v∈W.filter (fun v => j v=2),Pair.penalty mode := by rw [sum_filter]; rfl
           _ = _ := by rw [ceq,sum_const,nsmul_eq_mul,Nat.cast_id]
    rw [eq]; by_cases h : mode.val=1
    · rw [mono h,one_mul]
    · simp [Pair.penalty,h]
  have counts := ThreeChoice.balance H A W
  have a2 : nbr H a Wᶜ=2 := by simp [W,outside,nbr,filter_insert,filter_singleton,ea.symm,ab,ea.ne,eb.ne,ab.ne]
  have b2 : nbr H b Wᶜ=2 := by simp [W,outside,nbr,filter_insert,filter_singleton,eb.symm,ab.symm,ea.ne,eb.ne,ab.ne]
  have ac := Repair.full_nbr H a W; have bc := Repair.full_nbr H b W
  change (∑ v∈W,j v)=∑ v∈({a,b}:Finset V),nbr H v W at counts
  rw [sum_pair ab.ne] at counts
  have inc : 12≤∑ v∈W,j v := by omega
  have upper := Pair.estimate H ws xm sx dx fi scores free mode j bill (fun v _ => jlim v) low
    (fun v vm => Pair.pair_fiber H ws aw vm) single
    (fun h => seen (touch (card_pos.mp (by rw [show (additional H e a b).card=1 from mono h]; decide))))
    (fun h => (two x).mpr (both (many h))) over inc
  exact (not_lt_of_ge (necessary_mass H ea eb ab.ne ear hi ws)) upper

/-- The catalogue inequality at diversity 31 for every connected
five-clique-free graph, at every order. -/
theorem exact_five_free (hc : H.Connected) (t : (types H).card=31) (free : H.CliqueFree 5) :
    gamma H≤bound H := by
  by_contra! fail
  let P := nonleaves H
  let J := H.induce (P:Set V)
  obtain ⟨n,_,fi,pos,g,u,x,e,_,_,dx,sx,de,se,rest,_⟩ := Frontier31.five_free_core H hc t free fail
  have jf : J.CliqueFree 5 := free.comap (Embedding.induce (P:Set V))
  have up := core_bound J n jf pos fi de se dx sx rest
  change gamma J=15 at g
  omega

/-- Every connected graph with at least 31 types and no five-clique
satisfies the catalogue inequality. -/
theorem at_least_31_five_free (hc : H.Connected) (hn : 2<Fintype.card V)
    (t : 31≤(types H).card) (free : H.CliqueFree 5) : gamma H≤bound H := by
  by_cases eq : (types H).card=31
  · exact exact_five_free H hc eq free
  · exact Diversity33.at_least_32 H hc hn (by omega)

/-- The bounded induced witness for a diversity-31 failure itself contains
a five-clique and retains the exact set of realized triangle counts. -/
theorem induced_five (hc : H.Connected) (hn : 2<Fintype.card V) (t : (types H).card=31)
    (bad : bound H<gamma H) :
    ∃ S : Finset V,2<S.card ∧ S.card≤33 ∧ (H.induce (S:Set V)).Connected ∧
      types (H.induce (S:Set V))=types H ∧ bound (H.induce (S:Set V))<gamma (H.induce (S:Set V)) ∧
      ∃ C : Finset S,(H.induce (S:Set V)).IsNClique 5 C := by
  classical
  obtain ⟨_,S,lo,hi,conn,same,fail⟩ := Diversity33.remaining H hc hn bad
  refine ⟨S,lo,hi,conn,same,fail,?_⟩
  by_contra! no
  exact (not_lt_of_ge (exact_five_free _ conn ((congrArg card same).trans t) no)) fail

end Graffiti384b.EarCredit
#print axioms Graffiti384b.EarCredit.core_bound
#print axioms Graffiti384b.EarCredit.exact_five_free
#print axioms Graffiti384b.EarCredit.at_least_31_five_free
#print axioms Graffiti384b.EarCredit.induced_five
