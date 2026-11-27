import CubicClosure33

namespace Graffiti384b.CubicShore
open Finset SimpleGraph EarAnchor EarFrame33 CliquePivot33
open private CubicShore.clique_score CubicShore.half_tight from CubicDiamondCut33
open private EarAnchor.sees_in_clique from CubicAnchor33
open private Repair.isolate Repair.triangles_le_choose Repair.nbr_mono from Repair384b
open private CliquePivot33.isolated_degree from CliquePivot33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- A second common neighbor of the ear endpoints gives a strict half-order
saving when one endpoint has triangle count two or three. -/
theorem square_below_half {e a c w : V} (de : H.degree e=2) (rare : trianglesAt H a=2 ∨ trianglesAt H a=3)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (five : ∃ C,H.IsNClique 5 C) (aw : H.Adj a w) (cw : H.Adj c w) (we : w≠e) : 2*gamma H<Fintype.card V := by
  classical
  apply Nat.lt_of_not_ge; intro half
  obtain ⟨u,du,_,uc,uw,cub,shape⟩ := forced_clique H de rare ea ec ac aw cw we pos inj half five
  obtain ⟨C,cl⟩ := five
  have cs := shape C cl
  let N := H.neighborFinset u
  have ns : N.card=3 := (card_neighborFinset_eq_degree ..).trans du
  have nc : N⊆C := cs ▸ ((subset_insert w N).trans (subset_insert ..))
  have cc : c∈C := cs ▸ mem_insert_self ..
  have wc : w∈C := cs ▸ mem_insert_of_mem (mem_insert_self ..)
  have missed (z : V) (low : H.degree z≤3) : z∉C := fun m => by have := EarAnchor.sees_in_clique H cl m; omega
  have en := missed e (by omega)
  have un := missed u (by omega)
  have an : a∉C := fun m => by have := CubicShore.clique_score H cl m; omega
  have au : a≠u := fun h => uc (h ▸ ac)
  obtain ⟨x,xn⟩ := card_pos.mp (show 0<N.card by omega)
  let K := N.erase x
  have ks : K.card=2 := by rw [show K=N.erase x from rfl,card_erase_of_mem xn,ns]
  have kn : K⊆N := erase_subset ..
  have kC := kn.trans nc
  have cN : c∉N := fun m => uc ((H.mem_neighborFinset _ _).mp m)
  have wN : w∉N := fun m => uw ((H.mem_neighborFinset _ _).mp m)
  let A := insert a (insert c K)
  let B : Finset V := {e,w,u}
  have aa : a∈A := mem_insert_self ..
  have ca : c∈A := mem_insert_of_mem (mem_insert_self ..)
  have ka : K⊆A := (subset_insert c K).trans (subset_insert ..)
  have eb : e∈B := mem_insert_self ..
  have wb : w∈B := mem_insert_of_mem (mem_insert_self ..)
  have ub : u∈B := mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))
  have dis : Disjoint A B := by
    apply disjoint_left.mpr; intro t ma mb
    rcases (show t=e ∨ t=w ∨ t=u by simpa only [B,mem_insert,mem_singleton] using mb) with h|h|h <;> subst t
    · rcases (show e=a ∨ e=c ∨ e∈K by simpa only [A,mem_insert] using ma) with h|h|m
      · exact ea.ne h
      · exact ec.ne h
      · exact en (kC m)
    · rcases (show w=a ∨ w=c ∨ w∈K by simpa only [A,mem_insert] using ma) with h|h|m
      · exact aw.ne.symm h
      · exact cw.ne.symm h
      · exact wN (kn m)
    · rcases (show u=a ∨ u=c ∨ u∈K by simpa only [A,mem_insert] using ma) with h|h|m
      · exact au h.symm
      · exact un (h ▸ cc)
      · exact un (kC m)
  have ewu : w≠u := fun h => un (h ▸ wc)
  have ew := we.symm
  have ksupport (t : V) (allK : ∀ i∈K,H.Adj t i) : 2≤nbr H t A := by
    have f : K.filter (H.Adj t)=K := filter_true_of_mem allK
    have lo : 2≤nbr H t K := by simp [nbr,f,ks]
    exact lo.trans (Repair.nbr_mono H t ka)
  have frame : Frame H A B := by
    refine ⟨dis,?_,?_⟩
    · intro t m
      rcases (show t=a ∨ t=c ∨ t∈K by simpa only [A,mem_insert] using m) with rfl|rfl|tk
      · exact PinnedColor34.two H ew ea.symm aw eb wb
      · exact PinnedColor34.two H ew ec.symm cw eb wb
      · have tw : H.Adj t w := cl.1 (kC tk) wc (fun eq => wN (eq ▸ kn tk))
        exact PinnedColor34.two H ewu tw ((H.mem_neighborFinset _ _).mp (kn tk)).symm wb ub
    · intro t m
      rcases (show t=e ∨ t=w ∨ t=u by simpa only [B,mem_insert,mem_singleton] using m) with h|h|h <;> subst t
      · exact PinnedColor34.two H ac.ne ea ec aa ca
      · exact PinnedColor34.two H ac.ne aw.symm cw.symm aa ca
      · exact ksupport u (fun i m => (H.mem_neighborFinset _ _).mp (kn m))
  have xa : x∉A := by
    intro m
    rcases (show x=a ∨ x=c ∨ x∈K by simpa only [A,mem_insert] using m) with h|h|k
    · exact an (h ▸ nc xn)
    · exact cN (h ▸ xn)
    · exact not_mem_erase x N k
  have xb : x∉B := by
    intro m
    rcases (show x=e ∨ x=w ∨ x=u by simpa only [B,mem_insert,mem_singleton] using m) with h|h|h
    · exact en (h ▸ nc xn)
    · exact wN (h ▸ xn)
    · exact un (h ▸ nc xn)
  have xw := cl.1 (nc xn) wc (fun h => wN (h ▸ xn))
  obtain ⟨t,tx,tout,bout,lo,_,_⟩ := EarOnClique33.mixed_blocker H (CubicShore.half_tight H half) frame xa xb
    (ksupport x (fun i im => cl.1 (nc xn) (kC im) (mem_erase.mp im).1.symm))
    (PinnedColor34.two H ewu xw ((H.mem_neighborFinset _ _).mp xn).symm wb ub)
  have te : t≠e := fun h => bout (h ▸ eb)
  have ta : t≠a := fun h => tout (h ▸ aa)
  have tu : t≠u := fun h => bout (h ▸ ub)
  have scoreE : trianglesAt H e=1 := by
    have cap := Repair.triangles_le_choose H e
    rw [de,Nat.choose_self] at cap
    have := pos e; omega
  have t4 : 4≤H.degree t := by
    apply Nat.le_of_not_gt; intro low
    have d : H.degree t=0 ∨ H.degree t=1 ∨ H.degree t=2 ∨ H.degree t=3 := by omega
    rcases d with h|h|h|h
    all_goals first | exact (cub t h).elim ta tu | skip
    all_goals
      have cap := Repair.triangles_le_choose H t
      rw [h] at cap
      have po := pos t
      apply te; apply inj; rw [scoreE]
      norm_num [Nat.choose] at cap; omega
  rw [CliquePivot33.isolated_degree H tx] at lo
  by_cases adj : H.Adj t x
  · rw [card_erase_of_mem ((H.mem_neighborFinset _ _).mpr adj),card_neighborFinset_eq_degree] at lo
    omega
  · rw [erase_eq_of_not_mem (fun m => adj ((H.mem_neighborFinset _ _).mp m)),card_neighborFinset_eq_degree] at lo
    omega

/-- A cubic ear endpoint automatically has triangle count two and a second
common neighbor, so no half-order positive core contains such an endpoint. -/
theorem below_half {e a c : V} (de : H.degree e=2) (da : H.degree a=3)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (five : ∃ C,H.IsNClique 5 C) : 2*gamma H<Fintype.card V := by
  obtain ⟨w,wm,_,cw,_,na,_,two⟩ := diamond H de da ea ec ac pos inj
  have aw := (H.mem_neighborFinset _ _).mp (show w∈H.neighborFinset a from
    na ▸ mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _)))
  exact square_below_half H de (Or.inl two) ea ec ac pos inj five aw cw (outside_mem.mp wm).1

/-- In a positive extremal core both endpoints of the unique ear have
degree at least four, irrespective of the attachment point of the leaf. -/
theorem endpoints {e a c : V} (de : H.degree e=2) (ea : H.Adj e a) (ec : H.Adj e c)
    (ac : H.Adj a c) (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (half : Fintype.card V≤2*gamma H) (five : ∃ C,H.IsNClique 5 C) :
    4≤H.degree a ∧ 4≤H.degree c := by
  have one : trianglesAt H e=1 := by
    have cap := Repair.triangles_le_choose H e
    rw [de,Nat.choose_self] at cap; have := pos e; omega
  have atLeast {t : V} (et : H.Adj e t) (three : H.degree t≠3) : 4≤H.degree t := by
    apply Nat.le_of_not_gt; intro sm
    have range : H.degree t=0 ∨ H.degree t=1 ∨ H.degree t=2 := by omega
    have cap := Repair.triangles_le_choose H t
    have cap1 : (H.degree t).choose 2≤1 := by rcases range with h|h|h <;> rw [h] <;> decide
    have := pos t
    exact et.ne (inj (one.trans (show trianglesAt H t=1 by omega).symm))
  exact ⟨atLeast ea (fun d => (not_lt_of_ge half) (below_half H de d ea ec ac pos inj five)),
    atLeast ec (fun d => (not_lt_of_ge half) (below_half H de d ec ea ac.symm pos inj five))⟩

/-- In the remaining half-order case both endpoints have triangle count at
least four as soon as their common neighborhood extends beyond the ear. -/
theorem square_scores {e a c w : V} (de : H.degree e=2)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (half : Fintype.card V≤2*gamma H) (five : ∃ C,H.IsNClique 5 C)
    (aw : H.Adj a w) (cw : H.Adj c w) (we : w≠e) :
    4≤trianglesAt H a ∧ 4≤trianglesAt H c := by
  have one : trianglesAt H e=1 := by
    have cap := Repair.triangles_le_choose H e; rw [de,Nat.choose_self] at cap
    have := pos e; omega
  have lo (t : V) (ne : e≠t) : 2≤trianglesAt H t := by
    have := pos t
    have diff : trianglesAt H t≠1 := fun h => ne (inj (one.trans h.symm))
    omega
  have na := fun (h : trianglesAt H a=2 ∨ trianglesAt H a=3) =>
    (not_lt_of_ge half) (square_below_half H de h ea ec ac pos inj five aw cw we)
  have nc := fun (h : trianglesAt H c=2 ∨ trianglesAt H c=3) =>
    (not_lt_of_ge half) (square_below_half H de h ec ea ac.symm pos inj five cw aw we)
  have := lo a ea.ne
  have := lo c ec.ne
  constructor
  · apply Nat.le_of_not_gt; intro sm; exact na (by omega)
  · apply Nat.le_of_not_gt; intro sm; exact nc (by omega)

/-- A positive 32-vertex core of this shape already has a 15-vertex
solution; including the deleted vertex settles every attachment at order 33. -/
theorem full_bound (n : Fintype.card V=33) (t : (types H).card=33) (z : V) :
    let P := ({z} : Finset V)ᶜ
    let G := H.induce (P : Set V)
    ∀ e a c : P,G.degree e=2 → G.Adj e a → G.Adj e c → G.Adj a c →
    (G.degree a=3 ∨ ((trianglesAt G a=2 ∨ trianglesAt G a=3) ∧ ∃ w,w≠e ∧ G.Adj a w ∧ G.Adj c w)) →
    (∀ v,0<trianglesAt G v) → Function.Injective (trianglesAt G) →
    (∃ C,G.IsNClique 5 C) → gamma G≤15 ∧ gamma H≤bound H := by
  let P := ({z} : Finset V)ᶜ
  let G := H.induce (P : Set V)
  change ∀ e a c : P,_
  intro e a c de ea ec ac shape pos inj five
  have order : Fintype.card P=32 := by rw [Fintype.card_coe]; simp [P,card_compl,n]
  have save : 2*gamma G<Fintype.card P := by
    rcases shape with da|⟨rare,w,we,aw,cw⟩
    · exact below_half G de da ea ec ac pos inj five
    · exact square_below_half G de rare ea ec ac pos inj five aw cw we
  change 2*gamma G<Fintype.card P at save
  have small : gamma G≤15 := by omega
  refine ⟨small,?_⟩
  obtain ⟨X,cov,size⟩ := (gamma_induced_iff H (W:=P)).mp small
  have dom : TwoDominates H (insert z X) := by
    intro y out
    have yz : y≠z := fun eq => out (eq ▸ mem_insert_self ..)
    exact (cov.2 y (by simp [P,yz]) (fun m => out (mem_insert_of_mem m))).trans
      (Repair.nbr_mono H y (subset_insert ..))
  have up : gamma H≤(insert z X).card := Nat.sInf_le ⟨_,dom,rfl⟩
  have bound : bound H=16 := by unfold Graffiti384b.bound; rw [n,t]
  have := card_insert_le z X
  omega

end Graffiti384b.CubicShore
#print axioms Graffiti384b.CubicShore.square_below_half
#print axioms Graffiti384b.CubicShore.square_scores
#print axioms Graffiti384b.CubicShore.below_half
#print axioms Graffiti384b.CubicShore.endpoints
#print axioms Graffiti384b.CubicShore.full_bound
