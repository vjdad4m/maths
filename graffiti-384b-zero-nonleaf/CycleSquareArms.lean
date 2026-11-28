import ShortestArms
import CoupledSquares

namespace Graffiti384b.OddStars.HallArms
open Finset SimpleGraph OneEar PositivePalette
open private OddStars.merge_frames from CoupledSquares
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in
/-- Alternating colors split the cycle into two self-supporting sets. -/
private theorem cycle_frame {e : V}
    {n : ℕ} (big : 2 ≤ n) (even : n % 2 = 0) (f : ℕ → V)
    (step : ∀ i < n, G.Adj (f i) (f (i+1)))
    (inj : ∀ i ≤ n, ∀ j ≤ n, f i = f j → i=j)
    (avoid : ∀ i ≤ n, f i ≠ e) (first : G.Adj e (f 0)) (last : G.Adj e (f n)) :
    ∃P Q : Finset V,Disjoint P Q ∧ P∪Q=insert e ((range (n+1)).image f) ∧
       (∀v∈P,2≤nbr G v Q) ∧ (∀v∈Q,2≤nbr G v P) := by
  classical
  let side (k : ℕ) := (((range (n+1)).filter (fun i => i%2=k)).image f)
  let P := side 0
  let Q := insert e (side 1)
  have mem (k i : ℕ) (hi : i≤n) (par : i%2=k) : f i∈side k :=
    mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_range.mpr (by omega),par⟩,rfl⟩
  have index {k : ℕ} {v : V} (m : v∈side k) : ∃ i≤n, i%2=k ∧ f i=v := by
    obtain ⟨i,im,fi⟩ := mem_image.mp m
    exact ⟨i,Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp im).1),(mem_filter.mp im).2,fi⟩
  have dis : Disjoint P Q := by
    apply disjoint_left.mpr
    intro v vp vq
    obtain ⟨i,hi,ei,rfl⟩ := index vp
    rcases mem_insert.mp vq with eq | vq
    · exact avoid i hi eq
    · obtain ⟨j,hj,oj,eq⟩ := index vq
      have := inj j hj i hi eq
      omega
  have middle (i : ℕ) (lo : 0 < i) (up : i < n) :
      2 ≤ nbr G (f i) (side (1-i%2)) := by
    have prev := step (i-1) (by omega)
    rw [show i-1+1=i by omega] at prev
    exact PinnedColor34.two G (fun eq => by have := inj (i-1) (by omega) (i+1) (by omega) eq; omega)
      prev.symm (step i up) (mem _ _ (by omega) (by omega)) (mem _ _ (by omega) (by omega))
  have eqm : e∈Q := mem_insert_self ..
  have allPins : P∪Q=insert e ((range (n+1)).image f) := by
    ext v
    constructor
    · intro m
      have onSide {k : ℕ} (h : v∈side k) : v∈insert e ((range (n+1)).image f) := by
        obtain ⟨i,hi,_,rfl⟩ := index h
        exact mem_insert_of_mem (mem_image_of_mem f (mem_range.mpr (by omega)))
      rcases mem_union.mp m with h|h
      · exact onSide h
      · exact (mem_insert.mp h).elim (fun eq => mem_insert.mpr (Or.inl eq)) onSide
    · intro h
      rcases mem_insert.mp h with rfl|h
      · exact mem_union_right _ eqm
      obtain ⟨i,im,rfl⟩ := mem_image.mp h
      have hi := mem_range.mp im
      by_cases bit : i%2=0
      · exact mem_union_left _ (mem _ _ (by omega) bit)
      · exact mem_union_right _ (mem_insert_of_mem (mem _ _ (by omega) (by omega)))
  refine ⟨P,Q,dis,allPins,?_,?_⟩
  · intro v vp
    obtain ⟨i,hi,par,rfl⟩ := index vp
    by_cases iz : i=0
    · subst i
      exact PinnedColor34.two G (Ne.symm (avoid 1 (by omega))) first.symm (step 0 (by omega))
        eqm (mem_insert_of_mem (mem 1 1 (by omega) rfl))
    by_cases en : i=n
    · subst i
      have prev := step (n-1) (by omega)
      rw [show n-1+1=n by omega] at prev
      exact PinnedColor34.two G (Ne.symm (avoid (n-1) (by omega))) last.symm prev.symm eqm
        (mem_insert_of_mem (mem 1 _ (by omega) (by omega)))
    have h := middle i (by omega) (by omega)
    rw [par] at h
    exact h.trans (card_le_card (filter_subset_filter _ (subset_insert ..)))
  · intro v vq
    rcases mem_insert.mp vq with rfl | vm
    · exact PinnedColor34.two G (fun eq => by have := inj 0 (by omega) n le_rfl eq; omega)
        first last (mem 0 0 (by omega) rfl) (mem 0 n le_rfl even)
    · obtain ⟨i,hi,par,rfl⟩ := index vm
      have h := middle i (by omega) (by omega)
      simpa only [par,Nat.sub_self] using h


/-- Attach a square to a protected cycle at at most one square vertex.
The square may be reversed relative to the prescribed cycle cut. -/
private theorem attach_square {P Q : Finset V} {e z u c d : V} (dis : Disjoint P Q)
    (lp : ∀v∈P,2≤nbr G v Q) (rq : ∀v∈Q,2≤nbr G v P) (em : e∈P∪Q)
    (off : ∀v∈P∪Q,v≠z ∧ v≠c ∧ v≠d) (zu : z≠u) (cd : c≠d)
    (zc : G.Adj z c) (zd : G.Adj z d) (uc : G.Adj u c) (ud : G.Adj u d) :
    Covered G (insert e (insert z (high G))) := by
  let A : Finset V := {z,u}
  let B : Finset V := {c,d}
  have cross : ∀x∈A,∀y∈B,G.Adj x y := by
    intro x xm y ym
    rcases mem_insert.mp xm with rfl|xm
    · exact (mem_insert.mp ym).elim (fun h => h ▸ zc) (fun h => mem_singleton.mp h ▸ zd)
    · obtain rfl := mem_singleton.mp xm
      exact (mem_insert.mp ym).elim (fun h => h ▸ uc) (fun h => mem_singleton.mp h ▸ ud)
  have ab : ∀v∈A,2≤nbr G v B := fun v vm => PinnedColor34.two G cd
    (cross _ vm _ (mem_insert_self ..)) (cross _ vm _ (mem_insert_of_mem (mem_singleton_self _)))
    (mem_insert_self ..) (mem_insert_of_mem (mem_singleton_self _))
  have ba : ∀v∈B,2≤nbr G v A := fun v vm => PinnedColor34.two G zu
    (cross _ (mem_insert_self ..) _ vm).symm (cross _ (mem_insert_of_mem (mem_singleton_self _)) _ vm).symm
    (mem_insert_self ..) (mem_insert_of_mem (mem_singleton_self _))
  have dab : Disjoint A B := disjoint_left.mpr (fun x ax bx => (cross x ax x bx).ne rfl)
  have away {X : Finset V} (sub : X⊆P∪Q) : Disjoint X B := disjoint_left.mpr (fun v vm bm =>
    (mem_insert.mp bm).elim (off v (sub vm)).2.1 (fun h => (off v (sub vm)).2.2 (mem_singleton.mp h)))
  have awayA {X : Finset V} (sub : X⊆P∪Q) (nu : u∉X) : Disjoint X A := disjoint_left.mpr
    (fun v vm am => (mem_insert.mp am).elim (off v (sub vm)).1 (fun vv => nu (mem_singleton.mp vv ▸ vm)))
  by_cases up : u∈P
  · have sep : Disjoint (P∪A) (Q∪B) := disjoint_union_left.mpr
      ⟨disjoint_union_right.mpr ⟨dis,away subset_union_left⟩,
       disjoint_union_right.mpr ⟨(awayA subset_union_right (disjoint_left.mp dis up)).symm,dab⟩⟩
    exact OddStars.merge_frames G sep lp rq ab ba ((mem_union.mp em).elim
      (fun h => Or.inl (mem_union_left _ h)) (fun h => Or.inr (mem_union_left _ h)))
      (Or.inl (mem_union_right _ (mem_insert_self ..)))
  · have sep : Disjoint (P∪B) (Q∪A) := disjoint_union_left.mpr
      ⟨disjoint_union_right.mpr ⟨dis,awayA subset_union_left up⟩,
       disjoint_union_right.mpr ⟨(away subset_union_right).symm,dab.symm⟩⟩
    exact OddStars.merge_frames G sep lp rq ba ab ((mem_union.mp em).elim
      (fun h => Or.inl (mem_union_left _ h)) (fun h => Or.inr (mem_union_left _ h)))
      (Or.inr (mem_union_right _ (mem_insert_self ..)))

/-- The two arm prefixes close an even cycle using their penultimate
cross-edge. It meets the square through z only at the first penultimate vertex. -/
theorem diamond_cut {e z a b : V} (L : Link G e z a b) (ez : e≠z) (noez : ¬G.Adj e z)
    (ea : G.Adj e a) (eb : G.Adj e b) (np : 0<L.n) (mp : 0<L.m)
    (odd : (L.n+L.m)%2=1)
    (uv : (inside G ({e,z}ᶜ)).Adj (L.p.atIdx (L.n-1)) (L.q.atIdx (L.m-1)))
    (du : (inside G ({e,z}ᶜ)).Adj L.d (L.p.atIdx (L.n-1))) :
    Covered G (insert e (insert z (high G))) := by
  classical
  let N := L.n+L.m-1
  let f (i : ℕ) := if i<L.n then L.p.atIdx i else L.q.atIdx (N-i)
  have left {i : ℕ} (h : i<L.n) : f i=L.p.atIdx i := if_pos h
  have right {i : ℕ} (h : L.n≤i) : f i=L.q.atIdx (N-i) := if_neg (by omega)
  have step (i : ℕ) (hi : i<N) : G.Adj (f i) (f (i+1)) := by
    by_cases less : i+1<L.n
    · rw [left (by omega),left less]; exact (L.p.step i (by omega)).1
    by_cases join : i+1=L.n
    · rw [left (by omega),right (by omega),show i=L.n-1 by omega,
        show N-(L.n-1+1)=L.m-1 by dsimp [N]; omega]
      exact uv.1
    rw [right (by omega),right (by omega)]
    have move := (L.q.step (N-(i+1)) (by dsimp [N]; omega)).1.symm
    rwa [show N-(i+1)+1=N-i by omega] at move
  have unique (i : ℕ) (hi : i≤N) (j : ℕ) (hj : j≤N) (eq : f i=f j) : i=j := by
    by_cases il : i<L.n <;> by_cases jl : j<L.n
    · exact L.p.unique i il.le j jl.le ((left il).symm.trans (eq.trans (left jl)))
    · rw [left il,right (by omega)] at eq
      exact (L.sep i il.le (N-j) (by dsimp [N]; omega) eq).elim
    · rw [right (by omega),left jl] at eq
      exact (L.sep j jl.le (N-i) (by dsimp [N]; omega) eq.symm).elim
    · rw [right (by omega),right (by omega)] at eq
      have same := L.q.unique (N-i) (by dsimp [N]; omega) (N-j) (by dsimp [N]; omega) eq
      omega
  have avoid (i : ℕ) (_ : i≤N) : f i≠e := by
    by_cases il : i<L.n
    · rw [left il]; exact L.p.avoid i il.le
    · rw [right (by omega)]; exact L.q.avoid _ (by dsimp [N]; omega)
  have first : G.Adj e (f 0) := by rwa [left np,L.p.start]
  have last : G.Adj e (f N) := by rwa [right (by dsimp [N]; omega),Nat.sub_self,L.q.start]
  obtain ⟨P,Q,dis,shape,lp,rq⟩ := cycle_frame G (e:=e) (n:=N) (by dsimp [N]; omega)
    (by dsimp [N]; omega) f step unique avoid first last
  have outside (i : ℕ) : f i≠z ∧ f i≠L.c ∧ f i≠L.d := by
    by_cases il : i<L.n
    · rw [left il]
      refine ⟨fun eq => mem_compl.mp (L.p.step i il).2.1 (mem_insert_of_mem (mem_singleton.mpr eq)),?_,?_⟩
      · intro eq; have := L.p.unique i il.le L.n le_rfl (eq.trans L.p.finish.symm); omega
      · exact fun eq => L.sep i il.le _ le_rfl (eq.trans L.q.finish.symm)
    · rw [right (by omega)]
      have small : N-i<L.m := by dsimp [N]; omega
      refine ⟨fun eq => mem_compl.mp (L.q.step _ small).2.1 (mem_insert_of_mem (mem_singleton.mpr eq)),?_,?_⟩
      · exact fun eq => L.sep _ le_rfl _ small.le (L.p.finish.trans eq.symm)
      · intro eq; have := L.q.unique _ small.le L.m le_rfl (eq.trans L.q.finish.symm); omega
  have ex : e≠L.c ∧ e≠L.d := ⟨fun h => noez (h.symm ▸ L.zc.symm),fun h => noez (h.symm ▸ L.zd.symm)⟩
  have off (v : V) (m : v∈P∪Q) : v≠z ∧ v≠L.c ∧ v≠L.d := by
    rw [shape] at m
    rcases mem_insert.mp m with rfl|m
    · exact ⟨ez,ex⟩
    obtain ⟨i,_,rfl⟩ := mem_image.mp m; exact outside i
  have uc := (L.p.step (L.n-1) (by omega)).1
  rw [show L.n-1+1=L.n by omega,L.p.finish] at uc
  have ou := outside (L.n-1)
  rw [left (by omega)] at ou
  exact attach_square G dis lp rq (by rw [shape]; exact mem_insert_self ..) off ou.1.symm
    (by simpa only [L.p.finish,L.q.finish] using L.sep L.n le_rfl L.m le_rfl) L.zc L.zd uc du.1.symm

end Graffiti384b.OddStars.HallArms
#print axioms Graffiti384b.OddStars.HallArms.diamond_cut