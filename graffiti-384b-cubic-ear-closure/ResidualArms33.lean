import AnchorEdge33

namespace Graffiti384b.ResidualShore
open Finset SimpleGraph OneEar
open private EarExchange33.count_insert from Exchange33
open private Repair.nbr_mono Repair.full_nbr from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Oriented pins with one missing opposite neighbor allowed at the root. -/
def Arm (r : V) (S P Q : Finset V) : Prop :=
  P∪Q⊆S ∧ Disjoint P Q ∧ r∈P ∧
  (∀ x∈P,(if x=r then 1 else 2)≤nbr G x Q) ∧ (∀ x∈Q,2≤nbr G x P)

theorem combine {v p q : V} (vp : G.Adj v p) (vq : G.Adj v q) (pq : p≠q)
    {S T P Q L R : Finset V} (apart : Disjoint S T) (vs : v∉S) (vt : v∉T)
    (one : Arm G p S P Q) (two : Arm G q T L R) (minimum : ∀ x,x≠v → 3≤G.degree x) :
    ∃ D,TwoDominates G D ∧ 2*D.card≤Fintype.card V := by
  classical
  obtain ⟨su,dis,pp,l1,r1⟩ := one
  obtain ⟨tu,d2,ql,l2,r2⟩ := two
  let A := P∪L
  let B := insert v (Q∪R)
  have ps : P⊆S := subset_union_left.trans su
  have qs : Q⊆S := subset_union_right.trans su
  have lt : L⊆T := subset_union_left.trans tu
  have rt : R⊆T := subset_union_right.trans tu
  have dp : Disjoint A B := by
    apply disjoint_left.mpr; intro x xm ym
    rcases mem_union.mp xm with xp|xl <;> rcases mem_insert.mp ym with rfl|mem
    · exact vs (ps xp)
    · rcases mem_union.mp mem with xq|xr
      · exact disjoint_left.mp dis xp xq
      · exact disjoint_left.mp apart (ps xp) (rt xr)
    · exact vt (lt xl)
    · rcases mem_union.mp mem with xq|xr
      · exact disjoint_left.mp apart (qs xq) (lt xl)
      · exact disjoint_left.mp d2 xl xr
  have von : v∉Q∪R := fun m => (mem_union.mp m).elim (fun h => vs (qs h)) (fun h => vt (rt h))
  have support (x : V) (xm : x∈A) : 2≤nbr G x B := by
    rw [show B=insert v (Q∪R) from rfl,EarExchange33.count_insert G v x von]
    rcases mem_union.mp xm with h|h
    · have b := l1 x h
      have t := Repair.nbr_mono G x (show Q⊆Q∪R from subset_union_left)
      by_cases eq : x=p
      · rw [if_pos eq] at b; rw [if_pos (show G.Adj x v by simpa only [eq] using vp.symm)]; omega
      · simp [eq] at b; omega
    · have b := l2 x h
      have t := Repair.nbr_mono G x (show R⊆Q∪R from subset_union_right)
      by_cases eq : x=q
      · rw [if_pos eq] at b; rw [if_pos (show G.Adj x v by simpa only [eq] using vq.symm)]; omega
      · simp [eq] at b; omega
  obtain ⟨D,ad,bd,left,right⟩ := PinnedColor34.cut G A B dp
  have vb : v∈B := mem_insert_self ..
  have suppB (x : V) (xm : x∈B) : 2≤nbr G x A := by
    rcases mem_insert.mp xm with rfl|m
    · exact PinnedColor34.two G pq vp vq (mem_union_left _ pp) (mem_union_right _ ql)
    rcases mem_union.mp m with xq|xr
    · exact (r1 x xq).trans (Repair.nbr_mono G x subset_union_left)
    · exact (r2 x xr).trans (Repair.nbr_mono G x subset_union_right)
  have domD : TwoDominates G D := by
    intro x no
    by_cases pins : x∈B
    · exact (suppB x pins).trans (Repair.nbr_mono G x ad)
    have lo := minimum x (fun eq => pins (eq ▸ vb))
    have h := right x (mem_compl.mpr no) pins
    have t := Repair.full_nbr G x D
    omega
  have domC : TwoDominates G Dᶜ := by
    intro x no
    have xd : x∈D := by simpa using no
    by_cases pins : x∈A
    · exact (support x pins).trans (Repair.nbr_mono G x bd)
    have lo := minimum x (fun eq => (mem_compl.mp (bd vb)) (eq ▸ xd))
    have h := left x xd pins
    have t := Repair.full_nbr G x D
    omega
  by_cases small : 2*D.card≤Fintype.card V
  · exact ⟨D,domD,small⟩
  · refine ⟨Dᶜ,domC,?_⟩
    have := card_le_univ D
    rw [card_compl]; omega

omit [Fintype V] in
/-- A path from the root can end with a cycle through two equally colored
earlier neighbors of its endpoint. Alternating pins support the whole arm. -/
theorem fork_arm {v r t : V} {n i j : ℕ} (s : Route G v r t n)
    (ij : i<j) (jn : j<n) (same : i%2=j%2)
    (ti : G.Adj t (s.atIdx i)) (tj : G.Adj t (s.atIdx j))
    {S : Finset V} (inside : ∀ k≤n,s.atIdx k∈S) : ∃ P Q,Arm G r S P Q := by
  classical
  let side (b : ℕ) := (((range (j+1)).filter (fun k => k%2=b)).image s.atIdx) ∪
    (if b=j%2 then ∅ else {t})
  have put (k : ℕ) (hk : k≤j) : s.atIdx k∈side (k%2) :=
    mem_union_left _ (mem_image.mpr ⟨k,mem_filter.mpr ⟨mem_range.mpr (by omega),rfl⟩,rfl⟩)
  have tail (b : ℕ) (hb : b≠j%2) : t∈side b := mem_union_right _ (by simp [hb])
  have parse {b : ℕ} {x : V} (h : x∈side b) :
      (∃ k≤j,k%2=b ∧ s.atIdx k=x) ∨ (b≠j%2 ∧ x=t) := by
    rcases mem_union.mp h with m|m
    · obtain ⟨k,km,eq⟩ := mem_image.mp m
      obtain ⟨kk,par⟩ := mem_filter.mp km
      exact Or.inl ⟨k,by have := mem_range.mp kk; omega,par,eq⟩
    · split at m
      · simp at m
      · exact Or.inr ⟨by assumption,mem_singleton.mp m⟩
  have fresh (k : ℕ) (hk : k≤j) : s.atIdx k≠t := fun h => by
    have := s.unique k (by omega) n le_rfl (h.trans s.finish.symm); omega
  have dis : Disjoint (side 0) (side 1) := by
    apply disjoint_left.mpr; intro x x0 x1
    rcases parse x0 with ⟨k,hk,pk,rfl⟩|⟨p0,rfl⟩ <;> rcases parse x1 with ⟨m,hm,pm,eq⟩|⟨p1,eq⟩
    · have := s.unique m (by omega) k (by omega) eq; omega
    · exact fresh k hk eq
    · exact fresh m hm eq
    · omega
  have near (b : ℕ) (hb : b≤1) (x : V) (h : x∈side b) :
      (if x=r then 1 else 2)≤nbr G x (side (1-b)) := by
    rcases parse h with ⟨k,hk,pk,rfl⟩|⟨bt,rfl⟩
    · by_cases zero : k=0
      · subst k; rw [s.start,if_pos rfl]
        have first := s.step 0 (by omega)
        rw [s.start] at first
        have m : s.atIdx 1∈side (1-b) := by simpa [show b=0 by omega] using put 1 (by omega)
        exact card_pos.mpr ⟨_,mem_filter.mpr ⟨m,first⟩⟩
      have prev := (s.step (k-1) (by omega)).symm
      rw [show k-1+1=k by omega] at prev
      have prevm : s.atIdx (k-1)∈side (1-b) := by rw [← show (k-1)%2=1-b by omega]; exact put _ (by omega)
      have up : 2≤nbr G (s.atIdx k) (side (1-b)) := by
        by_cases endk : k=j
        · subst k; exact PinnedColor34.two G (fresh _ (by omega)) prev tj.symm prevm (tail _ (by omega))
        · have nextm : s.atIdx (k+1)∈side (1-b) := by rw [← show (k+1)%2=1-b by omega]; exact put _ (by omega)
          exact PinnedColor34.two G (fun eq => by have := s.unique (k-1) (by omega) (k+1) (by omega) eq; omega)
            prev (s.step k (by omega)) prevm nextm
      split <;> omega
    · have pair := PinnedColor34.two G (fun eq => by have := s.unique i (by omega) j (by omega) eq; omega) ti tj
        (show s.atIdx i∈side (1-b) by rw [← show i%2=1-b by omega]; exact put i (by omega))
        (show s.atIdx j∈side (1-b) by rw [← show j%2=1-b by omega]; exact put j (by omega))
      split <;> omega
  have root : r∈side 0 := by simpa only [Nat.zero_mod,s.start] using put 0 (by omega)
  refine ⟨side 0,side 1,?_,dis,root,fun x h => near 0 (by decide) x h,?_⟩
  · intro x xm
    have within {b : ℕ} (h : x∈side b) : x∈S := by
      rcases parse h with ⟨k,hk,_,rfl⟩|⟨_,rfl⟩
      · exact inside k (by omega)
      · simpa only [s.finish] using inside n le_rfl
    exact (mem_union.mp xm).elim within within
  · intro x h
    have ne : x≠r := fun eq => disjoint_left.mp dis root (eq ▸ h)
    simpa [ne] using near 1 (by decide) x h

end Graffiti384b.ResidualShore
#print axioms Graffiti384b.ResidualShore.combine
#print axioms Graffiti384b.ResidualShore.fork_arm
