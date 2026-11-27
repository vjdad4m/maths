import OneEarFinish384b

/-! This module retains the actual two-coloring constructed by the one-ear
proof. The indexed route operations and reachability lemma are imported. The
cycle pins, separated-component cut and parity case split are adapted from the
four one-ear sources; the old public conclusions only give a cardinal bound. -/
namespace Graffiti384b.CoreColor33
open Finset SimpleGraph LowSample OneEar
open private Repair.nbr_mono Repair.full_nbr from Repair384b
open private OneEar.route_of_reach OneEar.deg2 from OneEarFinish384b
open private TrianglePrune.triangle_iff from TrianglePrune384b
open private LowSample.two_degree from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def GoodCut : Prop := ∃ A : Finset V,
  (∀ v∈nonleaves G,v∈A → 2≤nbr G v Aᶜ) ∧
  (∀ v∈nonleaves G,v∈Aᶜ → 2≤nbr G v A)

theorem pinned {P Q : Finset V} (dis : Disjoint P Q)
    (degrees : ∀ v∈nonleaves G,v∉P → v∉Q → 3≤G.degree v)
    (lp : ∀ v∈P,2≤nbr G v Q) (rq : ∀ v∈Q,2≤nbr G v P) : GoodCut G := by
  obtain ⟨A,pa,qb,la,rb⟩ := PinnedColor34.cut G P Q dis
  refine ⟨A,?_,?_⟩
  · intro v vn va
    by_cases vp : v∈P
    · exact (lp v vp).trans (Repair.nbr_mono G v qb)
    · have dg := degrees v vn vp (fun h => mem_compl.mp (qb h) va)
      have ae := la v va vp
      have su := Repair.full_nbr G v A
      omega
  · intro v vn vb
    by_cases vq : v∈Q
    · exact (rq v vq).trans (Repair.nbr_mono G v pa)
    · have dg := degrees v vn (fun h => mem_compl.mp vb (pa h)) vq
      have ae := rb v vb vq
      have su := Repair.full_nbr G v A
      omega

private theorem cycle {e : V} (only : twos G = {e})
    {n : ℕ} (big : 2 ≤ n) (even : n % 2 = 0) (f : ℕ → V)
    (step : ∀ i < n, G.Adj (f i) (f (i+1)))
    (inj : ∀ i ≤ n, ∀ j ≤ n, f i = f j → i=j)
    (avoid : ∀ i ≤ n, f i ≠ e) (first : G.Adj e (f 0)) (last : G.Adj e (f n)) :
    GoodCut G := by
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
  apply pinned G dis
  · intro v vn _ out
    by_contra! small
    have vm : v∈twos G := mem_sdiff.mpr ⟨vn,fun vh => by have := (mem_filter.mp vh).2; omega⟩
    rw [only,mem_singleton] at vm
    exact out (vm ▸ eqm)
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

private theorem split {e a b : V} (only : twos G={e})
    (ear : G.neighborFinset e={a,b}) (ab : G.Adj a b)
    (apart : ¬(opened G {e,a,b}).Reachable a b) : GoodCut G := by
  classical
  let K : Finset V := {e,a,b}
  let H := opened G K
  have ea : G.Adj e a := (G.mem_neighborFinset _ _).mp (ear ▸ mem_insert_self ..)
  have eb : G.Adj e b := (G.mem_neighborFinset _ _).mp (ear ▸ mem_insert_of_mem (mem_singleton_self _))
  have ek : e∈K := mem_insert_self ..
  have ak : a∈K := mem_insert_of_mem (mem_insert_self ..)
  have bk : b∈K := mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))
  have iso {v : V} (edge : H.Adj e v) : False := by
    have vm := (G.mem_neighborFinset _ _).mpr edge.1
    rw [ear] at vm
    exact edge.2 ⟨ek,mem_insert_of_mem vm⟩
  obtain ⟨A,_,_,left,right⟩ := PinnedColor34.cut H ∅ ∅ (by simp)
  let opp (v : V) := if v∈A then Aᶜ else A
  have balance (v : V) : H.degree v ≤ 2*nbr H v (opp v) := by
    have total := Repair.full_nbr H v A
    by_cases va : v∈A
    · have h := left v va (by simp)
      simp only [opp,if_pos va]; omega
    · have h := right v (mem_compl.mpr va) (by simp)
      simp only [opp,if_neg va]; omega
  let ref (v : V) := if H.Reachable a v then a else b
  let S := univ.filter (fun v => v≠e ∧ (v∈A ↔ ref v∈A))
  have sm {v : V} : v∈S ↔ v≠e ∧ (v∈A ↔ ref v∈A) := by simp [S]
  have as' : a∈S := sm.mpr ⟨ea.ne.symm,by simp [ref,Reachable.refl]⟩
  have bs' : b∈S := sm.mpr ⟨eb.ne.symm,by simp [ref,apart,H,K]⟩
  have es : e∉S := fun m => (sm.mp m).1 rfl
  have across {u v : V} (adj : H.Adj u v) (ov : v∈opp u) : (v∈S ↔ u∉S) := by
    have ue : u≠e := fun eq => iso (eq ▸ adj)
    have ve : v≠e := fun eq => iso (eq ▸ adj.symm)
    have reach : H.Reachable a u ↔ H.Reachable a v :=
      ⟨fun r => r.trans adj.reachable,fun r => r.trans adj.symm.reachable⟩
    have fixed : ref u=ref v := by simp only [ref,reach]
    rw [sm,sm]
    simp only [ue,ve,true_and,fixed]
    by_cases ua : u∈A
    · have va : v∉A := mem_compl.mp (show v∈Aᶜ by simpa [opp,ua] using ov)
      simp [ua,va,ue,ve]
    · have va : v∈A := by simpa [opp,ua] using ov
      simp [ua,va,ue,ve]
  let outside (v : V) := if v∈S then Sᶜ else S
  have inc (v : V) : (opp v).filter (H.Adj v)⊆(outside v).filter (G.Adj v) := by
    intro i im
    obtain ⟨ic,vi⟩ := mem_filter.mp im
    apply mem_filter.mpr ⟨?_,vi.1⟩
    have h := across vi ic
    by_cases vs : v∈S <;> simp [outside,vs,h]
  have nonEar {v : V} (vn : v∈nonleaves G) (ve : v≠e) : 3≤G.degree v := by
    by_cases vh : v∈high G
    · exact (mem_filter.mp vh).2
    · have vm : v∈twos G := mem_sdiff.mpr ⟨vn,vh⟩
      exact (ve (mem_singleton.mp (only ▸ vm))).elim
  have atAnchor (v : V) (vn : v∈nonleaves G) (vs : v∈S) (ev : G.Adj e v) (vk : v∈K) :
      2≤nbr G v (outside v) := by
    have vd := nonEar vn ev.ne.symm
    have hd : 0<H.degree v := by
      apply Nat.pos_of_ne_zero
      intro zero
      have nc : (H.neighborFinset v).card=0 := by rw [card_neighborFinset_eq_degree]; omega
      have cover : G.neighborFinset v⊆K.erase v := by
        intro i im
        have vi := (G.mem_neighborFinset _ _).mp im
        apply mem_erase.mpr ⟨vi.ne.symm,?_⟩
        apply Classical.byContradiction
        intro out
        have edge : H.Adj v i := ⟨vi,fun both => out both.2⟩
        have bad := (H.mem_neighborFinset _ _).mpr edge
        rw [card_eq_zero.mp nc] at bad
        exact Finset.not_mem_empty _ bad
      have cap := card_le_card cover
      rw [card_neighborFinset_eq_degree,card_erase_of_mem vk] at cap
      have kc : K.card=3 := by simp [K,ea.ne,eb.ne,ab.ne]
      omega
    have bal := balance v
    obtain ⟨i,im⟩ := card_pos.mp (show 0<((opp v).filter (H.Adj v)).card by change 0<nbr H v (opp v); omega)
    have vi := (mem_filter.mp im).2
    have ie : i≠e := fun eq => iso (eq ▸ vi.symm)
    exact PinnedColor34.two G ie vi.1 ev.symm (mem_filter.mp (inc v im)).1 (by simp [outside,vs,es])
  have good (v : V) (vn : v∈nonleaves G) : 2≤nbr G v (outside v) := by
    by_cases ve : v=e
    · subst v
      simpa [outside,es] using PinnedColor34.two G ab.ne ea eb as' bs'
    by_cases va : v=a
    · subst v; exact atAnchor a vn as' ea ak
    by_cases vb : v=b
    · subst v; exact atAnchor b vn bs' eb bk
    have vk : v∉K := by simp [K,ve,va,vb]
    have eq : H.neighborFinset v = G.neighborFinset v := by
      ext i; simp [H,opened,vk]
    have de : H.degree v=G.degree v := by simpa only [card_neighborFinset_eq_degree] using congrArg Finset.card eq
    have min := nonEar vn ve
    have bal := balance v
    have low : 2 ≤ nbr H v (opp v) := by omega
    exact low.trans (card_le_card (inc v))
  exact ⟨S,fun v vn vs => by simpa [outside,vs] using good v vn,
    fun v vn vs => by simpa [outside,mem_compl.mp vs] using good v vn⟩

variable {G} {e a b : V} {n : ℕ}

private theorem closeRoute (p : Route G e a b n) (only : twos G={e})
    (ea : G.Adj e a) (eb : G.Adj e b)
    (ab : a≠b) (par : n%2=0) : GoodCut G := by
  have nz : n≠0 := fun eq => ab (p.start.symm.trans (eq ▸ p.finish))
  exact cycle G only (by omega) par p.atIdx p.step p.unique p.avoid (by rwa [p.start]) (by rwa [p.finish])

/-- A triangle on the first edge of a simple route allows either parity.
If its third vertex is on the route, the two prefixes to it have lengths one and two. -/
private theorem parity (p : Route G e a b n) (two : 2≤n) (only : twos G={e})
    (ea : G.Adj e a) (eb : G.Adj e b) (ab : a≠b)
    {z : V} (ze : z≠e) (az : G.Adj a z) (uz : G.Adj (p.atIdx 1) z) :
    GoodCut G := by
  classical
  by_cases ev : n%2=0
  · exact closeRoute p only ea eb ab ev
  have au : G.Adj a (p.atIdx 1) := by simpa only [p.start] using p.step 0 (by omega)
  have earlier (i j : ℕ) (ij : i < j) (jn : j≤n) : ∀ k≤n-j, p.atIdx i ≠ (p.suffix j jn).atIdx k := by
    intro k hk eq
    have := p.unique i (by omega) (j+k) (by omega) eq
    omega
  have absent {j : ℕ} (jp : 0 < j) (jn : j≤n) : ∀ k≤n-j, a≠(p.suffix j jn).atIdx k :=
    by simpa only [p.start] using earlier 0 j jp jn
  by_cases hit : ∃ i≤n, p.atIdx i=z
  · obtain ⟨i,hi,iz⟩ := hit
    have ip : 1 < i := by
      by_cases le : 1 < i
      · exact le
      exfalso
      rcases (show i=0 ∨ i=1 by omega) with rfl|rfl
      · exact az.ne (p.start.symm.trans iz)
      · exact uz.ne iz
    let t := p.suffix i hi
    by_cases oddTail : (n-i)%2=1
    · let r := t.prepend (by rwa [iz]) ea.ne.symm (absent (by omega) hi)
      exact closeRoute r only ea eb ab (by omega)
    · let s := t.prepend (by rwa [iz]) (p.avoid 1 (by omega)) (earlier 1 i ip hi)
      have fresh (k : ℕ) (hk : k≤n-i+1) : a≠s.atIdx k := by
        cases k with
        | zero => exact au.ne
        | succ j => exact absent (by omega) hi j (by omega)
      let r := s.prepend au ea.ne.symm fresh
      exact closeRoute r only ea eb ab (by omega)
  · have zfresh (k : ℕ) (hk : k≤n-1) : z≠(p.suffix 1 (by omega)).atIdx k :=
      fun eq => hit ⟨1+k,by omega,eq.symm⟩
    let s := (p.suffix 1 (by omega)).prepend uz.symm ze zfresh
    have fr (k : ℕ) (hk : k≤n-1+1) : a≠s.atIdx k := by
      cases k with
      | zero => exact az.ne
      | succ j => exact absent (j:=1) (by decide) (by omega) j (by omega)
    let r := s.prepend az ea.ne.symm fr
    exact closeRoute r only ea eb ab (by omega)
variable (G)

theorem single (support : ∀ u v,G.Adj u v → 0<trianglesAt G u → 0<trianglesAt G v →
      ∃ z,G.Adj u z ∧ G.Adj v z)
    (zeros : ∀ u v,2≤G.degree u → 2≤G.degree v → trianglesAt G u=0 → trianglesAt G v=0 → u=v)
    {e : V} (only : twos G={e}) (pe : 0<trianglesAt G e) :
    GoodCut G := by
  classical
  have et : e∈twos G := only ▸ mem_singleton_self _
  obtain ⟨a,b,ear,ea,eb,ab⟩ := SharedExact34.ear_pair G (LowSample.two_degree G et) pe
  by_cases reach : (opened G {e,a,b}).Reachable a b
  · obtain ⟨n,two,⟨r⟩⟩ := OneEar.route_of_reach G ear eb ab reach
    by_cases ev : n%2=0
    · exact closeRoute r only ea eb ab.ne ev
    have interior {a b : V} (p : Route G e a b n) : 2≤G.degree (p.atIdx 1) :=
      OneEar.deg2 G (fun eq => by have := p.unique 0 (by omega) 2 (by omega) eq; omega)
        (p.step 0 (by omega)).symm (p.step 1 (by omega))
    have finishEnd {a b : V} (p : Route G e a b n) (ea : G.Adj e a) (eb : G.Adj e b) (ab : G.Adj a b)
        (ear : G.neighborFinset e={a,b}) (pos : 0<trianglesAt G (p.atIdx 1)) : GoodCut G := by
      have near := p.step 0 (by omega)
      rw [p.start] at near
      have pa := (TrianglePrune.triangle_iff G a).mpr ⟨e,b,ea.symm,ab,eb⟩
      obtain ⟨z,az,uz⟩ := support a _ near pa pos
      have ze : z≠e := by
        intro eq
        have m := (G.mem_neighborFinset _ _).mpr (show G.Adj e (p.atIdx 1) from eq ▸ uz.symm)
        rw [ear,mem_insert,mem_singleton] at m
        rcases m with ua|ub
        · exact near.ne ua.symm
        · have idx := p.unique 1 (by omega) n le_rfl (ub.trans p.finish.symm)
          omega
      exact parity p two only ea eb ab.ne ze az uz
    by_cases pos : 0<trianglesAt G (r.atIdx 1)
    · exact finishEnd r ea eb ab ear pos
    have other : 0<trianglesAt G (r.reverse.atIdx 1) := by
      apply Nat.pos_of_ne_zero
      intro zero
      have same := zeros _ _ (interior r) (interior r.reverse) (by omega) zero
      have := r.unique 1 (by omega) (n-1) (by omega) same
      omega
    exact finishEnd r.reverse eb ea ab.symm (ear.trans (pair_comm ..)) other
  · exact split G only ear ab reach

end Graffiti384b.CoreColor33
#print axioms Graffiti384b.CoreColor33.single
