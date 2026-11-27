import FragmentFlankRules

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph
open CompactOmission (six_tree_absurd)

variable {V : Type*} {G : SimpleGraph V}

structure FragmentFrame (G : SimpleGraph V) [DecidableRel G.Adj] {n k : ℕ} (b : Layout n)
    (e : Fin (n+1) → Fin (n+1) → Bool) (D : Seams n k) (mate : Fin (n+1)) where
  f : Fin (n+1) ↪ V
  path : PathOn G {v | v ≠ f (Fin.last n)}
  B : List V
  I : Fin k → List V
  core : B.Perm (block f ++ (List.finRange k).flatMap I)
  chart : ∀ i j, G.Adj (f i) (f j) ↔ e i j = true
  inside : ∀ i, (f (D i).1 :: I i ++ [f (D i).2]).Chain' G.Adj
  first : B.head? = some (f 0)
  last : B.getLast? = some (f (rightEnd n))
  exterior : ∀ v, (∀ i, v ≠ f i) → ¬ G.Adj v (f (Fin.last n)) ∧ ¬ G.Adj v (f mate)
  pre : ∀ i, f (b.prev i) ∈ path.predecessors
  suc : ∀ i, f (b.next i) ∈ path.rev.predecessors

variable [DecidableRel G.Adj]

variable {n k : ℕ} {b : Layout n} {e : Fin (n+1) → Fin (n+1) → Bool}
variable {D : Seams n k} {mate : Fin (n+1)}

private theorem off_anchor (F : FragmentFrame G b e D mate) {L R : List V}
    (s : F.path.vertices = L ++ (F.B ++ R)) {v : V} (mem : v ∈ L ∨ v ∈ R)
    (i : Fin (n+1)) : v ≠ F.f i := by
  intro eq
  have nd : (L ++ (F.B ++ R)).Nodup := s ▸ F.path.nodup
  rcases block_cases F.f i with yes|z
  · have inB : v ∈ F.B := F.core.mem_iff.mpr (List.mem_append_left _ (eq.symm ▸ yes))
    rcases mem with left|right
    · exact (List.nodup_append.mp nd).2.2 left (List.mem_append_left _ inB)
    · exact (List.nodup_append.mp (List.nodup_append.mp nd).2.1).2.2 inB right
  · have h : v ∈ F.path.vertices := by rw [s]; simp only [List.mem_append]; tauto
    exact (F.path.covers _).mp h (eq.trans (congrArg F.f z))

private theorem opposite_distinct (F : FragmentFrame G b e D mate) {L R : List V}
    (s : F.path.vertices = L ++ (F.B ++ R)) {x y : V} (hx : x ∈ L) (hy : y ∈ R) :
    x ≠ y := by
  have nd : (L ++ (F.B ++ R)).Nodup := s ▸ F.path.nodup
  intro eq
  exact (List.nodup_append.mp nd).2.2 hx (List.mem_append_right _ (eq.symm ▸ hy))

private theorem border_left (F : FragmentFrame G b e D mate) {L : List V} {x : V}
    (h : (L ++ F.B).Chain' G.Adj) (l : x ∈ L.getLast?) : G.Adj x (F.f 0) :=
  (List.chain'_append.mp h).2.2 x l _ (by rw [F.first]; rfl)

private theorem border_right (F : FragmentFrame G b e D mate) {R : List V} {x : V}
    (h : (F.B ++ R).Chain' G.Adj) (r : x ∈ R.head?) : G.Adj x (F.f (rightEnd n)) :=
  ((List.chain'_append.mp h).2.2 _ (by rw [F.last]; rfl) x r).symm

variable [DecidableEq V] [Fintype V]

private theorem profile_at_flank (F : FragmentFrame G b e D mate) (budget : Catalogue.treeNumber G ≤ 5)
    (C : FragmentFlanks n k b e D mate) {L R : List V}
    (s : F.path.vertices = L ++ (F.B ++ R)) {v : V} (mem : v ∈ L ∨ v ∈ R) :
    ∃ m ∈ C.profiles, ProfileAt G F.f v m := by
  have off := off_anchor F s mem
  exact external_from_check budget C.single F.chart off (F.exterior v off).1 (F.exterior v off).2

private theorem pair_flanks (F : FragmentFrame G b e D mate) (budget : Catalogue.treeNumber G ≤ 5)
    (noTrace : ¬ Catalogue.Traceable G) (C : FragmentFlanks n k b e D mate)
    {U R : List V} {l r : V}
    (split : F.path.vertices = (U ++ [l]) ++ (F.B ++ r :: R)) :
    C.lmask ∈ C.profiles ∧ C.rmask ∈ C.profiles ∧
      ProfileAt G F.f l C.lmask ∧ ProfileAt G F.f r C.rmask ∧ decide (G.Adj l r) = C.linked := by
  have distinct := opposite_distinct F split (x := l) (y := r) (by simp) (by simp)
  have hereL := off_anchor F split (v := l) (Or.inl (by simp))
  have hereR := off_anchor F split (v := r) (Or.inr (by simp))
  obtain ⟨m,hm,lm⟩ := profile_at_flank F budget C split (v := l) (Or.inl (by simp))
  obtain ⟨q,hq,rq⟩ := profile_at_flank F budget C split (v := r) (Or.inr (by simp))
  have pCh : (((U ++ [l]) ++ F.B) ++ r :: R).Chain' G.Adj := by
    simpa only [split,List.append_assoc] using F.path.chain
  have lp : G.Adj l (F.f 0) := border_left F pCh.left_of_append (by simp)
  have qr : G.Adj r (F.f (rightEnd n)) :=
    border_right F (by simpa only [split] using
      (show ((U ++ [l]) ++ (F.B ++ r :: R)).Chain' G.Adj from split ▸ F.path.chain).right_of_append) rfl
  rcases C.pair m q (decide (G.Adj l r)) hm hq ((lm _).mp lp) ((rq _).mp qr) with
    ⟨T,tree⟩|⟨route,valid,enter,exit⟩|⟨em,eq,linked⟩
  · let x : Fin 2 ↪ V := ⟨![l,r],by intro i j eq; fin_cases i <;> fin_cases j <;> simp_all⟩
    have dis (i : Fin (n+1)) (j : Fin 2) : x j ≠ F.f i := by
      fin_cases j
      · exact hereL i
      · exact hereR i
    let g := extend F.f x dis
    have chart : ∀ i j, G.Adj (g i) (g j) ↔ pairEdge e m q (decide (G.Adj l r)) i j = true := by
      apply extension_chart F.chart
      · intro j
        fin_cases j
        · exact lm
        · exact rq
      · intro i j
        fin_cases i <;> fin_cases j <;> simp [x,pairLinks,G.adj_comm r l]
    exact (six_tree_absurd budget chart tree).elim
  · obtain ⟨w⟩ := realize_fragments F.core F.chart F.inside valid
    have order : (((U ++ [l]) ++ F.B) ++ r :: R).Perm F.path.vertices := by
      simpa only [split,List.append_assoc] using List.Perm.refl _
    exact (noTrace (trace_of_framed_route F.path order w pCh.left_of_append.left_of_append
      pCh.right_of_append
      (by
        intro x hx
        have ex : l = x := by simpa using hx
        exact ex ▸ (lm _).mpr enter)
      (by
        intro y hy
        have ey : r = y := by simpa using hy
        exact ey ▸ ((rq _).mpr exit).symm))).elim
  · exact ⟨em ▸ hm,eq ▸ hq,em ▸ lm,eq ▸ rq,linked⟩

private theorem advance_flank (F : FragmentFrame G b e D mate) (budget : Catalogue.treeNumber G ≤ 5)
    (noTrace : ¬ Catalogue.Traceable G) (C : FragmentFlanks n k b e D mate)
    (lmem : C.lmask ∈ C.profiles) (rmem : C.rmask ∈ C.profiles)
    {U H R : List V} {y l r : V}
    (split : F.path.vertices = (U ++ y :: l :: H) ++ (F.B ++ r :: R))
    (same : ∀ w ∈ l :: H, ProfileAt G F.f w C.lmask ∧ decide (G.Adj w r) = C.linked)
    (right : ProfileAt G F.f r C.rmask) :
    ProfileAt G F.f y C.lmask ∧ decide (G.Adj y r) = C.linked := by
  have offL := off_anchor F split (v := l) (Or.inl (by simp))
  have offR := off_anchor F split (v := r) (Or.inr (by simp))
  have offY := off_anchor F split (v := y) (Or.inl (by simp))
  have lr := opposite_distinct F split (x := l) (y := r) (by simp) (by simp)
  have yr := opposite_distinct F split (x := y) (y := r) (by simp) (by simp)
  have ly : l ≠ y := by
    have nd : ((U ++ y :: l :: H) ++ (F.B ++ r :: R)).Nodup := split ▸ F.path.nodup
    have nd' := (List.nodup_append.mp (List.nodup_append.mp nd).1).2.1
    exact fun e => (List.nodup_cons.mp nd').1 (by simp [e])
  obtain ⟨m,hm,hY⟩ := profile_at_flank F budget C split (v := y) (Or.inl (by simp))
  have hL := same l (by simp)
  have full : (((U ++ y :: l :: H) ++ F.B) ++ r :: R).Chain' G.Adj := by
    simpa only [split,List.append_assoc] using F.path.chain
  have pre := full.left_of_append.left_of_append
  have sub := pre.right_of_append
  have lyEdge : G.Adj l y := sub.rel_head.symm
  rcases C.advance lmem rmem m (decide (G.Adj y r)) hm with
      ⟨T,tree⟩|⟨route,valid,front|back⟩|⟨eq,link⟩
  · let x : Fin 3 ↪ V := ⟨![l,r,y],by intro i j eq; fin_cases i <;> fin_cases j <;> simp_all⟩
    have off (i : Fin (n+1)) (j : Fin 3) : x j ≠ F.f i := by
      fin_cases j
      · exact offL i
      · exact offR i
      · exact offY i
    let g := extend F.f x off
    have links : ∀ i j, G.Adj (x i) (x j) ↔ fragmentStepLinks C.linked (decide (G.Adj y r)) i j = true := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [x,fragmentStepLinks,lyEdge,← hL.2,G.adj_comm r l,
        G.adj_comm y l,G.adj_comm r y]
    have chart : ∀ i j, G.Adj (g i) (g j) ↔
        fragmentStepEdge e C.lmask C.rmask m C.linked (decide (G.Adj y r)) i j = true := by
      apply extension_chart F.chart _ links
      intro i
      fin_cases i
      · exact hL.1
      · exact right
      · exact hY
    exact (six_tree_absurd budget chart tree).elim
  · obtain ⟨w⟩ := realize_fragments F.core F.chart F.inside valid
    have order : (((U ++ y :: l :: H) ++ F.B) ++ r :: R).Perm F.path.vertices := by
      simpa only [split,List.append_assoc] using List.Perm.refl _
    refine (noTrace (trace_of_framed_route F.path order w pre full.right_of_append ?_ ?_)).elim
    · intro x hx
      have ee := Option.mem_def.mp hx
      rw [List.getLast?_append_of_ne_nil U (by simp),List.getLast?_cons_cons] at ee
      exact ((same x (List.mem_of_getLast? ee)).1 _).mpr front.1
    · intro t ht
      have eq : r = t := by simpa using ht
      exact eq ▸ ((right _).mpr front.2).symm
  · obtain ⟨w⟩ := realize_fragments F.core F.chart F.inside valid
    have order : (((U ++ [y]) ++ F.B) ++ ((l :: H) ++ r :: R)).Perm F.path.vertices := by
      simpa only [split,List.append_assoc,List.cons_append,List.nil_append] using
        (((List.perm_append_comm (l₁ := F.B) (l₂ := l :: H)).append_left (U ++ [y])).append_right (r :: R))
    have lp : (U ++ [y]).Chain' G.Adj := by
      exact (show ((U ++ [y]) ++ (l :: H)).Chain' G.Adj from
        by simpa only [List.append_assoc,List.cons_append,List.nil_append] using pre).left_of_append
    have rp : ((l :: H) ++ r :: R).Chain' G.Adj := by
      apply sub.tail.append full.right_of_append
      intro x hx t ht
      have eq : r = t := by simpa using ht
      have hm := List.mem_of_getLast? (Option.mem_def.mp hx)
      exact eq ▸ of_decide_eq_true ((same _ hm).2.trans back.2.2)
    refine (noTrace (trace_of_framed_route F.path order w lp rp ?_ ?_)).elim
    · intro x hx
      have eq : y = x := by simpa using hx
      exact eq ▸ (hY _).mpr back.1
    · intro v hv
      have eq : l = v := by simpa using hv
      exact eq ▸ ((hL.1 _).mpr back.2.1).symm
  · exact ⟨eq ▸ hY,link⟩

/-- Extend the flank scan to entire fragments of arbitrary length. -/
theorem traceable_of_fragment_flanks (F : FragmentFrame G b e D mate)
    (budget : Catalogue.treeNumber G ≤ 5) (C : FragmentFlanks n k b e D mate) (L R : List V)
    (split : F.path.vertices = L ++ (F.B ++ R)) : Catalogue.Traceable G := by
  classical
  by_contra noTrace
  have firstOff (empty : L = []) : ¬ BlocksFirst b e := by
    rintro ⟨i,adj⟩
    have first : F.path.first = F.f 0 := by
      have h : F.path.vertices.head? = some (F.f 0) := by
        rw [split,empty,List.nil_append,List.head?_append]
        simp [F.first]
      rw [List.head?_eq_head F.path.nonempty] at h
      exact Option.some.inj h
    have mem : F.f 0 ∈ F.path.rev.terminalFlanks := by
      rw [PathOn.terminalFlanks,PathOn.rev_last,first]
      exact Finset.mem_insert_self _ _
    exact F.path.rev.terminalFlanks_independent noTrace _ mem _
      (Finset.mem_insert_of_mem (F.suc i)) ((F.chart _ _).mpr adj)
  have lastOff (empty : R = []) : ¬ BlocksLast b e := by
    rintro ⟨i,adj⟩
    have last : F.path.last = F.f (rightEnd n) := by
      have h : F.path.vertices.getLast? = some (F.f (rightEnd n)) := by
        rw [split,empty,List.append_nil,List.getLast?_append,F.last]
        rfl
      rw [List.getLast?_eq_getLast F.path.nonempty] at h
      exact Option.some.inj h
    have mem : F.f (rightEnd n) ∈ F.path.terminalFlanks := by
      rw [PathOn.terminalFlanks,last]
      exact Finset.mem_insert_self _ _
    exact F.path.terminalFlanks_independent noTrace _ mem _
      (Finset.mem_insert_of_mem (F.pre i)) ((F.chart _ _).mpr adj)
  by_cases noL : L = []
  · have rn : R ≠ [] := fun h => C.someFlank.elim (firstOff noL) (lastOff h)
    obtain ⟨r,T,rfl⟩ := List.exists_cons_of_ne_nil rn
    obtain ⟨q,hq,rq⟩ := profile_at_flank F budget C split (v := r) (Or.inr (by simp))
    have ch : (F.B ++ r :: T).Chain' G.Adj := (split ▸ F.path.chain).right_of_append
    obtain ⟨route,valid,link⟩ := C.leftEmpty (firstOff noL) q hq
      ((rq _).mp (border_right F ch rfl))
    obtain ⟨w⟩ := realize_fragments F.core F.chart F.inside valid
    have order : (([] ++ F.B) ++ r :: T).Perm F.path.vertices := by simp [split,noL]
    exact noTrace (trace_of_framed_route F.path order w (by simp) ch.right_of_append
      (by simp) (by
        intro x hx
        have ee : r = x := by simpa using hx
        exact ee ▸ ((rq _).mpr link).symm))
  · have leftForm : ∃ U l, L = U ++ [l] :=
      ⟨L.dropLast,L.getLast noL,(List.dropLast_append_getLast noL).symm⟩
    obtain ⟨U,l,rfl⟩ := leftForm
    by_cases noR : R = []
    · obtain ⟨m,hm,lm⟩ := profile_at_flank F budget C split (v := l) (Or.inl (by simp))
      have ch : ((U ++ [l]) ++ F.B).Chain' G.Adj := by simpa [split,noR] using F.path.chain
      obtain ⟨route,valid,link⟩ := C.rightEmpty (lastOff noR) m hm
        ((lm _).mp (border_left F ch (by simp)))
      obtain ⟨w⟩ := realize_fragments F.core F.chart F.inside valid
      have order : (((U ++ [l]) ++ F.B) ++ []).Perm F.path.vertices := by simp [split,noR]
      exact noTrace (trace_of_framed_route F.path order w ch.left_of_append (by simp)
        (by
          intro x hx
          have ee : l = x := by simpa using hx
          exact ee ▸ (lm _).mpr link) (by simp))
    · obtain ⟨r,T,rfl⟩ := List.exists_cons_of_ne_nil noR
      obtain ⟨lm,rm,left,right,link⟩ := pair_flanks F budget noTrace C split
      have eliminate (A : List V) (v : V) (S : List V)
          (form : F.path.vertices = (A ++ v :: S) ++ (F.B ++ r :: T))
          (same : ∀ x ∈ v :: S, ProfileAt G F.f x C.lmask ∧ decide (G.Adj x r) = C.linked) : False := by
        induction A using List.reverseRecOn generalizing v S with
        | nil =>
          have eq : F.path.first = v := by
            have head : F.path.vertices.head? = some v := by simp [form]
            rw [List.head?_eq_head F.path.nonempty] at head
            exact Option.some.inj head
          have isStart : v ∈ F.path.rev.terminalFlanks := by
            rw [PathOn.terminalFlanks,F.path.rev_last,eq]
            exact Finset.mem_insert_self _ _
          obtain ⟨i,ei⟩ := C.stop
          exact F.path.rev.terminalFlanks_independent noTrace _ isStart _
            (Finset.mem_insert_of_mem (F.suc i)) (((same v (by simp)).1 _).mpr ei)
        | append_singleton B y ih =>
          have now : F.path.vertices = (B ++ y :: v :: S) ++ (F.B ++ r :: T) := by
            simpa only [List.append_assoc,List.cons_append,List.nil_append] using form
          have new := advance_flank F budget noTrace C lm rm now same right
          apply ih y (v :: S) now
          intro x hx
          rcases List.mem_cons.mp hx with rfl|hx
          · exact new
          · exact same x hx
      exact eliminate U l [] split (by simpa only [List.mem_singleton,forall_eq] using And.intro left link)

#print axioms traceable_of_fragment_flanks

end Graffiti199Depleted.WiderOmission
