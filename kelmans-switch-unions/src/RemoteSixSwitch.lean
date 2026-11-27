import RemoteSquareConvergence

namespace KelmansCactus.AtomicBridge.RemoteSixSwitch
open SimpleGraph
open scoped Sym2
open RemoteSquareConvergence (pair lift_reach lift_reach_from_root pair_deleted)
variable {V : Type*}

structure Six (V : Type*) where
  a : V
  b : V
  c : V
  d : V
  e : V
  f : V

namespace Six
def old (s : Six V) (x y : V) : Prop :=
  pair s.a s.b x y ∨ pair s.c s.d x y ∨ pair s.e s.f x y
def new (s : Six V) (x y : V) : Prop :=
  pair s.b s.c x y ∨ pair s.d s.e x y ∨ pair s.f s.a x y
end Six

def Realization (s : Six V) (K X Y : SimpleGraph V) : Prop :=
  (∀ x y, X.Adj x y ↔ K.Adj x y ∨ s.old x y) ∧
  (∀ x y, Y.Adj x y ↔ K.Adj x y ∨ s.new x y)

private theorem reach_p {G : SimpleGraph V} {a b x y : V}
    (r : G.Reachable a b) (p : pair a b x y) : G.Reachable x y := by
  rcases p with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact r
  · exact r.symm

theorem Realization.base_le_old {s : Six V} {K X Y : SimpleGraph V}
    (h : Realization s K X Y) : K≤X :=
  fun _ _ e => (h.1 _ _).mpr (Or.inl e)
theorem Realization.base_le_new {s : Six V} {K X Y : SimpleGraph V}
    (h : Realization s K X Y) : K≤Y :=
  fun _ _ e => (h.2 _ _).mpr (Or.inl e)

private theorem old_edges {s : Six V} {K X Y : SimpleGraph V}
    (h : Realization s K X Y) :
    X.Adj s.a s.b ∧ X.Adj s.c s.d ∧ X.Adj s.e s.f :=
  ⟨(h.1 _ _).2 (Or.inr (Or.inl (Or.inl ⟨rfl,rfl⟩))),
   (h.1 _ _).2 (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl,rfl⟩)))),
   (h.1 _ _).2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))))⟩
private theorem new_edges {s : Six V} {K X Y : SimpleGraph V}
    (h : Realization s K X Y) :
    Y.Adj s.b s.c ∧ Y.Adj s.d s.e ∧ Y.Adj s.f s.a :=
  ⟨(h.2 _ _).2 (Or.inr (Or.inl (Or.inl ⟨rfl,rfl⟩))),
   (h.2 _ _).2 (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl,rfl⟩)))),
   (h.2 _ _).2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))))⟩

theorem alternate_retains_components (G : SimpleGraph V) {a b : V}
    (alt : (G.deleteEdges {s(a,b)}).Reachable a b) {x y : V}
    (r : G.Reachable x y) :
    (G.deleteEdges {s(a,b)}).Reachable x y := by
  apply lift_reach _ r
  intro u v e
  by_cases q : pair a b u v
  · exact reach_p alt q
  · apply SimpleGraph.Adj.reachable
    exact SimpleGraph.deleteEdges_adj.mpr ⟨e,by simpa only [Set.mem_singleton_iff,Sym2.eq_iff,pair] using q⟩

/-- In a crossing six-switch, old edges ab,cd are in one component and ef
is in a second. The common retained graph covers the old first component
by the residual components of c and d, and leaves the second intact.
Only ab and ef need individual alternate paths in the initial graph. -/
theorem residual_cover {s : Six V} {K X Y : SimpleGraph V}
    (h : Realization s K X Y)
    (join : X.Reachable s.a s.c) (split : ¬X.Reachable s.a s.e)
    (altAB : (X.deleteEdges {s(s.a,s.b)}).Reachable s.a s.b)
    (altEF : (X.deleteEdges {s(s.e,s.f)}).Reachable s.e s.f) :
    (∀ x, X.Reachable s.a x → K.Reachable s.c x ∨ K.Reachable s.d x) ∧
      (∀ x, X.Reachable s.e x → K.Reachable s.e x) := by
  obtain ⟨ab,cd,ef⟩ := old_edges h
  have kc (x : V) (rx : X.Reachable s.a x) :
      K.Reachable s.c x ∨ K.Reachable s.d x := by
    let D := X.deleteEdges {s(s.a,s.b)}
    have raw : D.Reachable s.c x := alternate_retains_components X altAB (join.symm.trans rx)
    rw [SimpleGraph.reachable_iff_reflTransGen] at raw
    induction raw with
    | refl => exact Or.inl (SimpleGraph.Reachable.refl _)
    | @tail u v p e ih =>
      have ru : X.Reachable s.c u :=
        ((SimpleGraph.reachable_iff_reflTransGen (G:=D) _ _).mpr p).mono (X.deleteEdges_le _)
      rcases (h.1 _ _).mp (SimpleGraph.deleteEdges_adj.mp e).1 with k|⟨r|r|r⟩
      · exact (ih (join.trans ru)).elim (fun q=>Or.inl (q.trans k.reachable)) (fun q=>Or.inr (q.trans k.reachable))
      · exact (pair_deleted e r).elim
      · rcases r with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact Or.inr (SimpleGraph.Reachable.refl _)
        · exact Or.inl (SimpleGraph.Reachable.refl _)
      · rcases r with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact (split (join.trans ru)).elim
        · exact (split (join.trans (ru.trans ef.reachable.symm))).elim
  have ke (x : V) (rx : X.Reachable s.e x) : K.Reachable s.e x := by
    let D := X.deleteEdges {s(s.e,s.f)}
    have raw : D.Reachable s.e x := alternate_retains_components X altEF rx
    apply lift_reach_from_root (X.deleteEdges_le _) raw
    intro u v ru e
    rcases (h.1 _ _).mp (SimpleGraph.deleteEdges_adj.mp e).1 with k|⟨r|r|r⟩
    · exact k
    · rcases r with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact (split ru.symm).elim
      · exact (split (ab.reachable.trans ru.symm)).elim
    · rcases r with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact (split (join.trans ru.symm)).elim
      · exact (split (join.trans (cd.reachable.trans ru.symm))).elim
    · exact (pair_deleted e r).elim
  exact ⟨kc,ke⟩

/-- No more than two new components cover both old components of a
crossing six-switch. Other current components are not needed for this claim. -/
theorem two_component_cover {s : Six V} {K X Y : SimpleGraph V}
    (h : Realization s K X Y)
    (join : X.Reachable s.a s.c) (split : ¬X.Reachable s.a s.e)
    (altAB : (X.deleteEdges {s(s.a,s.b)}).Reachable s.a s.b)
    (altEF : (X.deleteEdges {s(s.e,s.f)}).Reachable s.e s.f) :
    ∀ x, X.Reachable s.a x ∨ X.Reachable s.e x →
      Y.Reachable s.c x ∨ Y.Reachable s.d x := by
  have r := residual_cover h join split altAB altEF
  obtain ⟨_,de,_⟩ := new_edges h
  intro x p
  rcases p with q|q
  · exact ((r.1 x) q).elim (fun w=>Or.inl (w.mono h.base_le_new))
      (fun w=>Or.inr (w.mono h.base_le_new))
  · exact Or.inr (de.reachable.trans ((r.2 x q).mono h.base_le_new))

/-- Exact orientation condition for a genuine merge of the two touched
regions. If the two old sides really split, crossing arcs make progress
exactly when at least one of ac or bd is still a residual connection. -/
theorem merges_iff {s : Six V} {K X Y : SimpleGraph V}
    (h : Realization s K X Y)
    (join : X.Reachable s.a s.c) (split : ¬X.Reachable s.a s.e)
    (altAB : (X.deleteEdges {s(s.a,s.b)}).Reachable s.a s.b)
    (altEF : (X.deleteEdges {s(s.e,s.f)}).Reachable s.e s.f) :
    Y.Reachable s.c s.d ↔
      K.Reachable s.c s.d ∨ K.Reachable s.a s.c ∨ K.Reachable s.b s.d := by
  have cov := residual_cover h join split altAB altEF
  obtain ⟨ab,_,ef⟩ := old_edges h
  obtain ⟨bc,de,fa⟩ := new_edges h
  have eK := cov.2 s.f ef.reachable
  constructor
  · intro res
    by_contra! n
    rcases n with ⟨ncd,nac,nbd⟩
    have cb : K.Reachable s.c s.b :=
      (cov.1 s.b ab.reachable).elim id (fun p=>(nbd p.symm).elim)
    have ncE : ¬K.Reachable s.c s.e := fun p=>split (join.trans (p.mono h.base_le_old))
    have ncF : ¬K.Reachable s.c s.f := fun p=>ncE (p.trans eK.symm)
    have closed (x y : V) (p : K.Reachable s.c x) (e : Y.Adj x y) :
        K.Reachable s.c y := by
      rcases (h.2 _ _).mp e with k|⟨k|k|k⟩
      · exact p.trans k.reachable
      · rcases k with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact SimpleGraph.Reachable.refl _
        · exact cb
      · rcases k with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact (ncd p).elim
        · exact (ncE p).elim
      · rcases k with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact (ncF p).elim
        · exact (nac p.symm).elim
    rw [SimpleGraph.reachable_iff_reflTransGen] at res
    have supported : ∀ x, Relation.ReflTransGen Y.Adj s.c x → K.Reachable s.c x := by
      intro x p
      induction p with
      | refl => exact SimpleGraph.Reachable.refl _
      | tail _ e ih => exact closed _ _ ih e
    exact ncd (supported _ res)
  · rintro (p|p|p)
    · exact p.mono h.base_le_new
    · exact (p.mono h.base_le_new).symm.trans
        (fa.reachable.symm.trans ((eK.mono h.base_le_new).symm.trans de.reachable.symm))
    · exact bc.reachable.symm.trans (p.mono h.base_le_new)

/-- If the orientation criterion holds, the move genuinely coarsens
reachability, not merely the component count. -/
theorem merge_preserves_reach {s : Six V} {K X Y : SimpleGraph V}
    (h : Realization s K X Y)
    (join : X.Reachable s.a s.c) (split : ¬X.Reachable s.a s.e)
    (altAB : (X.deleteEdges {s(s.a,s.b)}).Reachable s.a s.b)
    (altEF : (X.deleteEdges {s(s.e,s.f)}).Reachable s.e s.f)
    (orient : K.Reachable s.c s.d ∨ K.Reachable s.a s.c ∨ K.Reachable s.b s.d) :
    (∀ x y, X.Reachable x y → Y.Reachable x y) ∧ Y.Reachable s.a s.e := by
  have joined := (merges_iff h join split altAB altEF).mpr orient
  have covers := two_component_cover h join split altAB altEF
  have shared : ∀ x, X.Reachable s.a x ∨ X.Reachable s.e x → Y.Reachable s.c x :=
    fun x p=>(covers x p).elim id (fun q=>joined.trans q)
  obtain ⟨ab,cd,ef⟩ := old_edges h
  constructor
  · intros x y p
    apply lift_reach _ p
    intro x y e
    rcases (h.1 _ _).mp e with edge|⟨r|r|r⟩
    · exact (h.base_le_new edge).reachable
    · exact reach_p ((shared _ (Or.inl (SimpleGraph.Reachable.refl _))).symm.trans
        (shared _ (Or.inl ab.reachable))) r
    · exact reach_p joined r
    · exact reach_p ((shared _ (Or.inr (SimpleGraph.Reachable.refl _))).symm.trans
        (shared _ (Or.inr ef.reachable))) r
  · exact (shared _ (Or.inl (SimpleGraph.Reachable.refl _))).symm.trans
      (shared _ (Or.inr (SimpleGraph.Reachable.refl _)))


/-- A six-switch whose common graph bypasses all three old edges always
preserves old reachability; in particular it can merge three old components. -/
theorem all_bypasses_preserve_reach {s : Six V} {K X Y : SimpleGraph V}
    (h : Realization s K X Y)
    (ab : K.Reachable s.a s.b) (cd : K.Reachable s.c s.d) (ef : K.Reachable s.e s.f) :
    ∀ x y, X.Reachable x y → Y.Reachable x y := by
  intro x y r
  apply lift_reach _ r
  intro u v e
  rcases (h.1 _ _).mp e with edge|⟨conn|conn|conn⟩
  · exact (h.base_le_new edge).reachable
  · exact reach_p (ab.mono h.base_le_new) conn
  · exact reach_p (cd.mono h.base_le_new) conn
  · exact reach_p (ef.mono h.base_le_new) conn

#print axioms all_bypasses_preserve_reach
#print axioms two_component_cover
#print axioms merges_iff
#print axioms merge_preserves_reach
end KelmansCactus.AtomicBridge.RemoteSixSwitch
