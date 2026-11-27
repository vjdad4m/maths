import NoFiveSeventh133

namespace Graffiti133FarPentagon
open SimpleGraph Graffiti133 Graffiti133RevisitSix Graffiti133Pentagon Graffiti133NoFive Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Frame (G : SimpleGraph V) where
  c : Fin 5 → V
  inj : Function.Injective c
  adj : ∀ i j, G.Adj (c i) (c j) ↔ pent i j
  h4 : FourCycleFree G

def MakeOne (F : Frame G) (x : V) (i : Fin 5) : Prop :=
  (∀ j, x ≠ F.c j) ∧ ∀ j, G.Adj x (F.c j) ↔ j = i

def MakeTwo (F : Frame G) (x : V) (i : Fin 5) : Prop :=
  (∀ j, x ≠ F.c j) ∧ ∀ j, G.Adj x (F.c j) ↔ j = i ∨ j = i+1

def Near (F : Frame G) (x : V) : Prop := (∀ i, x ≠ F.c i) ∧ ∃ i, G.Adj x (F.c i)
def Far (F : Frame G) (x : V) : Prop := (∀ i, x ≠ F.c i) ∧ ∀ i, ¬G.Adj x (F.c i)

theorem build_frame (h4 : FourCycleFree G) (h5 : ¬ NoSimpleFive133 G) :
    Nonempty (Frame G) := by
  classical
  unfold NoSimpleFive133 at h5
  push_neg at h5
  obtain ⟨a,b,c,d,e,hn,hAB,hBC,hCD,hDE,hEA⟩ := h5
  let f : Fin 5 → V := ![a,b,c,d,e]
  have inj : Function.Injective f := by
    apply List.nodup_ofFn.mp
    simpa [f,List.ofFn_succ] using hn
  have hside (i : Fin 5) : G.Adj (f i) (f (i+1)) := by
    fin_cases i
    all_goals first | exact hAB | exact hBC | exact hCD | exact hDE | exact hEA.1
  exact ⟨⟨f,inj,cycle_pentagon h4 inj hside,h4⟩⟩

namespace Frame
variable (F : Frame G)

private lemma finite_contact : ∀ b : Fin 5 → Bool,
    (∀ i, b i = true → b (i+2) = false) → (∃ i, b i = true) →
    (∃ i, ∀ j, b j = true ↔ j = i) ∨ (∃ i, ∀ j, b j = true ↔ j = i ∨ j = i+1) := by
  decide

private lemma forbid2 {x : V} (hx : ∀ i, x ≠ F.c i) (i : Fin 5)
    (h : G.Adj x (F.c i)) : ¬G.Adj x (F.c (i+2)) := by
  intro e
  have eq := F.h4 (F.c i) (F.c (i+2)) x (F.c (i+1))
    (fun w => (show i ≠ i+2 by fin_cases i <;> decide) (F.inj w)) h.symm e.symm
    ((F.adj _ _).mpr (Or.inl rfl))
    ((F.adj _ _).mpr (Or.inr (by fin_cases i <;> decide)))
  exact hx _ eq

theorem classify {x : V} (hx : Near F x) :
    (∃ i, MakeOne F x i) ∨ (∃ i, MakeTwo F x i) := by
  classical
  let b : Fin 5 → Bool := fun i => decide (G.Adj x (F.c i))
  have btrue (i : Fin 5) : b i = true ↔ G.Adj x (F.c i) := by simp [b]
  have sep (i : Fin 5) (h : b i = true) : b (i+2) = false := by
    cases he : b (i+2)
    · rfl
    · exact (F.forbid2 hx.1 i ((btrue _).mp h) ((btrue _).mp he)).elim
  obtain ⟨i,hi⟩ := hx.2
  rcases finite_contact b sep ⟨i,(btrue _).mpr hi⟩ with ⟨j,hj⟩ | ⟨j,hj⟩
  · exact Or.inl ⟨j,hx.1,fun w => (btrue _).symm.trans (hj w)⟩
  · exact Or.inr ⟨j,hx.1,fun w => (btrue _).symm.trans (hj w)⟩

private lemma far_ne_near {a b : V} (ha : Far F a) (hb : Near F b) : a ≠ b := by
  intro e
  obtain ⟨i,hi⟩ := hb.2
  exact ha.2 i (e.symm ▸ hi)

private theorem completes_far (no7 : ¬∃ f : Fin 7 → V, InducedPath G f)
    {x y z : V} (hx : Near F x) (hy : Far F y) (hz : Far F z)
    (exy : G.Adj x y) (eyz : G.Adj y z) : G.Adj x z := by
  classical
  apply Classical.byContradiction
  intro no
  obtain ⟨p,hp,h0,ht⟩ := extend_pentagon F.h4 F.inj F.adj x hx.1 hx.2
  have offY (i : Fin 5) : y ≠ p i := by
    intro e
    by_cases h : i.val=0
    · have eq : i=0 := Fin.ext h
      rw [eq,h0] at e
      exact exy.ne e.symm
    · obtain ⟨j,ej⟩ := ht i (Nat.pos_of_ne_zero h)
      exact hy.1 j (e.trans ej)
  have adjY : G.Adj y (p 0) := h0.symm ▸ exy.symm
  have noY (i : Fin 5) (h : 0 < i.val) : ¬G.Adj y (p i) := by
    obtain ⟨j,hj⟩ := ht i h
    exact fun e => hy.2 j (hj ▸ e)
  obtain ⟨q,hq,q0,qt⟩ := prepend_induced_with_positions (by decide) hp y offY adjY noY
  change q (0:Fin 6)=y at q0
  have q_rest (i : Fin 6) (h : 0 < i.val) : q i = x ∨ ∃ j, q i = F.c j := by
    let t : Fin 5 := ⟨i.val-1,by have := i.isLt; omega⟩
    have eq : q i = p t := qt i h
    by_cases e : t.val=0
    · have et : t=0 := Fin.ext e
      exact Or.inl (eq.trans (et ▸ h0))
    · obtain ⟨j,hj⟩ := ht t (Nat.pos_of_ne_zero e)
      exact Or.inr ⟨j,eq.trans hj⟩
  have offZ (i : Fin 6) : z ≠ q i := by
    intro e
    by_cases h : i.val=0
    · have eq : i=0 := Fin.ext h
      rw [eq,q0] at e
      exact eyz.ne e.symm
    · rcases q_rest i (Nat.pos_of_ne_zero h) with eq | ⟨j,eq⟩
      · exact (F.far_ne_near hz hx) (e.trans eq)
      · exact hz.1 j (e.trans eq)
  have adjZ : G.Adj z (q 0) := q0.symm ▸ eyz.symm
  have noZ (i : Fin 6) (h : 0 < i.val) : ¬G.Adj z (q i) := by
    intro e
    rcases q_rest i h with eq | ⟨j,eq⟩
    · exact no (eq ▸ e.symm)
    · exact hz.2 j (eq ▸ e)
  obtain ⟨r,hr,_,_⟩ := prepend_induced_with_positions (by decide) hq z offZ adjZ noZ
  exact no7 ⟨r,hr⟩

private theorem far_has_near (hc : G.Connected)
    (no7 : ¬∃ f : Fin 7 → V, InducedPath G f) :
    ∀ y, Far F y → ∃ x, Near F x ∧ G.Adj x y := by
  classical
  have step (u v : V) (e : G.Adj u v)
      (hu : Far F u → ∃ x, Near F x ∧ G.Adj x u) :
      Far F v → ∃ x, Near F x ∧ G.Adj x v := by
    intro hv
    have out : ∀ i, u ≠ F.c i := fun i eq => hv.2 i ((eq ▸ e).symm)
    by_cases near : ∃ i, G.Adj u (F.c i)
    · exact ⟨u,⟨out,near⟩,e⟩
    · have hFar : Far F u := ⟨out,fun i h => near ⟨i,h⟩⟩
      obtain ⟨x,hx,ex⟩ := hu hFar
      exact ⟨x,hx,F.completes_far no7 hx hFar hv ex e⟩
  intro y
  obtain ⟨p⟩ := hc (F.c 0) y
  have hwalk {a b : V} (q : G.Walk a b)
      (ha : Far F a → ∃ x, Near F x ∧ G.Adj x a) :
      Far F b → ∃ x, Near F x ∧ G.Adj x b := by
    induction q with
    | nil => exact ha
    | cons e q ih => exact ih (step _ _ e ha)
  exact hwalk p (fun h => (h.1 0 rfl).elim)

theorem far_independent (hc : G.Connected) (no7 : ¬∃ f : Fin 7 → V, InducedPath G f)
    (min : ∀ x, 2 ≤ localIndependence G x)
    {y z : V} (hy : Far F y) (hz : Far F z) :
    ¬ G.Adj y z := by
  classical
  intro e
  obtain ⟨x,hx,ex⟩ := F.far_has_near hc no7 y hy
  have ez := F.completes_far no7 hx hy hz ex e
  have allN (v : V) (hv : G.Adj y v) : v = x ∨ v = z := by
    have out : ∀ i, v ≠ F.c i := fun i eq => hy.2 i (eq ▸ hv)
    by_cases ht : ∃ i, G.Adj v (F.c i)
    · have near : Near F v := ⟨out,ht⟩
      have hvz := F.completes_far no7 near hy hz hv.symm e
      exact Or.inl (F.h4 y z v x e.ne hv hvz.symm ex.symm ez.symm)
    · have far : Far F v := ⟨out,fun i h => ht ⟨i,h⟩⟩
      have exv := F.completes_far no7 hx hy far ex hv
      exact Or.inr (F.h4 x y v z ex.ne exv hv ez e)
  have low : localIndependence G y ≤ 1 := by
    apply Finset.sup_le_iff.mpr
    intro A hA
    obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
    apply Finset.card_le_one.mpr
    intro a ha b hb
    rcases allN a (hN _ ha) with ea | ea <;> rcases allN b (hN _ hb) with eb | eb
    · exact ea.trans eb.symm
    · exact (hI _ ha _ hb (ea.symm ▸ eb.symm ▸ ez)).elim
    · exact (hI _ ha _ hb (ea.symm ▸ eb.symm ▸ ez.symm)).elim
    · exact ea.trans eb.symm
  have h := min y
  omega

#print axioms far_independent
end Frame
end Graffiti133FarPentagon
