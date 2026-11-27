import RemoteSixSwitch
import RemoteGapRunPacking

namespace KelmansCactus.AtomicBridge.RemoteSixMixed
open SimpleGraph Finset
open RemoteSixSwitch
open RemoteGapRunPacking (run_factor joined_at_factor)
open SquareCap (FactorOn)
variable {V : Type*} {G : SimpleGraph V}

structure Between (G : SimpleGraph V) (L : List V) (a b : V) : Prop where
  nodup : L.Nodup
  chain : L.Chain' G.Adj
  head : L.head?=some a
  last : L.getLast?=some b

theorem Between.reverse {L : List V} {a b : V} (w : Between G L a b) :
    Between G L.reverse b a :=
  ⟨List.nodup_reverse.mpr w.nodup, List.chain'_reverse.mpr (w.chain.imp fun _ _ e=>e.symm),
    (List.head?_reverse).trans w.last,(List.getLast?_reverse).trans w.head⟩

theorem Between.mono {G H : SimpleGraph V} (sub : G≤H) {L : List V} {a b : V}
    (w : Between G L a b) : Between H L a b :=
  ⟨w.nodup,w.chain.imp fun _ _ e=>sub e,w.head,w.last⟩

theorem Between.concat {L R : List V} {a b c d : V}
    (u : Between G L a b) (v : Between G R c d) (link : G.Adj b c)
    (notBoth : ∀ x∈L,x∉R) : Between G (L++R) a d := by
  refine ⟨u.nodup.append v.nodup notBoth,u.chain.append v.chain ?_,
    by simp [u.head],by simp [v.last]⟩
  intro x xm y ym
  rw [u.last] at xm
  rw [v.head] at ym
  have ex : b=x := Option.some.inj xm
  have ey : c=y := Option.some.inj ym
  rwa [←ex,←ey]

/-- In the nonmerging six orientation, mixing the two gate choices still
gives spanning runs across all three residual paths. One uses old cd and new fa,
and the other uses old ab and new de. Neither run is required to be a rank. -/
theorem mixed_runs {s : Six V} {K X Y : SimpleGraph V}
    (real : Realization s K X Y) (A B C : List V)
    (ra : Between K A s.a s.d) (rb : Between K B s.b s.c) (rc : Between K C s.e s.f)
    (ba : ∀ x∈B,x∉A) (ac : ∀ x∈A,x∉C) (bc : ∀ x∈B,x∉C) :
    Between (X⊔Y) (B++A.reverse++C.reverse) s.b s.e ∧
      Between (X⊔Y) (B.reverse++A++C) s.c s.f := by
  have sub : K≤X⊔Y := le_trans real.base_le_old le_sup_left
  have A' := ra.mono sub
  have B' := rb.mono sub
  have C' := rc.mono sub
  have cd : (X⊔Y).Adj s.c s.d :=
    (show X≤X⊔Y from le_sup_left) ((real.1 _ _).2 (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl,rfl⟩)))))
  have fa : (X⊔Y).Adj s.f s.a :=
    (show Y≤X⊔Y from le_sup_right) ((real.2 _ _).2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩)))))
  have ab : (X⊔Y).Adj s.a s.b :=
    (show X≤X⊔Y from le_sup_left) ((real.1 _ _).2 (Or.inr (Or.inl (Or.inl ⟨rfl,rfl⟩))))
  have de : (X⊔Y).Adj s.d s.e :=
    (show Y≤X⊔Y from le_sup_right) ((real.2 _ _).2 (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl,rfl⟩)))))
  constructor
  · apply (B'.concat A'.reverse cd (fun x h m=>ba x h (by simpa using m))).concat C'.reverse fa.symm
    intro x him m
    have xc : x∈C := by simpa using m
    rcases List.mem_append.mp him with h|h
    · exact bc x h xc
    · exact ac x (by simpa using h) xc
  · apply (B'.reverse.concat A' ab.symm (fun x h=>ba x (by simpa using h))).concat C' de
    intro x him m
    rcases List.mem_append.mp him with h|h
    · exact bc x (by simpa using h) m
    · exact ac x h m

/-- A mixed run can absorb an omitted slot at its exposed end, independently
of the length of each of the three residual paths. -/
theorem factor_with_exposed_slot [DecidableEq V] {L : List V} {a b q : V}
    (path : Between G L a b) (edge : G.Adj b q) (outside : q∉L.toFinset)
    (div : 3∣L.length+1) : FactorOn G (L.toFinset∪{q}) := by
  have p := joined_at_factor L [] q path.nodup (by simp) path.chain (by simp)
    (by
      intro x xend
      rw [path.last] at xend
      have bx : b=x := Option.some.inj xend
      exact bx ▸ edge)
    (by simp) (by simp) outside (by simp) (by simpa using div)
  simpa using p

/-- The union of a split six-switch still repairs the entire affected region
whenever the omitted slot can be attached at any of the four exposed ports.
No single rank is assumed to support all tiles. -/
theorem mixed_factor_at_outer_port [DecidableEq V] {s : Six V} {K X Y : SimpleGraph V}
    (real : Realization s K X Y) (A B C : List V)
    (ra : Between K A s.a s.d) (rb : Between K B s.b s.c) (rc : Between K C s.e s.f)
    (ba : ∀ x∈B,x∉A) (ac : ∀ x∈A,x∉C) (bc : ∀ x∈B,x∉C)
    (q : V) (away : q∉A.toFinset∪B.toFinset∪C.toFinset)
    (touch : (X⊔Y).Adj s.b q ∨ (X⊔Y).Adj s.c q ∨ (X⊔Y).Adj s.e q ∨ (X⊔Y).Adj s.f q)
    (div : 3∣A.length+B.length+C.length+1) :
    FactorOn (X⊔Y) (A.toFinset∪B.toFinset∪C.toFinset∪{q}) := by
  obtain ⟨w,z⟩ := mixed_runs real A B C ra rb rc ba ac bc
  have go {L : List V} {x y : V} (p : Between (X⊔Y) L x y)
      (shape : L.toFinset=A.toFinset∪B.toFinset∪C.toFinset)
      (len : L.length=A.length+B.length+C.length)
      (edge : (X⊔Y).Adj y q) :
      FactorOn (X⊔Y) (A.toFinset∪B.toFinset∪C.toFinset∪{q}) := by
    have hf := factor_with_exposed_slot p edge (shape.symm ▸ away) (len.symm ▸ div)
    rwa [shape] at hf
  rcases touch with e|e|e|e
  · apply go w.reverse _ _ e
    · ext x; simp [or_comm,or_assoc,or_left_comm]
    · simp [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
  · apply go z.reverse _ _ e
    · ext x; simp [or_comm,or_assoc,or_left_comm]
    · simp [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
  · apply go w _ _ e
    · ext x; simp [or_comm,or_assoc,or_left_comm]
    · simp [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
  · apply go z _ _ e
    · ext x; simp [or_comm,or_assoc,or_left_comm]
    · simp [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]

#print axioms mixed_runs
#print axioms mixed_factor_at_outer_port
end KelmansCactus.AtomicBridge.RemoteSixMixed
