import RemoteSixMixed
import RemoteGapRunPacking

namespace KelmansCactus.AtomicBridge.RemoteFourMixedCycle
open SimpleGraph Finset
open RemoteSixMixed (Between)
open RemoteGapRunPacking (RunCover run_factor runCover_factor)
open RemoteVacancyRails (factor_disjUnion)
open SquareCap (FactorOn HasFactor)
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A sealed run is a simple path whose last vertex is adjacent to its first. -/
structure Sealed (G : SimpleGraph V) (L : List V) (u v : V) : Prop where
  path : Between G L u v
  closing : G.Adj v u

omit [DecidableEq V] in
/-- The two mixed cyclic orders of a cheap four-spoke release with genuinely
diagonal exterior strips. Here P joins one opposite pair and Q the other,
including their spokes and any slots on the actual expanded routes. -/
theorem diagonal_cycles (P Q : List V) {a b c d : V}
    (ac : Between G P a c) (bd : Between G Q b d)
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) (da : G.Adj d a)
    (apart : ∀ x∈P,x∉Q) :
    Sealed G (P++Q) a d ∧ Sealed G (P++Q.reverse) a b :=
  ⟨⟨ac.concat bd bc.symm apart,da⟩,
   ⟨ac.concat bd.reverse cd (fun x hx hm=>apart x hx (by simpa using hm)),ab.symm⟩⟩

/-- Open the same cycle at any specified vertex without changing its support
or number of vertices. This is what lets an arbitrary common ear be retained
as a tail rather than forcing the strip endpoints to be the terminal ports. -/
theorem open_at {L : List V} {u v x : V} (C : Sealed G L u v) (inside : x∈L) :
    ∃ R : List V, R.Nodup ∧ R.Chain' G.Adj ∧ R.getLast?=some x ∧
      R.toFinset=L.toFinset ∧ R.length=L.length := by
  obtain ⟨A,B,eq⟩ := List.append_of_mem inside
  have oldNod : (A++x::B).Nodup := eq ▸ C.path.nodup
  have oldPath : (A++x::B).Chain' G.Adj := eq ▸ C.path.chain
  have oldHead : (A++x::B).head?=some u := eq ▸ C.path.head
  have oldLast : (A++x::B).getLast?=some v := eq ▸ C.path.last
  have move : (A++x::B).Perm ((x::B)++A) := List.perm_append_comm
  have joined : ((x::B)++A).Chain' G.Adj := by
    obtain ⟨p,q,_⟩ := List.chain'_append.mp oldPath
    apply q.append p
    intro s hs t ht
    have ms : s∈(A++x::B).getLast? := List.mem_getLast?_append_of_mem_getLast? hs
    have mt : t∈(A++x::B).head? := List.mem_head?_append_of_mem_head? ht
    rw [oldLast] at ms
    rw [oldHead] at mt
    have ev : v=s := Option.some.inj ms
    have eu : u=t := Option.some.inj mt
    rw [←ev,←eu]
    exact C.closing
  refine ⟨((x::B)++A).reverse,List.nodup_reverse.mpr (move.nodup_iff.mp oldNod),
    List.chain'_reverse.mpr (joined.imp (fun _ _ h=>h.symm)),by simp,?_ ,?_⟩
  · rw [eq]
    ext z
    simp [or_comm,or_left_comm]
  · simp [eq,Nat.add_comm]

/-- An arbitrarily long remaining nonzero ear can be appended at either chosen
base port; it need not have order one or two. The other ear tails may be
packed separately as divisible runs. -/
theorem absorb_ear {L E : List V} {u v x : V}
    (C : Sealed G L u v)
    (xIn : x∈L) (E_nodup : E.Nodup) (E_chain : E.Chain' G.Adj)
    (ear : ∀ w∈E.head?,G.Adj x w)
    (separ : Disjoint L.toFinset E.toFinset)
    (balance : 3∣L.length+E.length) : FactorOn G (L.toFinset∪E.toFinset) := by
  obtain ⟨R,Rn,Rc,Rlast,shape,len⟩ := open_at C xIn
  have nd : (R++E).Nodup := Rn.append E_nodup (by
    intro z zr ze
    exact Finset.disjoint_left.mp separ (shape ▸ List.mem_toFinset.mpr zr)
      (List.mem_toFinset.mpr ze))
  have chain : (R++E).Chain' G.Adj := Rc.append E_chain (by
    intro s sh w wh
    rw [Rlast] at sh
    exact (Option.some.inj sh) ▸ ear w wh)
  have n : 3∣(R++E).length := by simpa [List.length_append,len] using balance
  have f := run_factor (R++E) nd chain n
  have F : (R++E).toFinset=L.toFinset∪E.toFinset := by
    rw [List.toFinset_append,shape]
  rwa [F] at f

/-- A constructive route from diagonal-strip geometry to a full packing in
the mixed rebuilt graph. The sole ear merged into the cyclic order can be
empty, and the remaining disjoint regions are specified by ordinary runs of
length divisible by three. Neither single original rank need factor. -/
theorem diagonal_release_one_ear [Fintype V]
    (P Q E : List V) {a b c d x : V}
    (ac : Between G P a c) (bd : Between G Q b d)
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) (da : G.Adj d a)
    (apart : ∀ y∈P,y∉Q)
    (xIn : x∈P++Q) (E_nodup : E.Nodup) (E_chain : E.Chain' G.Adj)
    (ear : ∀ w∈E.head?,G.Adj x w)
    (separ : Disjoint (P++Q).toFinset E.toFinset)
    (balance : 3∣P.length+Q.length+E.length)
    (rest : Finset V) (other : RunCover G rest)
    (disjoint : Disjoint ((P++Q).toFinset∪E.toFinset) rest)
    (full : ((P++Q).toFinset∪E.toFinset)∪rest=Finset.univ) : HasFactor G := by
  have C := (diagonal_cycles P Q ac bd ab bc cd da apart).1
  have here := absorb_ear C xIn E_nodup E_chain ear separ
    (by simpa [List.length_append] using balance)
  have f := factor_disjUnion here (runCover_factor other) disjoint
  rwa [full] at f

#print axioms diagonal_cycles
#print axioms open_at
#print axioms absorb_ear
#print axioms diagonal_release_one_ear
end KelmansCactus.AtomicBridge.RemoteFourMixedCycle
