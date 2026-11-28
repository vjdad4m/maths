import PosaSpine189
import PosaGreedy189
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.PosaSpine
open private Graffiti189LongestPath.FanRoutable.path_append_separated from FanLower189
set_option warningAsError true
set_option maxHeartbeats 6000000
namespace Graffiti189LongestPath.PosaTracks
variable {V ι : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A bypass carries its own ordered spine endpoints and its exterior support. -/
structure Detour {a b : V} (p : G.Walk a b) (lo hi : Nat) where
  strict : lo<hi
  bound : hi≤p.length
  walk : G.Walk (p.getVert lo) (p.getVert hi)
  simple : walk.IsPath
  only : ∀ z∈walk.support,z∈p.support → z=p.getVert lo ∨ z=p.getVert hi

variable {a b : V} (p : G.Walk a b) (S : Finset ι) (l r : ι → Nat)
    (D : ∀ j∈S,Detour p (l j) (r j))

structure Track (xs : List ι) (start : Nat) where
  walk : G.Walk (p.getVert start) (p.getVert p.length)
  simple : walk.IsPath
  ordered : Ordered p walk
  bounds : Bounds p walk start p.length
  skip : ∀ i≤p.length,∀ j∈xs,l j<i → i<r j → p.getVert i∉walk.support
  hits : ∀ j∈xs,p.getVert (l j)∈walk.support ∧ p.getVert (r j)∈walk.support
  complete : ∀ i≤p.length,start≤i →
    (∀ j∈xs,¬(l j<i ∧ i<r j)) → p.getVert i∈walk.support
  exterior : ∀ z∈walk.support,z∉p.support →
    ∃ j∈xs,∃ h : j∈S,z∈(D j h).walk.support

/-- Realize one separated track as an actual ordered simple walk.
Its exact used exterior vertices remain labelled by their detour. -/
theorem make_track (hp : p.IsPath)
    (offDisj : ∀ i (hi : i∈S) j (hj : j∈S), i≠j →
      ∀ z∈(D i hi).walk.support,z∈(D j hj).walk.support → z∈p.support)
    (xs : List ι) (start : Nat) (startN : start≤p.length)
    (source : ∀ i∈xs,i∈S)
    (sep : xs.Pairwise (fun i j => r i≤l j))
    (left : ∀ i∈xs,start≤l i) : Nonempty (Track p S l r D xs start) := by
  classical
  induction xs generalizing start with
  | nil =>
    obtain ⟨q,qp,qo,qb,_,qs,qc⟩ := spine_segment p hp start p.length startN le_rfl
    refine ⟨⟨q,qp,qo,qb,?_,?_,?_,?_⟩⟩
    · intro i hi j nj
      simp at nj
    · intro j nj
      simp at nj
    · intro i il si _
      exact (qc i il).mpr ⟨si,il⟩
    · intro z hz no
      exact (no (qs z hz)).elim
  | cons j xs ih =>
    have jj : j∈S := source _ List.mem_cons_self
    let M := D j jj
    have jl : start≤l j := left _ List.mem_cons_self
    have bf := (List.pairwise_cons.mp sep).1
    obtain ⟨T⟩ := ih (r j) M.bound
      (fun i hi => source i (List.mem_cons_of_mem _ hi))
      (List.pairwise_cons.mp sep).2 bf
    obtain ⟨q,qp,qo,qb,_,qs,qc⟩ := spine_segment p hp start (l j) jl
      (M.strict.le.trans M.bound)
    have ex := ordered_exterior p hp M.strict M.bound M.simple M.only
    let P := q.append M.walk
    have Pp : P.IsPath := Graffiti189LongestPath.FanRoutable.path_append_separated
      qp M.simple (by
        intro z zq zm
        rcases M.only z zm (qs z zq) with h|h
        · exact h
        have xx := (qb (r j) M.bound (h ▸ zq)).2
        exact (not_le_of_gt M.strict xx).elim)
    have Po : Ordered p P := ordered_append p qp qo ex.1 qb ex.2
    have Pb : Bounds p P start (r j) := bound_append p jl M.strict.le qb ex.2
    have offP (z : V) (zp : z∈P.support) (zo : z∉p.support) : z∈M.walk.support := by
      rw [show P=q.append M.walk from rfl,support_append,List.mem_append] at zp
      exact zp.elim (fun h => (zo (qs z h)).elim) List.mem_of_mem_tail
    let W := P.append T.walk
    have Wp : W.IsPath := Graffiti189LongestPath.FanRoutable.path_append_separated
      Pp T.simple (by
        intro z zp zt
        by_cases zi : z∈p.support
        · obtain ⟨n,e,nl⟩ := mem_support_iff_exists_getVert.mp zi
          have q := (Pb n nl (e.symm ▸ zp)).2
          have h := (T.bounds n nl (e.symm ▸ zt)).1
          have nn : n=r j := by omega
          exact e.symm.trans (congrArg p.getVert nn)
        obtain ⟨i,ix,ii,ii'⟩ := T.exterior z zt zi
        have ne : j≠i := by
          intro e
          have h := bf i ix
          rw [←e] at h
          exact (not_le_of_gt M.strict h)
        exact (zi (offDisj j jj i ii ne z (offP z zp zi) ii')).elim)
    refine ⟨⟨W,Wp,ordered_append p Pp Po T.ordered Pb T.bounds,
      bound_append p (jl.trans M.strict.le) M.bound Pb T.bounds,?_,?_,?_,?_⟩⟩
    · intro n nl i ix lim ri wn
      rw [show W=P.append T.walk from rfl,support_append,List.mem_append] at wn
      rcases List.mem_cons.mp ix with he|hi
      · subst i
        rcases wn with pn|tn
        · rw [show P=q.append M.walk from rfl,support_append,List.mem_append] at pn
          rcases pn with qn|mn
          · exact (not_le_of_gt lim (qb _ nl qn).2)
          have h := (ex.2 n nl (List.mem_of_mem_tail mn)).1
          have e := M.only _ (List.mem_of_mem_tail mn) (p.getVert_mem_support n)
          rcases e with el|er
          · have z := hp.getVert_injOn nl (M.strict.le.trans M.bound) el
            omega
          · have z := hp.getVert_injOn nl M.bound er
            omega
        · exact (not_le_of_gt ri (T.bounds n nl (List.mem_of_mem_tail tn)).1)
      rcases wn with h|h
      · exact (not_le_of_gt lim ((Pb n nl h).2.trans (bf i hi)))
      · exact T.skip n nl i hi lim ri (List.mem_of_mem_tail h)
    · intro i ix
      rcases List.mem_cons.mp ix with he|hi
      · subst i
        change p.getVert (l j)∈(P.append T.walk).support ∧ p.getVert (r j)∈(P.append T.walk).support
        exact ⟨(mem_support_append_iff P T.walk).mpr
          (Or.inl ((mem_support_append_iff q M.walk).mpr (Or.inl q.end_mem_support))),
          (mem_support_append_iff P T.walk).mpr (Or.inl P.end_mem_support)⟩
      · have hits := T.hits i hi
        rw [show W=P.append T.walk from rfl]
        exact ⟨(mem_support_append_iff P T.walk).mpr (Or.inr hits.1),
          (mem_support_append_iff P T.walk).mpr (Or.inr hits.2)⟩
    · intro n nl ni keep
      apply (mem_support_append_iff P T.walk).mpr
      by_cases le : n≤l j
      · exact Or.inl ((mem_support_append_iff q M.walk).mpr (Or.inl ((qc n nl).mpr ⟨ni,le⟩)))
      have no := keep j List.mem_cons_self
      have rn : r j≤n := by omega
      exact Or.inr (T.complete n nl rn (fun i hi => keep i (List.mem_cons_of_mem _ hi)))
    · intro z zw zo
      rw [show W=P.append T.walk from rfl,support_append,List.mem_append] at zw
      rcases zw with h|h
      · exact ⟨j,List.mem_cons_self,jj,offP _ h zo⟩
      · obtain ⟨i,hm,hs,hd⟩ := T.exterior z (List.mem_of_mem_tail h) zo
        exact ⟨i,List.mem_cons_of_mem _ hm,hs,hd⟩

#print axioms make_track
end Graffiti189LongestPath.PosaTracks
