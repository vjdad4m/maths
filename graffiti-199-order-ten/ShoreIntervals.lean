import TwinShoreRouting

open private reversePath from PathRepair

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V}
variable {A B : Set V} {D : Finset V}

/-- An interval spanning a side and lying strictly inside a deletion path
gives a route between two cut vertices. -/
theorem route_of_internal_shore_interval {r : V} (P : PathOn G {x | x ≠ r})
    {L M R : List V} (shape : P.vertices = L ++ M ++ R)
    (left : L ≠ []) (right : R ≠ []) (nonempty : B.Nonempty)
    (mem : ∀ v, v ∈ M ↔ v ∈ B) (boundary : ShoreBoundary G D B) :
    ∃ a ∈ D, ∃ b ∈ D, a ≠ b ∧ ShoreRoute G B a b := by
  obtain ⟨x,xB⟩ := nonempty
  have mne : M ≠ [] := fun e => List.not_mem_nil (e ▸ (mem x).mpr xB)
  let a := L.getLast left
  let b := R.head right
  let y := M.head mne
  let z := M.getLast mne
  have aL : a ∈ L := List.getLast_mem _
  have bR : b ∈ R := List.head_mem _
  have yB : y ∈ B := (mem y).mp (List.head_mem _)
  have zB : z ∈ B := (mem z).mp (List.getLast_mem _)
  have nd := P.nodup
  rw [shape] at nd
  obtain ⟨ndLM,_,disR⟩ := List.nodup_append.mp nd
  obtain ⟨_,ndM,disM⟩ := List.nodup_append.mp ndLM
  have aB : a ∉ B := fun h => disM aL ((mem _).mpr h)
  have bB : b ∉ B := fun h => disR (List.mem_append_right _ ((mem _).mpr h)) bR
  have ab : a ≠ b := fun e => disR (List.mem_append_left _ aL) (e.symm ▸ bR)
  have chain := P.chain
  rw [shape] at chain
  obtain ⟨lm,_,transitionR⟩ := List.chain'_append.mp chain
  obtain ⟨_,mChain,transitionL⟩ := List.chain'_append.mp lm
  have ay := transitionL a (List.getLast_mem_getLast? _) y (List.head_mem_head? _)
  have bz := transitionR z (by
    rw [List.getLast?_append_of_ne_nil _ mne]
    exact List.getLast_mem_getLast? _) b (List.head_mem_head? _)
  let path : PathOn G B := ⟨M,mne,mChain,ndM,mem⟩
  exact ⟨a,boundary _ yB _ aB ay.symm,b,boundary _ zB _ bB bz,ab,y,z,ay,bz,⟨path,rfl,rfl⟩⟩

private theorem in_front_iff {ListAll L R : List V} (form : ListAll = L ++ R)
    (nd : ListAll.Nodup) (i : Fin ListAll.length) : ListAll.get i ∈ L ↔ i.val < L.length := by
  subst ListAll
  change (L ++ R)[i.val] ∈ L ↔ _
  by_cases h : i.val < L.length
  · simp only [h,iff_true]
    rw [List.getElem_append_left h]
    exact List.getElem_mem _
  · simp only [h,iff_false]
    rw [List.getElem_append_right (Nat.le_of_not_gt h)]
    exact fun m => (List.nodup_append.mp nd).2.2 m (List.getElem_mem _)

variable [DecidableEq V] [Fintype V] [DecidableRel G.Adj]

/-- If one side occupies the whole start of a one-omission path and
contains no neighbor of the omitted vertex, its complement must contain
at least as many nonneighbors as neighbors of the omitted vertex. -/
theorem card_le_of_successors_in_shore_complement {r : V} (P : PathOn G {x | x ≠ r})
    (no : ¬ Traceable G) {L R : List V} (form : P.vertices = L ++ R)
    (mem : ∀ v, v ∈ L ↔ v ∈ B)
    (allOff : ∀ v, G.Adj r v → v ∉ B) (T : Finset V)
    (nonneighbors : ∀ v, v ≠ r → ¬ G.Adj r v → v ∉ B → v ∈ T) :
    (G.neighborFinset r).card ≤ T.card := by
  classical
  let N := G.neighborFinset r
  have present (v : ↥N) : ∃ i : Fin P.vertices.length, P.vertices.get i = v.val := by
    have edge := (G.mem_neighborFinset _ _).mp v.property
    apply List.mem_iff_get.mp
    exact (P.covers _).mpr edge.ne.symm
  choose place atPlace using present
  have step (v : ↥N) :
      ∃ j : Fin P.vertices.length, (place v).val + 1 = j.val ∧ P.vertices.get j ∈ T := by
    have edge := (G.mem_neighborFinset _ _).mp v.property
    have adj : G.Adj r (P.vertices.get (place v)) := by rw [atPlace]; exact edge
    obtain ⟨j,idx,_,noEdge⟩ := (path_flanks_of_nontraceable P no (place v) adj).2
    have pos : L.length ≤ (place v).val := by
      apply Nat.le_of_not_gt
      intro h
      exact allOff _ adj ((mem _).mp ((in_front_iff form P.nodup _).mpr h))
    have off : P.vertices.get j ∉ B := by
      intro h
      have before := (in_front_iff form P.nodup j).mp ((mem _).mpr h)
      omega
    exact ⟨j,idx,nonneighbors _ ((P.covers _).mp (List.get_mem _ _)) noEdge off⟩
  choose successor hstep inT using step
  let f : ↥N → ↥T := fun v => ⟨P.vertices.get (successor v),inT v⟩
  have inj : Function.Injective f := by
    intro x y eq
    have stepEq : successor x = successor y :=
      (List.nodup_iff_injective_get.mp P.nodup) (congrArg Subtype.val eq)
    have pos : place x = place y := by
      apply Fin.ext
      have hx := hstep x
      have hy := hstep y
      rw [stepEq] at hx
      omega
    exact Subtype.ext ((atPlace x).symm.trans ((congrArg P.vertices.get pos).trans (atPlace y)))
  simpa only [Fintype.card_coe,N] using Fintype.card_le_of_injective f inj

private theorem no_initial_interval_of_opposite_shore (S : ThreeVertexShore G A)
    (conn : ConnectivityAtLeast G 3) (size : D.card = 3) (degree : G.degree S.left = 3)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundary : ShoreBoundary G D A) (apart : Disjoint A B)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D)
    (P : PathOn G {x | x ≠ S.left}) (no : ¬ Traceable G) {L R : List V}
    (form : P.vertices = L ++ R) (mem : ∀ v, v ∈ L ↔ v ∈ B) : False := by
  classical
  obtain ⟨s,sD,_,ns,_⟩ := cubic_three_vertex_shore_profile S conn size offA boundary degree P no
  have middleMem : S.middle ∈ A :=
    Eq.mpr (congrArg (fun U : Set V => S.middle ∈ U) S.shape) (by simp)
  have allOff (v : V) (edge : G.Adj S.left v) : v ∉ B := by
    have h := (G.mem_neighborFinset _ _).mpr edge
    rw [ns] at h
    rcases Finset.mem_insert.mp h with e|hv
    · exact Set.disjoint_left.mp apart (e.symm ▸ middleMem)
    · exact offB v (Finset.mem_of_mem_erase hv)
  let T : Finset V := {s,S.right}
  have nonneighbors (v : V) (ne : v ≠ S.left) (noAdj : ¬ G.Adj S.left v) (vB : v ∉ B) :
      v ∈ T := by
    rcases cover v with vA|vb|vD
    · have h : v ∈ ({S.left,S.middle,S.right} : Set V) := S.shape ▸ vA
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
      rcases h with e|e|e
      · exact (ne e).elim
      · exact (noAdj (e.symm ▸ S.lm)).elim
      · simp [T,e]
    · exact (vB vb).elim
    · by_cases e : v = s
      · simp [T,e]
      · apply False.elim
        apply noAdj
        apply (G.mem_neighborFinset _ _).mp
        rw [ns]
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨e,vD⟩)
  have contra := card_le_of_successors_in_shore_complement P no form mem allOff T nonneighbors
  rw [G.card_neighborFinset_eq_degree,degree] at contra
  have upper : T.card ≤ 2 := by
    simpa only [Finset.card_singleton] using Finset.card_insert_le s ({S.right} : Finset V)
  omega

/-- If the graph remains nontraceable, the opposite shore must occupy
at least two intervals of every spanning path after deletion of the
cubic endpoint of the three-vertex path shore. -/
theorem no_single_interval_of_opposite_shore (S : ThreeVertexShore G A)
    (conn : ConnectivityAtLeast G 3) (size : D.card = 3) (degree : G.degree S.left = 3)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B)
    (apart : Disjoint A B) (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D)
    (nonempty : B.Nonempty) (P : PathOn G {x | x ≠ S.left}) (no : ¬ Traceable G) :
    ¬ ∃ L M R : List V, P.vertices = L ++ M ++ R ∧ (∀ v, v ∈ M ↔ v ∈ B) := by
  rintro ⟨L,M,R,form,mem⟩
  by_cases lnil : L = []
  · have eq : P.vertices = M ++ R := by simpa only [lnil,List.nil_append] using form
    exact no_initial_interval_of_opposite_shore S conn size degree offA offB boundA apart cover
      P no eq mem
  by_cases rnil : R = []
  · have eq : P.vertices = L ++ M := by simpa only [rnil,List.append_nil] using form
    have reverseEq : (reversePath P).vertices = M.reverse ++ L.reverse := by
      change P.vertices.reverse = _
      rw [eq,List.reverse_append]
    have reverseMem (v : V) : v ∈ M.reverse ↔ v ∈ B := by simpa only [List.mem_reverse] using mem v
    exact no_initial_interval_of_opposite_shore S conn size degree offA offB boundA apart cover
      (reversePath P) no reverseEq reverseMem
  obtain ⟨a,ha,b,hb,ab,route⟩ := route_of_internal_shore_interval P form lnil rnil nonempty mem boundB
  exact no (traceable_of_cubic_path_shore_and_route S conn size offA offB boundA apart cover
    degree P ha hb ab route)

#print axioms route_of_internal_shore_interval
#print axioms card_le_of_successors_in_shore_complement
#print axioms no_single_interval_of_opposite_shore

end Graffiti199Depleted.Catalogue
