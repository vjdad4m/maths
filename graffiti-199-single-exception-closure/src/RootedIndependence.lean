import PinnedFlanks
namespace Graffiti199Depleted.Catalogue.Anchored
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} [Fintype V]

private theorem exists_longest (d : V) : ∃ S : Finset V, ∃ P : PathOn G (↑S : Set V),
    P.last = d ∧ Longest G P := by
  classical
  let fam := (Finset.univ : Finset (Finset V)).filter fun (T : Finset V) => ∃ p : PathOn G (↑T : Set V), p.last = d
  have mem (T : Finset V) : T ∈ fam ↔ ∃ p : PathOn G (↑T : Set V), p.last = d := by simp [fam]
  obtain ⟨s,_,se⟩ := Traverses.single (G := G) d
  have one : ({d} : Finset V) ∈ fam := (mem {d}).mpr (by rw [Finset.coe_singleton]; exact ⟨s,se⟩)
  obtain ⟨S,hS,mx⟩ := fam.exists_max_image Finset.card ⟨_,one⟩
  obtain ⟨P,pd⟩ := (mem S).mp hS
  refine ⟨S,P,pd,?_⟩
  intro L nd chain last
  have ne : L ≠ [] := fun e => by simp [e] at last
  let R : PathOn G (↑L.toFinset : Set V) := ⟨L,ne,chain,nd,fun v => by simp⟩
  have rd : R.last = d := Option.some.inj ((List.getLast?_eq_getLast ne).symm.trans (last.trans (congrArg some pd)))
  have h := mx _ ((mem _).mpr ⟨R,rd⟩)
  have eq : P.vertices.toFinset = S := by ext v; simpa only [List.mem_toFinset] using P.covers v
  rw [List.toFinset_card_of_nodup nd,← eq,List.toFinset_card_of_nodup P.nodup] at h
  exact h

private theorem boundary_lower {S : Finset V} {C : Set V} [DecidablePred (Touch G C)] (P : PathOn G (↑S : Set V)) (long : Longest G P)
    {k : ℕ} (conn : ConnectivityAtLeast G k) (off : Disjoint (↑S : Set V) C) (nz : C.Nonempty)
    (bd : ShoreBoundary G S C) : k ≤ (S.filter (Touch G C)).card := by
  classical
  let T := S.filter (Touch G C)
  by_contra! lt
  obtain ⟨b,hb⟩ := nz
  have bOff : b ∉ T := fun h => Set.disjoint_left.mp off (Finset.mem_filter.mp h).1 hb
  have firstU := (P.covers P.first).mp (List.head_mem P.nonempty)
  have firstOff : P.first ∉ T := by
    rintro h
    obtain ⟨w,wC,e⟩ := (Finset.mem_filter.mp h).2
    exact first_avoids P long (fun hU => Set.disjoint_left.mp off hU wC) e.symm
  obtain ⟨walk⟩ := (conn.2 T lt).preconnected ⟨b,bOff⟩ ⟨P.first,firstOff⟩
  obtain ⟨u,hu,v,hv,uv⟩ := crossingOnWalk (U := {i : Survives T | i.val ∈ C}) walk hb
    (Set.disjoint_left.mp off firstU)
  exact v.property (Finset.mem_filter.mpr ⟨bd u.val hu v.val hv uv,⟨u.val,hu,uv.symm⟩⟩)

/-- If a longest path ending at d omits a component, its attachment
predecessors and a vertex of the component form an independent set away from d. -/
theorem large_independent_of_omission (d : V) {k : ℕ} (conn : ConnectivityAtLeast G k)
    (S : Finset V) (P : PathOn G (↑S : Set V)) (pd : P.last = d) (long : Longest G P) {b : V} (bs : b ∉ S) :
    ∃ W : Finset V, k < W.card ∧ d ∉ W ∧ (∀ u ∈ W, ∀ v ∈ W, ¬ G.Adj u v) := by
  classical
  let B := (DeletionGraph G S).connectedComponentMk (⟨b,bs⟩ : Survives S)
  let C := componentShore S B
  have bC : b ∈ C := ⟨⟨b,bs⟩,rfl,rfl⟩
  have off : Disjoint (↑S : Set V) C := Set.disjoint_left.mpr (componentShore_off_cut S B)
  have con := (componentShore_connected S B).preconnected
  let I := (Finset.univ : Finset (Slot P)).filter fun i => Touch G C (P.after i)
  let f : Slot P ↪ V := ⟨P.before,fun _ _ h => Fin.ext (P.nodup.getElem_inj_iff.mp h)⟩
  let g : Slot P ↪ V := ⟨P.after,by
    intro i j h
    have e : i.val + 1 = j.val + 1 := P.nodup.getElem_inj_iff.mp h
    exact Fin.ext (by omega)⟩
  let W := I.map f
  have eq : I.map g = S.filter (Touch G C) := by
    ext v
    simp only [I,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map,g,Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨i,t,rfl⟩; exact ⟨(P.covers _).mp (List.getElem_mem _),t⟩
    · rintro ⟨vS,t⟩
      obtain ⟨i,e⟩ := slot_of_contact P long off vS t
      exact ⟨i,e.symm ▸ t,e⟩
  have count := boundary_lower P long conn off ⟨b,bC⟩ (componentShore_boundary S B)
  rw [← eq,Finset.card_map] at count
  have mem {v : V} : v ∈ W ↔ ∃ i : Slot P, Touch G C (P.after i) ∧ P.before i = v := by simp [W,I,f]
  have bw : b ∉ W := by
    rintro h
    obtain ⟨i,_,e⟩ := mem.mp h
    exact bs (e ▸ (P.covers _).mp (List.getElem_mem _))
  have db : d ≠ b := fun e => bs (e ▸ pd ▸ P.last_mem)
  refine ⟨insert b W,?_,?_,?_⟩
  · rw [Finset.card_insert_of_not_mem bw,Finset.card_map]; omega
  · intro h
    rcases Finset.mem_insert.mp h with e|w
    · contradiction
    · obtain ⟨i,_,e⟩ := mem.mp w
      exact before_not_end P i (e.trans pd.symm)
  · intro u hu v hv
    rcases Finset.mem_insert.mp hu with rfl|uw <;> rcases Finset.mem_insert.mp hv with rfl|vw
    · exact G.loopless _
    · obtain ⟨j,t,rfl⟩ := mem.mp vw
      exact fun e => before_off P long con off j t ⟨_,bC,e.symm⟩
    · obtain ⟨i,t,rfl⟩ := mem.mp uw
      exact fun e => before_off P long con off i t ⟨_,bC,e⟩
    · obtain ⟨i,hi,rfl⟩ := mem.mp uw
      obtain ⟨j,hj,rfl⟩ := mem.mp vw
      exact before_stable P long con off i j hi hj

/-- Rooted Chvátal–Erdős path criterion. Independence is bounded only
on sets avoiding the prescribed endpoint. -/
theorem spanning_path_from_root (d : V) {k : ℕ} (conn : ConnectivityAtLeast G k)
    (cap : ∀ W : Finset V, d ∉ W → (∀ u ∈ W, ∀ v ∈ W, ¬ G.Adj u v) → W.card ≤ k) :
    ∃ e : V, Traverses G Set.univ d e := by
  classical
  obtain ⟨S,P,pd,long⟩ := exists_longest (G := G) d
  have full : (↑S : Set V) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro b
    by_contra bs
    obtain ⟨W,large,off,stable⟩ := large_independent_of_omission d conn S P pd long bs
    exact (Nat.not_lt_of_ge (cap W off stable)) large
  have t : Traverses G (↑S : Set V) P.first d := ⟨P,rfl,pd⟩
  exact ⟨P.first,full ▸ t.reverse⟩

#print axioms large_independent_of_omission
#print axioms spanning_path_from_root
end Graffiti199Depleted.Catalogue.Anchored


