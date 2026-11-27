import TwoCliqueShores

open private clique_path_between join_last from TwoCliqueShores

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A spanning path of an indicated vertex set with ordered endpoints. -/
def Traverses (G : SimpleGraph V) (U : Set V) (s t : V) : Prop :=
  ∃ p : PathOn G U, p.first = s ∧ p.last = t

namespace Traverses

theorem single (x : V) : Traverses G {x} x x := by
  let p : PathOn G ({x} : Set V) :=
    ⟨[x],by simp,List.chain'_singleton _,by simp,fun _ => by simp⟩
  exact ⟨p,rfl,rfl⟩

theorem clique [Fintype V] {U : Set V} {x y : V}
    (cl : U.Pairwise G.Adj) (hx : x ∈ U) (hy : y ∈ U) (xy : x ≠ y) :
    Traverses G U x y := clique_path_between cl hx hy xy

theorem join {U W : Set V} {a b c d : V}
    (p : Traverses G U a b) (q : Traverses G W c d)
    (disjoint : Disjoint U W) (bridge : G.Adj b c) : Traverses G (U ∪ W) a d := by
  obtain ⟨P,pf,pl⟩ := p
  obtain ⟨Q,qf,ql⟩ := q
  let R := P.join Q disjoint (pl.symm ▸ qf.symm ▸ bridge)
  refine ⟨R,?_,(join_last ..).trans ql⟩
  change (P.vertices ++ Q.vertices).head _ = a
  rw [List.head_append_of_ne_nil P.nonempty]
  exact pf

theorem reverse {U : Set V} {a b : V}
    (p : Traverses G U a b) : Traverses G U b a := by
  obtain ⟨P,pf,pl⟩ := p
  let R : PathOn G U :=
    ⟨P.vertices.reverse,by simpa using P.nonempty,
      List.chain'_reverse.mpr (P.chain.imp (fun _ _ e => e.symm)),
      List.nodup_reverse.mpr P.nodup,fun v => List.mem_reverse.trans (P.covers v)⟩
  have h : R.first = b := by
    have q : R.vertices.head? = some b := by
      change P.vertices.reverse.head? = some b
      rw [List.head?_reverse,List.getLast?_eq_getLast P.nonempty]
      exact congrArg some pl
    rw [List.head?_eq_head R.nonempty] at q
    exact Option.some.inj q
  have t : R.last = a := by
    have q : R.vertices.getLast? = some a := by
      change P.vertices.reverse.getLast? = some a
      rw [List.getLast?_reverse,List.head?_eq_head P.nonempty]
      exact congrArg some pf
    rw [List.getLast?_eq_getLast R.nonempty] at q
    exact Option.some.inj q
  exact ⟨R,h,t⟩

theorem start_clique [Fintype V] {U : Set V} {x : V}
    (cl : U.Pairwise G.Adj) (hx : x ∈ U) : ∃ y ∈ U, Traverses G U x y := by
  classical
  by_cases more : ∃ y ∈ U, y ≠ x
  · obtain ⟨y,hy,yx⟩ := more
    exact ⟨y,hy,clique cl hx hy yx.symm⟩
  · have same : U = {x} := by
      ext y
      exact ⟨fun h => Classical.byContradiction (fun e => more ⟨y,h,e⟩),fun h =>
        (show y = x from h).symm ▸ hx⟩
    exact ⟨x,hx,same.symm ▸ single x⟩

theorem end_clique [Fintype V] {U : Set V} {x : V}
    (cl : U.Pairwise G.Adj) (hx : x ∈ U) : ∃ y ∈ U, Traverses G U y x := by
  obtain ⟨y,hy,p⟩ := start_clique cl hx
  exact ⟨y,hy,p.reverse⟩

/-- Attach two clique blocks through their specified bridge vertices. -/
theorem along_cliques [Fintype V] {U W : Set V} {a b c d : V}
    (leftC : U.Pairwise G.Adj) (rightC : W.Pairwise G.Adj) (dis : Disjoint U W)
    (aU : a ∈ U) (bU : b ∈ U) (cW : c ∈ W) (dW : d ∈ W)
    (leftFit : a ≠ b ∨ U = {b}) (rightFit : c ≠ d ∨ W = {c})
    (bridge : G.Adj b c) : Traverses G (U ∪ W) a d := by
  classical
  have left : Traverses G U a b := by
    rcases leftFit with ab|eq
    · exact clique leftC aU bU ab
    · have ab : a ∈ ({b} : Set V) := eq ▸ aU
      change a = b at ab
      subst a
      exact eq.symm ▸ single b
  have right : Traverses G W c d := by
    rcases rightFit with cd|eq
    · exact clique rightC cW dW cd
    · have dc : d ∈ ({c} : Set V) := eq ▸ dW
      change d = c at dc
      subst d
      exact eq.symm ▸ single c
  exact left.join right dis bridge

end Traverses

private theorem chain_of_clique_list {U : Set V} {L : List V}
    (cl : U.Pairwise G.Adj) (nd : L.Nodup) (members : ∀ v ∈ L, v ∈ U) :
    L.Chain' G.Adj := by
  apply List.Pairwise.chain'
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj lt
  apply cl (members _ (List.getElem_mem hi)) (members _ (List.getElem_mem hj))
  intro eq
  have same : L.get ⟨i,hi⟩ = L.get ⟨j,hj⟩ := eq
  have e := congrArg Fin.val ((List.nodup_iff_injective_get.mp nd) same)
  change i = j at e
  omega

/-- Add every remaining universal vertex between the first two vertices
of a path, preserving its prescribed endpoints. -/
theorem traverses_of_universal_extension [Fintype V] {U : Set V} {L : List V} {x y : V}
    (two : 2 ≤ L.length) (nd : L.Nodup) (chain : L.Chain' G.Adj)
    (head : L.head? = some x) (last : L.getLast? = some y)
    (members : ∀ v ∈ L, v ∈ U)
    (universal : ∀ v ∈ U, v ∉ L → ∀ w ∈ U, v ≠ w → G.Adj v w) :
    Traverses G U x y := by
  classical
  cases L with
  | nil => simp at two
  | cons a L =>
    cases L with
    | nil => simp at two
    | cons b T =>
      let K := a :: b :: T
      let D := ((Finset.univ : Finset V).filter fun v => v ∈ U ∧ v ∉ K).toList
      have dmem (v : V) : v ∈ D ↔ v ∈ U ∧ v ∉ K := by simp [D]
      have cl : ({v | v ∈ D} : Set V).Pairwise G.Adj := by
        intro v hv w hw hne
        exact universal v ((dmem v).mp hv).1 ((dmem v).mp hv).2 w ((dmem w).mp hw).1 hne
      have clD : D.Chain' G.Adj :=
        chain_of_clique_list cl (Finset.nodup_toList _) (fun _ e => e)
      have tail : (D ++ b :: T).Chain' G.Adj := by
        apply clD.append chain.tail
        intro u hu v hv
        have ud := (dmem u).mp (List.mem_of_getLast? (Option.mem_def.mp hu))
        have e : b = v := by simpa using hv
        subst v
        exact universal u ud.1 ud.2 b (members _ (by simp)) (fun eq => ud.2 (by simp [K,eq]))
      let P := a :: (D ++ b :: T)
      have final : P.Chain' G.Adj := by
        cases hs : D with
        | nil => simpa only [P,hs,List.nil_append] using chain
        | cons d S =>
          have sd := (dmem d).mp (by simp [hs])
          have ad := (universal d sd.1 sd.2 a (members _ (by simp))
            (fun eq => sd.2 (by simp [K,eq]))).symm
          have routed : (a :: d :: (S ++ b :: T)).Chain' G.Adj :=
            List.chain'_cons.mpr ⟨ad,by simpa only [hs,List.cons_append] using tail⟩
          simpa only [P,hs,List.cons_append] using routed
      have dn : P.Nodup := by
        apply List.nodup_cons.mpr
        refine ⟨?_,List.nodup_append.mpr ⟨Finset.nodup_toList _,(List.nodup_cons.mp nd).2,?_⟩⟩
        · intro h
          rcases List.mem_append.mp h with h|h
          · exact ((dmem _).mp h).2 (by simp [K])
          · exact (List.nodup_cons.mp nd).1 h
        · intro v hv ht
          exact ((dmem v).mp hv).2 (List.mem_cons_of_mem _ ht)
      have covers (v : V) : v ∈ P ↔ v ∈ U := by
        constructor
        · intro h
          rcases List.mem_cons.mp h with rfl|h
          · exact members _ (by simp)
          · rcases List.mem_append.mp h with h|h
            · exact ((dmem _).mp h).1
            · exact members _ (by simp [h])
        · intro h
          by_cases old : v ∈ K
          · rcases List.mem_cons.mp old with rfl|hT
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_append_right _ hT)
          · exact List.mem_cons_of_mem _ (List.mem_append_left _ ((dmem _).mpr ⟨h,old⟩))
      let path : PathOn G U := ⟨P,by simp [P],final,dn,covers⟩
      have front : path.first = x := Option.some.inj head
      have finish : path.last = y := by
        have h : path.vertices.getLast? = some y := by
          change ((a :: D) ++ b :: T).getLast? = some y
          rw [List.getLast?_append_of_ne_nil _ (by simp)]
          simpa only [List.getLast?_cons_cons] using last
        rw [List.getLast?_eq_getLast path.nonempty] at h
        exact Option.some.inj h
      exact ⟨path,front,finish⟩

#print axioms traverses_of_universal_extension

end Graffiti199Depleted.Catalogue
