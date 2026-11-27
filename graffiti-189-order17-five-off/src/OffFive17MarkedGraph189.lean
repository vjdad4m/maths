import OffFive17CentralTransfers189
import OffFive17MarkedCoreBase189
import DisconnectedSingleGraphVerified

namespace OffFive17MarkedCore
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.TwoCut
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

variable {W : Type*} (D : SimpleGraph W) [Fintype W] [DecidableEq W] [DecidableRel D.Adj]

private def graphMask (e : Fin 5 ≃ W) : List Bool :=
  pairs.map fun z => decide (D.Adj (e (Fin.ofNat' 5 z.1)) (e (Fin.ofNat' 5 z.2)))

private theorem edge_exact (e : Fin 5 ≃ W) (u v : V) :
    edge (graphMask D e) u v=true ↔ D.Adj (e u) (e v) := by
  have basic {u v : Fin 5} (lt : u.val<v.val) :
      bit (graphMask D e) u.val v.val=true ↔ D.Adj (e u) (e v) := by
    have a := u.isLt
    have b := v.isLt
    have mem : (u.val,v.val)∈pairs := by
      simp only [pairs,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq]
      omega
    have u' : Fin.ofNat' 5 u.val=u := Fin.ext (Nat.mod_eq_of_lt u.isLt)
    have v' : Fin.ofNat' 5 v.val=v := Fin.ext (Nat.mod_eq_of_lt v.isLt)
    unfold bit graphMask
    have lookup (a b : ℕ) (p : (a,b)∈pairs) :
        pairs[pairs.idxOf (a,b)]?=some (a,b) := by
      simp only [pairs,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at p
      rcases p with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|
        ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
    rw [List.getElem?_map,lookup _ _ mem]
    change decide (D.Adj (e (Fin.ofNat' 5 u.val)) (e (Fin.ofNat' 5 v.val)))=true ↔ _
    rw [u',v']
    exact ⟨of_decide_eq_true,decide_eq_true⟩
  by_cases a : u.val<v.val
  · simpa only [edge,if_pos a] using basic a
  by_cases b : v.val<u.val
  · exact (by simpa only [edge,if_neg a,if_pos b] using basic (u:=v) (v:=u) b :
      edge (graphMask D e) u v=true ↔ D.Adj (e v) (e u)).trans (D.adj_comm _ _)
  have e' : u=v := Fin.ext (by omega)
  subst v
  simp [edge,D.loopless]

private theorem degree_exact (e : Fin 5 ≃ W) (u : V) :
    degree (graphMask D e) u=D.degree (e u) := by
  let L := (List.finRange 5).filter (edge (graphMask D e) u)
  have incl : L.toFinset.image e=D.neighborFinset (e u) := by
    ext v
    simp only [mem_image,mem_neighborFinset,List.mem_toFinset,L,List.mem_filter]
    constructor
    · rintro ⟨i,⟨_,adj⟩,rfl⟩
      exact (edge_exact D e u i).mp adj
    · intro adj
      obtain ⟨k,rfl⟩ := e.surjective v
      exact ⟨k,⟨List.mem_finRange k,(edge_exact D e u k).mpr adj⟩,rfl⟩
  have h := congrArg Finset.card incl
  rw [card_image_of_injective _ e.injective,
    List.toFinset_card_of_nodup ((List.nodup_finRange 5).filter _),
    card_neighborFinset_eq_degree] at h
  exact h

private theorem mk_core_path_of_list (e : Fin 5 ≃ W) (c : W→Fin 3) (l : List V)
    (cl : accepted (List.ofFn (fun k=>(c (e k)).val)) (graphMask D e) l) :
    ∃ s t,∃ q : D.Walk s t, c s=1 ∧ c t=2 ∧ q.IsPath ∧ 4 ≤ q.length := by
  have col (i : Fin 5) : color (List.ofFn (fun k=>(c (e k)).val)) i=(c (e i)).val := by
    fin_cases i <;> rfl
  obtain ⟨ll,nd,l1,l2,chain⟩ := cl
  rcases l with _|⟨a,l⟩
  · simp at ll
  rcases l with _|⟨b,l⟩
  · simp at ll
  rcases l with _|⟨d,l⟩
  · simp at ll
  rcases l with _|⟨f,l⟩
  · simp at ll
  rcases l with _|⟨z,l⟩
  · simp at ll
  have emp : l=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at ll; omega)
  subst l
  change color _ a=1 at l1
  change color _ z=2 at l2
  rw [col] at l1 l2
  simp only [List.chain'_cons,List.chain'_singleton,and_true] at chain
  have ab := (edge_exact D e a b).mp chain.1
  have bd := (edge_exact D e b d).mp chain.2.1
  have df := (edge_exact D e d f).mp chain.2.2.1
  have fz := (edge_exact D e f z).mp chain.2.2.2
  let q : D.Walk (e a) (e z) := .cons ab (.cons bd (.cons df (.cons fz .nil)))
  refine ⟨_,_,q,Fin.ext l1,Fin.ext l2,IsPath.mk' ?_,by simp [q]⟩
  exact nd.map e.injective

theorem marked_core_of_table
    (table : ∀ P∈colorTuples,row P=true)
    (m : W→Fin 3) (card : Fintype.card W=5)
    (c1 : ∃ x,m x=1) (c2 : ∃ x,m x=2)
    (mind : ∀ x,2 ≤ CoreTotalDegree17 D m x)
    (wide : ∀ x y,x≠y → 4 ≤ CoreTotalDegree17 D m x ∨ 4 ≤ CoreTotalDegree17 D m y)
    (no : ∀ x y,m x≠0 → m y≠0 → m x≠m y → D.neighborFinset x≠{y}) :
    ∃ s t,∃ q : D.Walk s t, m s=1 ∧ m t=2 ∧ q.IsPath ∧ 4 ≤ q.length := by
  classical
  let f : Fin 5 ≃ W := (Fintype.equivFinOfCardEq card).symm
  obtain ⟨σ,mono⟩ := Graffiti189LongestPath.TwoCut.SmallOrderFour.exists_mono_perm_fin
    (fun i=> (m (f i)).val)
  let e : Fin 5 ≃ W := σ.trans f
  let P := List.ofFn (fun i=>(m (e i)).val)
  let M := graphMask D e
  have pn : P.length=5 := by simp [P]
  have all (k : ℕ) (km : k∈P) : k=0 ∨ k∈([1,2]:List ℕ) := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp km
    have h := (m (e i)).isLt
    simp only [List.mem_cons,List.mem_nil_iff,or_false]
    omega
  have monoP : P.Pairwise (·≤·) := List.pairwise_ofFn.mpr (fun _ _ h=>mono h.le)
  have full (k : ℕ) (km : k∈([1,2]:List ℕ)) : k∈P := by
    have ks : k=1 ∨ k=2 := by simpa using km
    rcases ks with rfl|rfl
    · obtain ⟨x,x1⟩ := c1
      obtain ⟨i,rfl⟩ := e.surjective x
      exact List.mem_ofFn.mpr ⟨i,congrArg Fin.val x1⟩
    · obtain ⟨x,x2⟩ := c2
      obtain ⟨i,rfl⟩ := e.surjective x
      exact List.mem_ofFn.mpr ⟨i,congrArg Fin.val x2⟩
  have rowP := table P (mem_tuples pn all monoP full)
  have ml : M.length=10 := by simp [M,graphMask,pairs]
  have col (i : Fin 5) : color P i=(m (e i)).val := by fin_cases i <;> rfl
  have tot (i : Fin 5) : total P M i=CoreTotalDegree17 D m (e i) := by
    unfold total CoreTotalDegree17
    rw [col,degree_exact D e i]
    have eq : (m (e i)).val=0 ↔ m (e i)=0 := ⟨fun h=>Fin.ext h,fun h=>congrArg Fin.val h⟩
    simp [eq]
  have okMin : (List.finRange 5).all (fun i=>decide (2 ≤ total P M i))=true := by
    apply List.all_eq_true.mpr
    intro i _
    apply decide_eq_true
    rw [tot i]
    exact mind (e i)
  have okLow : ((List.finRange 5).filter (fun i=>decide (total P M i<4))).length ≤ 1 := by
    let A := (List.finRange 5).filter (fun i=>decide (total P M i<4))
    have nd : A.Nodup := (List.nodup_finRange 5).filter _
    change A.length ≤ 1
    rw [← List.toFinset_card_of_nodup nd]
    apply Nat.le_of_not_gt
    intro more
    obtain ⟨u,um,v,vm,uv⟩ := one_lt_card.mp more
    have ul := of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp um)).2
    have vl := of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp vm)).2
    change total P M u<4 at ul
    change total P M v<4 at vl
    rw [tot u] at ul
    rw [tot v] at vl
    exact (wide (e u) (e v) (fun h=>uv (e.injective h))).elim
      (fun h=>Nat.not_lt_of_ge h ul) (fun h=>Nat.not_lt_of_ge h vl)
  have okLeaf : noLeaf P M=true := by
    apply List.all_eq_true.mpr
    intro u _
    apply List.all_eq_true.mpr
    intro v _
    by_cases poss : unusualLeaf P M u v
    · exfalso
      obtain ⟨u0,v0,uv,adj,deg⟩ := poss
      have au : m (e u)≠0 := fun h=>u0 ((col u).trans (congrArg Fin.val h))
      have av : m (e v)≠0 := fun h=>v0 ((col v).trans (congrArg Fin.val h))
      have auv : m (e u)≠m (e v) := fun h=>uv ((col u).trans ((congrArg Fin.val h).trans (col v).symm))
      have cardU : (D.neighborFinset (e u)).card=1 := by
        rwa [card_neighborFinset_eq_degree,←degree_exact D e u]
      obtain ⟨z,zf⟩ := card_eq_one.mp cardU
      have vm : e v∈D.neighborFinset (e u) := (mem_neighborFinset _ _ _).mpr ((edge_exact D e u v).mp adj)
      have vz : e v=z := mem_singleton.mp (zf ▸ vm)
      exact no (e u) (e v) au av auv (vz.symm ▸ zf)
    · simp [poss]
  have guarded : guard P M=true := by simp [guard,okMin,okLow,okLeaf]
  obtain ⟨l,lp⟩ := row_sound rowP ml guarded
  exact mk_core_path_of_list D e m l lp

#print axioms marked_core_of_table
end OffFive17MarkedCore
