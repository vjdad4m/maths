import RemoteCycleChainCore
import RemoteGapRunPacking

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteCycleChain
open RemoteSubdivisionCore (Marks)
open RemoteGapRunPacking (biUnion_factor run_factor)
open SquareCap (HasFactor)
variable {V I : Type*} {G : SimpleGraph V} (M : Marks G I)

/-- Select the slot label of a marked edge in either orientation. -/
noncomputable def label (a b : V) : Option I := by
  classical
  exact if h : M.Removed a b then some h.choose else none

theorem label_hit {a b i} (h : label M a b=some i) : M.Pair i a b := by
  classical
  unfold label at h
  split at h
  next h' =>
    have e := Option.some.inj h
    exact e ▸ h'.choose_spec
  next => contradiction

theorem label_none {a b} (h : label M a b=none) : ¬M.Removed a b := by
  classical
  unfold label at h
  split at h
  next => contradiction
  next x => exact x

theorem label_of_pair {a b i} (h : M.Pair i a b) : label M a b=some i := by
  classical
  unfold label
  rw [dif_pos (show M.Removed a b from ⟨i,h⟩)]
  congr 1
  exact M.slot_unique (Classical.choose_spec (show M.Removed a b from ⟨i,h⟩)) h

def Traverses (i : I) : List V→Prop
  | [] => False
  | [_] => False
  | a::b::P => M.Pair i a b ∨ Traverses i (b::P)

theorem label_iff_traverses (i : I) : ∀ P : List V,
    i∈edgeLabels (label M) P ↔ Traverses M i P
  | [] => by simp [edgeLabels,Traverses]
  | [_] => by simp [edgeLabels,Traverses]
  | a::b::P => by
    rw [edgeLabels,List.mem_append,Option.mem_toList,label_iff_traverses i (b::P),Traverses]
    exact or_congr ⟨label_hit M,label_of_pair M⟩ Iff.rfl

/-- General constructive sufficient condition: route through the marks
in disjoint core paths. Each path costs its old order plus the number of
marked edges traversed. No residual factoring oracle is needed. -/
theorem factor_of_labelled_routes [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (s : V→V→Option I)
    (hit : ∀ {a b i}, s a b=some i → M.Pair i a b)
    (avoid : ∀ {a b}, G.Adj a b → s a b=none → ¬M.Removed a b)
    (B : Finset (List V))
    (paths : ∀ P∈B,P.Nodup ∧ P.Chain' G.Adj)
    (apart : ∀ P∈B,∀ Q∈B,P≠Q→Disjoint P.toFinset Q.toFinset)
    (cover : B.biUnion List.toFinset=univ)
    (marks : ∀ i : I,∃ P∈B,i∈edgeLabels s P)
    (mod3 : ∀ P∈B,3∣P.length+(edgeLabels s P).length) :
    HasFactor M.expanded := by
  let W : List V→Finset (V⊕I) := fun P=>(weave s P).toFinset
  have factors := biUnion_factor (G:=M.expanded) B W
    (fun P pm=>run_factor _ (weave_nodup M _ hit (paths P pm).1)
      (weave_path M _ hit avoid (paths P pm).2)
      (by rw [length_weave]; exact mod3 P pm)) ?_
  · have full : B.biUnion W=univ := by
      apply eq_univ_of_forall
      rintro (a|i)
      · have ta : a∈B.biUnion List.toFinset := by simp [cover]
        obtain ⟨P,pm,am⟩:=mem_biUnion.mp ta
        exact mem_biUnion.mpr ⟨P,pm,List.mem_toFinset.mpr
          ((old_weave _ a P).mpr (List.mem_toFinset.mp am))⟩
      · obtain ⟨P,pm,mi⟩ := marks i
        exact mem_biUnion.mpr ⟨P,pm,List.mem_toFinset.mpr
          ((labels_weave _ i P).mpr mi)⟩
    rwa [full] at factors
  · intro P pm Q qm ne
    have h := disjoint_left.mp (apart P pm Q qm ne)
    apply disjoint_left.mpr
    rintro (a|i) up uq
    · exact h (List.mem_toFinset.mpr ((old_weave _ a P).mp (List.mem_toFinset.mp up)))
        (List.mem_toFinset.mpr ((old_weave _ a Q).mp (List.mem_toFinset.mp uq)))
    · have f {T : List V} (hh : Sum.inr i∈W T) : M.a i∈T.toFinset :=
        List.mem_toFinset.mpr (label_ends M _ hit
          ((labels_weave _ i T).mp (List.mem_toFinset.mp hh))).1
      exact h (f up) (f uq)

theorem factor_of_routes [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (B : Finset (List V))
    (paths : ∀ P∈B,P.Nodup ∧ P.Chain' G.Adj)
    (apart : ∀ P∈B,∀ Q∈B,P≠Q→Disjoint P.toFinset Q.toFinset)
    (cover : B.biUnion List.toFinset=univ)
    (marks : ∀ i : I,∃ P∈B,Traverses M i P)
    (mod3 : ∀ P∈B,3∣P.length+(edgeLabels (label M) P).length) :
    HasFactor M.expanded :=
  factor_of_labelled_routes M (label M) (label_hit M) (fun _ nm=>label_none M nm)
    B paths apart cover (fun i=>let ⟨P,pm,mi⟩:=marks i
      ⟨P,pm,(label_iff_traverses M i P).mpr mi⟩) mod3

/-- Last-to-first attachment relation for oriented path pieces. In the
cycle-chain application, this is the marked edge between the two cycles. -/
def Link (A B : List V) : Prop :=
  ∀ a∈A.getLast?,∀ b∈B.head?,G.Adj a b

theorem flatten_chain : ∀ {L : List (List V)},
    (∀ P∈L,P≠[] ∧ P.Chain' G.Adj) → L.Chain' (Link (G:=G)) →
    L.flatten.Chain' G.Adj
  | [],_,_ => by simp
  | [P],h,_ => by simpa using (h P (by simp)).2
  | P::Q::R,h,k => by
    have qNonempty := (h Q (by simp)).1
    have tail := flatten_chain (fun S sm=>h S (List.mem_cons_of_mem _ sm)) k.tail
    change (P++(Q::R).flatten).Chain' G.Adj
    apply ((h P (by simp)).2).append tail
    intro a am b bm
    apply (List.chain'_cons.mp k).1 a am b
    simpa [List.flatten_cons,List.head?_append,qNonempty] using
      bm

theorem flatten_nodup : ∀ {L : List (List V)},
    (∀ P∈L,P.Nodup) →
    L.Pairwise (fun A B => ∀ x∈A,x∉B) → L.flatten.Nodup
  | [],_,_ => by simp
  | P::R,h,k => by
    rw [List.flatten_cons]
    apply (h P (by simp)).append
    · exact flatten_nodup (fun S sm=>h S (List.mem_cons_of_mem _ sm)) k.tail
    · intro x xm xa
      obtain ⟨Q,qm,xq⟩:=List.mem_flatten.mp xa
      exact (List.pairwise_cons.mp k).1 Q qm x xm xq

/-- Each member of B is an oriented chain of disjoint paths. In the
unrestricted 2-factor application, the pieces are its cycles opened at
nonmarked edges. A cycle with two omitted-mark ports may be opened
between them if they are adjacent in that 2-factor. No requirement is
placed on the residue of an individual cycle or link. -/
theorem factor_of_opened_cycle_chains [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (s : V→V→Option I)
    (hit : ∀ {a b i}, s a b=some i → M.Pair i a b)
    (avoid : ∀ {a b}, G.Adj a b → s a b=none → ¬M.Removed a b)
    (B : Finset (List (List V)))
    (pieces : ∀ L∈B,∀ P∈L,P≠[] ∧ P.Nodup ∧ P.Chain' G.Adj)
    (links : ∀ L∈B,L.Chain' (Link (G:=G)))
    (inside : ∀ L∈B,L.Pairwise (fun A B => ∀ x∈A,x∉B))
    (across : ∀ L∈B,∀ R∈B,L≠R→Disjoint L.flatten.toFinset R.flatten.toFinset)
    (cover : B.biUnion (fun L=>L.flatten.toFinset)=univ)
    (marks : ∀ i : I,∃ L∈B,i∈edgeLabels s L.flatten)
    (mod3 : ∀ L∈B,3∣L.flatten.length+(edgeLabels s L.flatten).length) :
    HasFactor M.expanded := by
  apply factor_of_labelled_routes M s hit avoid (B.image List.flatten)
  · intro P pm
    obtain ⟨L,lm,rfl⟩:=mem_image.mp pm
    exact ⟨flatten_nodup (fun Q qm=>(pieces L lm Q qm).2.1) (inside L lm),
      flatten_chain (fun Q qm=>⟨(pieces L lm Q qm).1,(pieces L lm Q qm).2.2⟩) (links L lm)⟩
  · intro P pm Q qm ne
    obtain ⟨L,lm,rfl⟩:=mem_image.mp pm
    obtain ⟨R,rm,rfl⟩:=mem_image.mp qm
    exact across L lm R rm (fun eq=>ne (congrArg List.flatten eq))
  · apply eq_univ_of_forall
    intro x
    have m : x∈B.biUnion (fun L=>L.flatten.toFinset) := by rw [cover]; exact mem_univ _
    obtain ⟨L,lm,xm⟩:=mem_biUnion.mp m
    exact mem_biUnion.mpr ⟨L.flatten,mem_image.mpr ⟨L,lm,rfl⟩,xm⟩
  · intro i
    obtain ⟨L,lm,hi⟩:=marks i
    exact ⟨L.flatten,mem_image.mpr ⟨L,lm,rfl⟩,hi⟩
  · intro P pm
    obtain ⟨L,lm,rfl⟩:=mem_image.mp pm
    exact mod3 L lm

#print axioms factor_of_opened_cycle_chains
#print axioms factor_of_routes
#print axioms flatten_chain
#print axioms flatten_nodup
end KelmansCactus.AtomicBridge.RemoteCycleChain
