import RemoteSubdivisionCore
import Mathlib.Data.List.Chain

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteCycleChain
open RemoteSubdivisionCore (Marks)
variable {V I : Type*} {G : SimpleGraph V} (M : Marks G I)
variable (s : V→V→Option I)

/-- Insert a marker at each designated edge of an oriented old path. -/
def weave : List V → List (V⊕I)
  | [] => []
  | [a] => [.inl a]
  | a::b::P => .inl a :: ((s a b).toList.map Sum.inr ++ weave (b::P))

def edgeLabels : List V → List I
  | [] => []
  | [_] => []
  | a::b::P => (s a b).toList ++ edgeLabels (b::P)

theorem old_weave (a : V) : ∀ P : List V,
    (Sum.inl a : V⊕I) ∈ weave s P ↔ a∈P
  | [] => by simp [weave]
  | [_] => by simp [weave]
  | b::c::P => by
    rw [weave,List.mem_cons,List.mem_append,old_weave a (c::P), List.mem_cons]
    simp

theorem labels_weave (i : I) : ∀ P : List V,
    (Sum.inr i : V⊕I) ∈ weave s P ↔ i∈edgeLabels s P
  | [] => by simp [weave,edgeLabels]
  | [_] => by simp [weave,edgeLabels]
  | a::b::P => by
    simp only [weave,edgeLabels,List.mem_cons,Sum.inr_ne_inl,false_or,List.mem_append,
      List.mem_map,Sum.inr.injEq,exists_eq_right,labels_weave i (b::P)]

theorem length_weave : ∀ P : List V,
    (weave s P).length=P.length+(edgeLabels s P).length
  | [] => by simp [weave,edgeLabels]
  | [_] => by simp [weave,edgeLabels]
  | a::b::P => by
    simp only [weave,edgeLabels,List.length_cons,List.length_append,List.length_map,
      length_weave (b::P)]
    omega

variable (hit : ∀ {a b i}, s a b=some i → M.Pair i a b)

include hit in
theorem label_ends : ∀ {P : List V} {i : I},
    i∈edgeLabels s P → M.a i∈P ∧ M.b i∈P
  | [],_,h => by simp [edgeLabels] at h
  | [_],_,h => by simp [edgeLabels] at h
  | a::b::P,i,h => by
    simp only [edgeLabels,List.mem_append,Option.mem_toList] at h
    rcases h with h|h
    · rcases hit h with ⟨p,q⟩|⟨p,q⟩ <;> rw [←p,←q] <;> simp
    · have h := label_ends h
      exact ⟨List.mem_cons_of_mem _ h.1,List.mem_cons_of_mem _ h.2⟩

include hit in
theorem weave_nodup : ∀ {P : List V}, P.Nodup → (weave s P).Nodup
  | [],_ => by simp [weave]
  | [_],_ => by simp [weave]
  | a::b::P,nod => by
    have nh := (List.nodup_cons.mp nod).1
    have nt := weave_nodup nod.tail
    cases hs : s a b with
    | none =>
      rw [weave,hs]
      exact List.nodup_cons.mpr ⟨fun h => nh ((old_weave s a (b::P)).mp h),nt⟩
    | some i =>
      rw [weave,hs]
      change (Sum.inl a :: Sum.inr i :: weave s (b::P)).Nodup
      refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,nt⟩⟩
      · intro h
        rcases List.mem_cons.mp h with h|h
        · cases h
        · exact nh ((old_weave s a (b::P)).mp h)
      · intro h
        have g := label_ends M s hit ((labels_weave s i (b::P)).mp h)
        rcases hit hs with ⟨p,_⟩|⟨p,_⟩
        · exact nh (p.symm ▸ g.1)
        · exact nh (p.symm ▸ g.2)

theorem weave_head (a : V) (P : List V) :
    (weave s (a::P)).head?=some (.inl a) := by
  cases P <;> rfl

variable (avoid : ∀ {a b}, G.Adj a b → s a b=none → ¬M.Removed a b)

include hit avoid in
theorem weave_path : ∀ {P : List V}, P.Chain' G.Adj → (weave s P).Chain' M.expanded.Adj
  | [],_ => by simp [weave]
  | [_],_ => by simp [weave]
  | a::b::P,path => by
    obtain ⟨ab,bt⟩ := List.chain'_cons.mp path
    have rest := weave_path bt
    have start : ∀ z∈(weave s (b::P)).head?, z=Sum.inl b := by simp [weave_head]
    cases hs : s a b with
    | none =>
      rw [weave,hs]
      apply rest.cons'
      intro z h
      rw [start z h]
      exact ⟨ab,avoid ab hs⟩
    | some i =>
      rw [weave,hs]
      change (Sum.inl a :: Sum.inr i :: weave s (b::P)).Chain' M.expanded.Adj
      have ends := M.both_ends (hit hs)
      apply (rest.cons' ?_).cons'
      · intro z h
        have hz : z=Sum.inr i := by simpa [eq_comm] using h
        subst z
        exact ends.1
      · intro z h
        rw [start z h]
        exact ends.2

end KelmansCactus.AtomicBridge.RemoteCycleChain
