import PartialRows
import FlankAttachment

open private pred_mem succ_mem from CompactOmission
open private three_names_exhaust_neighbors from DepletedFootprint

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph

structure Layout (n : ℕ) where
  port : Fin 3 ↪ Fin (n+1)
  interior : ∀ m, 0 < (port m).val ∧ (port m).val + 1 < n

def Layout.prev {n : ℕ} (b : Layout n) (i : Fin 3) : Fin (n+1) :=
  ⟨(b.port i).val - 1, by have h := b.interior i; omega⟩

def Layout.next {n : ℕ} (b : Layout n) (i : Fin 3) : Fin (n+1) :=
  ⟨(b.port i).val + 1, by have h := b.interior i; omega⟩

def Layout.ports {n : ℕ} (b : Layout n) : List (Fin (n+1)) := List.ofFn b.port
def Layout.lefts {n : ℕ} (b : Layout n) : List (Fin (n+1)) := List.ofFn b.prev
def Layout.rights {n : ℕ} (b : Layout n) : List (Fin (n+1)) := List.ofFn b.next
def Layout.mateContacts {n : ℕ} (b : Layout n) (m : Fin 3) : List (Fin (n+1)) :=
  [Fin.last n,b.prev m,b.next m]

variable {V : Type*} {G : SimpleGraph V}

def block {n : ℕ} (f : Fin (n+1) ↪ V) : List V :=
  (List.finRange n).map (fun i => f i.castSucc)

@[simp] theorem block_length {n : ℕ} (f : Fin (n+1) ↪ V) : (block f).length = n := by
  simp [block]

theorem block_get {n : ℕ} (f : Fin (n+1) ↪ V) (i : Fin (n+1)) (hi : i.val < n) :
    (block f)[i.val]'(by simpa using hi) = f i := by
  simp [block]

theorem block_cases {n : ℕ} (f : Fin (n+1) ↪ V) (i : Fin (n+1)) :
    f i ∈ block f ∨ i = Fin.last n := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact Or.inr rfl
  · exact Or.inl (List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩)

theorem block_perm {n : ℕ} (f : Fin (n+1) ↪ V) {P : List (Fin (n+1))}
    (h : P.Perm (List.finRange (n+1))) :
    (P.map f).Perm (f (Fin.last n) :: block f) := by
  have ee : (List.finRange (n+1)).map (f : Fin (n+1) → V) = block f ++ [f (Fin.last n)] := by
    rw [List.finRange_succ_last]
    simp [block,Function.comp_def]
  exact (ee ▸ h.map f).trans (by simpa only [List.append_nil] using
    (List.perm_middle (a := f (Fin.last n)) (l₁ := block f) (l₂ := [])))

theorem split_block_edge {n : ℕ} {f : Fin (n+1) ↪ V} (p : PathOn G {v | v ≠ f (Fin.last n)})
    {L R : List V} (split : p.vertices = L ++ block f ++ R)
    {i j : Fin (n+1)} (step : i.val + 1 = j.val) (hj : j.val < n) :
    p.vertices = (L ++ (block f).take i.val) ++ f i :: f j :: ((block f).drop (j.val+1) ++ R) := by
  have hi : i.val < n := by omega
  have h1 : i.val < (block f).length := by simpa using hi
  have h2 : j.val < (block f).length := by simpa using hj
  have mp : block f = (block f).take i.val ++ f i :: f j :: (block f).drop (j.val+1) := by
    calc
      block f = (block f).take i.val ++ (block f).drop i.val :=
        (List.take_append_drop i.val (block f)).symm
      _ = _ := by
        rw [List.drop_eq_getElem_cons h1,step,List.drop_eq_getElem_cons h2,
          block_get f i hi,block_get f j hj]
  conv_lhs => rw [split]
  nth_rw 1 [mp]
  simp only [List.append_assoc,List.cons_append]

theorem block_edge {n : ℕ} {f : Fin (n+1) ↪ V} (p : PathOn G {v | v ≠ f (Fin.last n)})
    {L R : List V} (split : p.vertices = L ++ block f ++ R)
    {i j : Fin (n+1)} (step : i.val + 1 = j.val) (hj : j.val < n) : G.Adj (f i) (f j) :=
  (List.chain'_cons.mp ((split_block_edge p split step hj ▸ p.chain).right_of_append)).1

structure Placement {n : ℕ} (G : SimpleGraph V) (f : Fin (n+1) ↪ V) (b : Layout n)
    (m : Fin 3) : Prop where
  consecutive : ∀ i j : Fin (n+1), i.val+1 = j.val → j.val < n → G.Adj (f i) (f j)
  omission : ∀ i, G.Adj (f (Fin.last n)) (f i) ↔ i ∈ b.ports
  portOff : ∀ i ∈ b.ports, ∀ j ∈ b.ports, ¬ G.Adj (f i) (f j)
  leftOff : ∀ i ∈ b.lefts, ∀ j ∈ b.lefts, ¬ G.Adj (f i) (f j)
  rightOff : ∀ i ∈ b.rights, ∀ j ∈ b.rights, ¬ G.Adj (f i) (f j)
  mate : ∀ i, G.Adj (f (b.port m)) (f i) → i ∈ b.mateContacts m

variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

theorem placement {n : ℕ} {f : Fin (n+1) ↪ V} (b : Layout n) (m : Fin 3)
    (p : PathOn G {v | v ≠ f (Fin.last n)}) {L R : List V} (split : p.vertices = L ++ block f ++ R)
    (noTrace : ¬ Catalogue.Traceable G)
    (za : ∀ i, G.Adj (f (Fin.last n)) (f (b.port i)))
    (ind : ∀ i j, ¬ G.Adj (f (b.port i)) (f (b.port j)))
    (dz : G.degree (f (Fin.last n)) = 3) (dm : G.degree (f (b.port m)) = 3) :
    Placement G f b m := by
  have zNe (a b' : Fin 3) (h : a ≠ b') : b.port a ≠ b.port b' := b.port.injective.ne h
  have lt (i : Fin 3) : (b.port i).val < n := by have h := b.interior i; omega
  have step (i : Fin 3) : (b.prev i).val + 1 = (b.port i).val := by
    have h := b.interior i
    change (b.port i).val - 1 + 1 = _
    omega
  have ls (i : Fin 3) : f (b.prev i) ∈ p.predecessors :=
    pred_mem (split_block_edge p split (step i) (lt i)) (za i)
  have rs (i : Fin 3) : f (b.next i) ∈ p.rev.predecessors :=
    succ_mem (split_block_edge p split rfl (b.interior i).2) (za i)
  constructor
  · intro i j step lt
    exact block_edge p split step lt
  · intro i
    constructor
    · intro h
      obtain ⟨v,hv,eq⟩ := three_names_exhaust_neighbors f
        (zNe 0 1 (by decide)) (zNe 0 2 (by decide)) (zNe 1 2 (by decide)) dz
        (za 0) (za 1) (za 2) _ h
      have enum : b.ports = [b.port 0,b.port 1,b.port 2] := rfl
      exact (f.injective eq) ▸ (enum.symm ▸ hv)
    · intro h
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
      exact za j
  · intro i hi j hj
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hi
    obtain ⟨c,rfl⟩ := List.mem_ofFn.mp hj
    exact ind a c
  · intro i hi j hj
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hi
    obtain ⟨c,rfl⟩ := List.mem_ofFn.mp hj
    exact p.terminalFlanks_independent noTrace _ (Finset.mem_insert_of_mem (ls a)) _
      (Finset.mem_insert_of_mem (ls c))
  · intro i hi j hj
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hi
    obtain ⟨c,rfl⟩ := List.mem_ofFn.mp hj
    exact p.rev.terminalFlanks_independent noTrace _ (Finset.mem_insert_of_mem (rs a)) _
      (Finset.mem_insert_of_mem (rs c))
  · intro i h
    have offL : (Fin.last n : Fin (n+1)) ≠ b.prev m := by
      have h := b.interior m
      intro he
      have e := congrArg Fin.val he
      change n = (b.port m).val - 1 at e
      omega
    have offR : (Fin.last n : Fin (n+1)) ≠ b.next m := by
      have h := b.interior m
      intro he
      have e := congrArg Fin.val he
      change n = (b.port m).val + 1 at e
      omega
    have dis : b.prev m ≠ b.next m := by
      intro he
      have e := congrArg Fin.val he
      change (b.port m).val - 1 = (b.port m).val + 1 at e
      omega
    obtain ⟨j,hj,eq⟩ := three_names_exhaust_neighbors f offL offR dis dm
      (za m).symm (block_edge p split (step m) (lt m)).symm
      (block_edge p split rfl (b.interior m).2) _ h
    exact (f.injective eq) ▸ hj

end Graffiti199Depleted.WiderOmission
