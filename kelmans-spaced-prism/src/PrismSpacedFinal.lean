import RemoteSpacedPrismLayout
import SquareCapFactor

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.PrismSpacedFinal
open RemoteSpacedPrismLayout
open SquareCap (IsTile HasFactor)

private abbrev Port := (Bool ⊕ Bool) ⊕ Bool
private abbrev V (k : Nat) := Core k ⊕ Port
private abbrev Blocks (k : Nat) := Fin 6 × Fin k × Bool
private abbrev Index (k : Nat) := Port ⊕ Blocks k

private theorem gap_pos (k : Nat) : 0 < gap k := by simp [gap]

private def column (k : Nat) (b : Blocks k) (i : Fin 3) : Fin (columns k) :=
  ⟨b.1.val * gap k + (3*b.2.1.val+1+i.val),by
    have lt : 3*b.2.1.val+1+i.val < gap k := by
      have h := b.2.1.isLt
      have t := i.isLt
      unfold gap
      omega
    have h1 : b.1.val*gap k + (3*b.2.1.val+1+i.val) < (b.1.val+1)*gap k := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have h2 : (b.1.val+1)*gap k ≤ columns k := by
      unfold columns
      apply Nat.mul_le_mul_right
      have z := b.1.isLt
      omega
    exact h1.trans_le h2⟩

private def vertex (k : Nat) (b : Blocks k) (i : Fin 3) : V k :=
  Sum.inl (column k b i,b.2.2)

private theorem vertices_inj (k : Nat) (b : Blocks k) : Function.Injective (vertex k b) := by
  intro i j eq
  have h := congrArg (fun v : Core k => v.1.val) (Sum.inl.inj eq)
  change b.1.val*gap k+(3*b.2.1.val+1+i.val) =
    b.1.val*gap k+(3*b.2.1.val+1+j.val) at h
  exact Fin.ext (by omega)

private def shapes (k : Nat) : Index k → Finset (V k)
  | Sum.inl p => {Sum.inl (markCol k p,false),Sum.inr p,Sum.inl (markCol k p,true)}
  | Sum.inr b => {vertex k b 0,vertex k b 1,vertex k b 2}

private theorem triangle_tile {T : Type*} [DecidableEq T] {G : SimpleGraph T} {x y z : T}
    (xy : G.Adj x y) (yz : G.Adj y z) (xz : x≠z) : IsTile G {x,y,z} := by
  refine ⟨by simp [card_insert_of_not_mem,xy.ne,yz.ne,xz],y,by simp,?_⟩
  intro w hw ne
  simp only [mem_insert,mem_singleton] at hw
  rcases hw with rfl|rfl|rfl
  · exact xy.symm
  · exact (ne rfl).elim
  · exact yz

private theorem shape_tile (k : Nat) (b : Index k) : IsTile (board k) (shapes k b) := by
  cases b with
  | inl p =>
    exact triangle_tile (slot_adj k p false).symm (slot_adj k p true)
      (fun e => (by decide : false≠true) (congrArg Prod.snd (Sum.inl.inj e)))
  | inr b =>
    apply triangle_tile
    · exact row_adj k (a:=column k b 0) (b:=column k b 1) (by
        change b.1.val*gap k+(3*b.2.1.val+1+0)+1 =
          b.1.val*gap k+(3*b.2.1.val+1+1)
        omega) b.2.2
    · exact row_adj k (a:=column k b 1) (b:=column k b 2) (by
        change b.1.val*gap k+(3*b.2.1.val+1+1)+1 =
          b.1.val*gap k+(3*b.2.1.val+1+2)
        omega) b.2.2
    · exact fun h => (by decide : (0:Fin 3)≠2) (vertices_inj k b h)

private abbrev Key := Nat × Nat × Bool
private def vKey (k : Nat) : V k → Key
  | .inr p => (index p,0,false)
  | .inl (i,b) => let q := i.val / gap k; let m := i.val % gap k
                  if m=0 then (q,0,false) else (q,(m-1)/3+1,b)
private def iKey (k : Nat) : Index k → Key
  | .inl p => (index p,0,false)
  | .inr b => (b.1.val,b.2.1.val+1,b.2.2)

private theorem iKey_inj (k : Nat) : Function.Injective (iKey k) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (index_injective (congrArg Prod.fst h))
    | inr b =>
      have e := congrArg (Prod.fst ∘ Prod.snd) h
      change 0 = b.2.1.val+1 at e
      omega
  | inr a =>
    cases b with
    | inl b =>
      have e := congrArg (Prod.fst ∘ Prod.snd) h
      change a.2.1.val+1=0 at e
      omega
    | inr b =>
      have fst : a.1=b.1 := Fin.ext (congrArg Prod.fst h)
      have mid := congrArg (Prod.fst ∘ Prod.snd) h
      change a.2.1.val+1=b.2.1.val+1 at mid
      have last : a.2.2=b.2.2 := congrArg (fun x : Key => x.2.2) h
      exact congrArg Sum.inr (Prod.ext fst (Prod.ext (Fin.ext (by omega)) last))

private theorem mark_key (k : Nat) (p : Port) (r : Bool) :
    vKey k (Sum.inl (markCol k p,r)) = iKey k (Sum.inl p) := by
  change (if index p*gap k % gap k=0 then (index p*gap k / gap k,0,false)
    else _) = _
  simp [Nat.mul_div_cancel _ (gap_pos k),iKey]

private theorem segment_key (k : Nat) (b : Blocks k) (d : Fin 3) :
    vKey k (vertex k b d) = iKey k (Sum.inr b) := by
  let m := 3*b.2.1.val+1+d.val
  have ml : m < gap k := by
    have hi := b.2.1.isLt
    have hd := d.isLt
    unfold m gap; omega
  have mn : m ≠ 0 := by unfold m; omega
  have div : (b.1.val*gap k+m)/gap k = b.1.val := by
    rw [Nat.mul_comm b.1.val, Nat.mul_add_div (gap_pos k)]
    simp [Nat.div_eq_of_lt ml]
  have modv : (b.1.val*gap k+m)%gap k = m := by
    rw [Nat.mul_comm b.1.val,Nat.mul_add_mod,Nat.mod_eq_of_lt ml]
  have sub : (m-1)/3=b.2.1.val := by
    have hd := d.isLt
    unfold m
    omega
  unfold vKey vertex
  change (if (b.1.val*gap k+m)%gap k=0 then ((b.1.val*gap k+m)/gap k,0,false)
    else ((b.1.val*gap k+m)/gap k,(((b.1.val*gap k+m)%gap k)-1)/3+1,b.2.2)) = _
  simp [modv,div,mn,sub,iKey]

private theorem key_of_member {k : Nat} {b : Index k} {v : V k}
     (hv : v ∈ shapes k b) : vKey k v = iKey k b := by
  cases b with
  | inl p =>
    simp only [shapes,mem_insert,mem_singleton] at hv
    rcases hv with rfl|rfl|rfl
    · exact mark_key k p false
    · rfl
    · exact mark_key k p true
  | inr b =>
    simp only [shapes,mem_insert,mem_singleton] at hv
    rcases hv with rfl|rfl|rfl
    · exact segment_key k b 0
    · exact segment_key k b 1
    · exact segment_key k b 2

private theorem member_some (k : Nat) (v : V k) : ∃ t : Index k,v ∈ shapes k t := by
  cases v with
  | inr p => exact ⟨.inl p,by simp [shapes]⟩
  | inl u =>
    obtain ⟨i,r⟩ := u
    let s : Fin 6 := ⟨i.val/gap k,(Nat.div_lt_iff_lt_mul (gap_pos k)).mpr i.isLt⟩
    have e : s.val*gap k + i.val%gap k = i.val := Nat.div_add_mod' _ _
    by_cases h : i.val%gap k=0
    · obtain ⟨p,eq⟩ := index_surjective s
      have kcol : markCol k p=i := Fin.ext (by
        change index p*gap k=i.val
        rw [eq]
        simpa [h] using e)
      refine ⟨.inl p,?_⟩
      cases r <;> simp [shapes,kcol]
    · have rem : i.val%gap k < gap k := Nat.mod_lt _ (gap_pos k)
      let j : Fin k := ⟨(i.val%gap k-1)/3,by have rem2 : i.val%gap k < 3*k+1 := rem; omega⟩
      let d : Fin 3 := ⟨(i.val%gap k-1)%3,by omega⟩
      let b : Blocks k := (s,j,r)
      have eq : column k b d=i := Fin.ext (by
        change s.val*gap k + (3*((i.val%gap k-1)/3)+1+(i.val%gap k-1)%3) = i.val
        omega)
      have ve : vertex k b d = Sum.inl (i,r) := by
        unfold vertex
        change Sum.inl (column k b d,r) = Sum.inl (i,r)
        rw [eq]
      refine ⟨.inr b,?_⟩
      rw [←ve]
      have ds := (by decide : ∀ d : Fin 3, d=0 ∨ d=1 ∨ d=2) d
      simp only [shapes,mem_insert,mem_singleton]
      rcases ds with d0|d1|d2
      · exact Or.inl (congrArg (vertex k b) d0)
      · exact Or.inr (Or.inl (congrArg (vertex k b) d1))
      · exact Or.inr (Or.inr (congrArg (vertex k b) d2))

/-- Marked columns tile through their subdivision-slot center. On every row
the open intervals between consecutive marks have length 3*k, and tile
in consecutive triples. This includes k=0 with no interval tiles. -/
theorem full_factor (k : Nat) : HasFactor (board k) := by
  let P := (univ : Finset (Index k)).image (shapes k)
  refine ⟨P,?_ ,?_,?_⟩
  · intro a ha
    obtain ⟨q,_,rfl⟩ := mem_image.mp ha
    exact shape_tile k q
  · intro a ha b hb ne
    obtain ⟨p,_,rfl⟩ := mem_image.mp ha
    obtain ⟨q,_,rfl⟩ := mem_image.mp hb
    apply disjoint_left.mpr
    intro u up uq
    have ep := key_of_member up
    have eq := key_of_member uq
    exact ne (congrArg (shapes k) (iKey_inj k (ep.symm.trans eq)))
  · apply eq_univ_of_forall
    intro u
    obtain ⟨b,bu⟩ := member_some k u
    exact mem_biUnion.mpr ⟨shapes k b,mem_image_of_mem _ (mem_univ _),bu⟩

#print axioms full_factor
end KelmansCactus.AtomicBridge.PrismSpacedFinal
