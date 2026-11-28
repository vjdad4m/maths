import T11TenBits384b
import Mathlib.Data.Fintype.EquivFin

namespace Graffiti384b.T11TenNormalize
open Finset
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

private def cutCond (k : Fin 4) (n : Nat) : Bool :=
  let A := maskSet n
  decide (A.card=5 ∧ 0∈A ∧ ((clique.filter (opposite A 0)).card=2) ∧
    ((diamond k |>.filter (opposite A 4)).card=2))
private def perms0 : Fin 12 → Label → Label :=
 ![![0,1,2,3,4,5,6,7,8,9],
   ![0,1,2,3,4,5,6,7,9,8],
   ![0,1,2,3,4,6,5,7,8,9],
   ![0,1,2,3,4,6,5,7,9,8],
   ![0,2,1,3,4,5,6,7,8,9],
   ![0,2,1,3,4,5,6,7,9,8],
   ![0,2,1,3,4,6,5,7,8,9],
   ![0,2,1,3,4,6,5,7,9,8],
   ![0,3,1,2,4,5,6,7,8,9],
   ![0,3,1,2,4,5,6,7,9,8],
   ![0,3,1,2,4,6,5,7,8,9],
   ![0,3,1,2,4,6,5,7,9,8]]
private def rows0 : List (Nat × Fin 12 × Nat) :=
 [(307,0,307),
  (563,1,307),
  (339,2,307),
  (595,3,307),
  (403,0,403),
  (659,1,403),
  (355,0,355),
  (611,1,355),
  (419,0,419),
  (675,1,419),
  (451,2,419),
  (707,3,419),
  (309,4,307),
  (565,5,307),
  (341,6,307),
  (597,7,307),
  (405,4,403),
  (661,5,403),
  (357,4,355),
  (613,5,355),
  (421,4,419),
  (677,5,419),
  (453,6,419),
  (709,7,419),
  (313,8,307),
  (569,9,307),
  (345,10,307),
  (601,11,307),
  (409,8,403),
  (665,9,403),
  (361,8,355),
  (617,9,355),
  (425,8,419),
  (681,9,419),
  (457,10,419),
  (713,11,419)]
private def perms1 : Fin 8 → Label → Label :=
 ![![0,1,2,3,4,5,6,7,8,9],
   ![0,1,2,3,4,5,6,7,9,8],
   ![0,1,2,3,4,5,6,8,7,9],
   ![0,1,2,3,4,5,6,8,9,7],
   ![0,1,2,3,4,5,6,9,7,8],
   ![0,1,3,2,4,5,6,7,8,9],
   ![0,1,3,2,4,5,6,8,7,9],
   ![0,1,3,2,4,5,6,9,7,8]]
private def rows1 : List (Nat × Fin 8 × Nat) :=
 [(403,0,403),
  (659,1,403),
  (787,3,403),
  (419,0,419),
  (675,1,419),
  (803,3,419),
  (451,0,451),
  (707,1,451),
  (835,3,451),
  (181,0,181),
  (309,2,181),
  (565,4,181),
  (213,0,213),
  (341,2,213),
  (597,4,213),
  (229,0,229),
  (357,2,229),
  (613,4,229),
  (185,5,181),
  (313,6,181),
  (569,7,181),
  (217,5,213),
  (345,6,213),
  (601,7,213),
  (233,5,229),
  (361,6,229),
  (617,7,229)]
private def perms2 : Fin 16 → Label → Label :=
 ![![0,1,2,3,4,5,6,7,8,9],
   ![0,1,2,3,4,5,6,7,9,8],
   ![0,1,2,3,4,5,6,8,7,9],
   ![0,1,2,3,4,5,6,8,9,7],
   ![0,1,2,3,4,5,6,9,7,8],
   ![0,1,2,3,4,6,5,7,8,9],
   ![0,1,2,3,4,6,5,7,9,8],
   ![0,1,2,3,4,6,5,8,7,9],
   ![0,1,2,3,4,6,5,8,9,7],
   ![0,1,2,3,4,6,5,9,7,8],
   ![0,1,3,2,4,5,6,7,8,9],
   ![0,1,3,2,4,5,6,8,7,9],
   ![0,1,3,2,4,5,6,9,7,8],
   ![0,1,3,2,4,6,5,7,8,9],
   ![0,1,3,2,4,6,5,8,7,9],
   ![0,1,3,2,4,6,5,9,7,8]]
private def rows2 : List (Nat × Fin 16 × Nat) :=
 [(403,0,403),
  (659,1,403),
  (787,3,403),
  (419,0,419),
  (675,1,419),
  (803,3,419),
  (451,5,419),
  (707,6,419),
  (835,8,419),
  (181,0,181),
  (309,2,181),
  (565,4,181),
  (213,5,181),
  (341,7,181),
  (597,9,181),
  (229,0,229),
  (357,2,229),
  (613,4,229),
  (185,10,181),
  (313,11,181),
  (569,12,181),
  (217,13,181),
  (345,14,181),
  (601,15,181),
  (233,10,229),
  (361,11,229),
  (617,12,229)]
private def perms3 : Fin 9 → Label → Label :=
 ![![0,1,2,3,4,5,6,7,8,9],
   ![0,1,2,3,4,5,6,8,7,9],
   ![0,1,2,3,4,5,6,9,7,8],
   ![0,1,2,3,4,5,7,6,8,9],
   ![0,1,2,3,4,5,7,8,6,9],
   ![0,1,2,3,4,5,7,9,6,8],
   ![0,1,2,3,4,5,8,6,7,9],
   ![0,1,2,3,4,5,8,9,6,7],
   ![0,1,2,3,4,5,9,6,7,8]]
private def rows3 : List (Nat × Fin 9 × Nat) :=
 [(211,0,211),
  (339,1,211),
  (595,2,211),
  (403,4,211),
  (659,5,211),
  (787,7,211),
  (227,0,227),
  (355,1,227),
  (611,2,227),
  (419,4,227),
  (675,5,227),
  (803,7,227),
  (213,0,213),
  (341,1,213),
  (597,2,213),
  (405,4,213),
  (661,5,213),
  (789,7,213),
  (229,0,229),
  (357,1,229),
  (613,2,229),
  (421,4,229),
  (677,5,229),
  (805,7,229),
  (121,0,121),
  (185,3,121),
  (313,6,121),
  (569,8,121)]

private def certPermutation (k : Fin 4) (p : Label → Label) : Prop :=
  Function.Injective p ∧ p 0=0 ∧ p 4=4 ∧ ∀ i j, motif k i j = motif k (p i) (p j)

instance (k : Fin 4) (p : Label → Label) : Decidable (certPermutation k p) := by
  unfold certPermutation Function.Injective
  infer_instance

private def certRow {N : Nat} (k : Fin 4) (t : Fin N → Label → Label)
    (r : Nat × Fin N × Nat) : Prop :=
  r.2.2 ∈ allowedCuts k ∧ ∀ i : Label, r.2.2.testBit i.val = r.1.testBit (t r.2.1 i).val

instance {N : Nat} (k : Fin 4) (t : Fin N → Label → Label)
    (r : Nat × Fin N × Nat) : Decidable (certRow k t r) := by
  unfold certRow
  infer_instance

private theorem cert {N : Nat} (k : Fin 4) (t : Fin N → Label → Label)
    (rows : List (Nat × Fin N × Nat)) (n : Fin 1024)
    (accept : cutCond k n.val = true → n.val ∈ rows.map Prod.fst)
    (rowChecked : rows.all (fun r => decide (certRow k t r)) = true)
    (permsChecked : ∀ i, certPermutation k (t i))
    (h : cutCond k n.val = true) :
    ∃ (p : Label ≃ Label) (m : Nat), p 0=0 ∧ p 4=4 ∧ m∈allowedCuts k ∧
      (∀ i : Label,m.testBit i.val=n.val.testBit (p i).val) ∧
      (∀ i j,motif k i j=motif k (p i) (p j)) := by
  obtain ⟨r,rm,re⟩ := List.mem_map.mp (accept h)
  have rOK := of_decide_eq_true ((List.all_eq_true.mp rowChecked) r rm)
  obtain ⟨fi,f0,f4,fs⟩ := permsChecked r.2.1
  let p := Equiv.ofBijective (t r.2.1) (Finite.injective_iff_bijective.mp fi)
  refine ⟨p,r.2.2,f0,f4,rOK.1,?_,fs⟩
  intro i
  rw [rOK.2 i,re]
  rfl

private theorem cutCond_true (k : Fin 4) (A : Finset Label)
    (c : A.card=5) (a : 0∈A)
    (p : (clique.filter (opposite A 0)).card=2)
    (q : ((diamond k).filter (opposite A 4)).card=2) :
    cutCond k (encode A).val = true := by
  simp [cutCond,maskSet_encode,c,a,p,q]

private theorem covered0 (n : Fin 1024) :
    cutCond 0 n.val = true → n.val ∈ rows0.map Prod.fst := by
  let a : Fin 16 := ⟨n.val / 64,by have := n.isLt; omega⟩
  let b : Fin 64 := ⟨n.val % 64,Nat.mod_lt _ (by decide)⟩
  have eq : n.val = 64*a.val+b.val := by
    dsimp [a,b]; omega
  have closed : ∀ (c : Fin 16) (r : Fin 64),
      cutCond 0 (64*c.val+r.val) = true → 64*c.val+r.val ∈ rows0.map Prod.fst := by
    intro c
    fin_cases c <;> decide
  rw [eq]
  exact closed a b

private theorem rowsChecked0 : rows0.all (fun r => decide (certRow 0 perms0 r)) = true := by decide
private theorem permsChecked0 : ∀ i, certPermutation 0 (perms0 i) := by decide

private theorem covered1 (n : Fin 1024) :
    cutCond 1 n.val = true → n.val ∈ rows1.map Prod.fst := by
  let a : Fin 16 := ⟨n.val / 64,by have := n.isLt; omega⟩
  let b : Fin 64 := ⟨n.val % 64,Nat.mod_lt _ (by decide)⟩
  have eq : n.val = 64*a.val+b.val := by
    dsimp [a,b]; omega
  have closed : ∀ (c : Fin 16) (r : Fin 64),
      cutCond 1 (64*c.val+r.val) = true → 64*c.val+r.val ∈ rows1.map Prod.fst := by
    intro c
    fin_cases c <;> decide
  rw [eq]
  exact closed a b

private theorem rowsChecked1 : rows1.all (fun r => decide (certRow 1 perms1 r)) = true := by decide
private theorem permsChecked1 : ∀ i, certPermutation 1 (perms1 i) := by decide

private theorem covered2 (n : Fin 1024) :
    cutCond 2 n.val = true → n.val ∈ rows2.map Prod.fst := by
  let a : Fin 16 := ⟨n.val / 64,by have := n.isLt; omega⟩
  let b : Fin 64 := ⟨n.val % 64,Nat.mod_lt _ (by decide)⟩
  have eq : n.val = 64*a.val+b.val := by
    dsimp [a,b]; omega
  have closed : ∀ (c : Fin 16) (r : Fin 64),
      cutCond 2 (64*c.val+r.val) = true → 64*c.val+r.val ∈ rows2.map Prod.fst := by
    intro c
    fin_cases c <;> decide
  rw [eq]
  exact closed a b

private theorem rowsChecked2 : rows2.all (fun r => decide (certRow 2 perms2 r)) = true := by decide
private theorem permsChecked2 : ∀ i, certPermutation 2 (perms2 i) := by decide

private theorem covered3 (n : Fin 1024) :
    cutCond 3 n.val = true → n.val ∈ rows3.map Prod.fst := by
  let a : Fin 16 := ⟨n.val / 64,by have := n.isLt; omega⟩
  let b : Fin 64 := ⟨n.val % 64,Nat.mod_lt _ (by decide)⟩
  have eq : n.val = 64*a.val+b.val := by
    dsimp [a,b]; omega
  have closed : ∀ (c : Fin 16) (r : Fin 64),
      cutCond 3 (64*c.val+r.val) = true → 64*c.val+r.val ∈ rows3.map Prod.fst := by
    intro c
    fin_cases c <;> decide
  rw [eq]
  exact closed a b

private theorem rowsChecked3 : rows3.all (fun r => decide (certRow 3 perms3 r)) = true := by decide
private theorem permsChecked3 : ∀ i, certPermutation 3 (perms3 i) := by decide

/-- Canonicalize the balanced color class using only automorphisms of the
already normalized cubic motif. -/
theorem normalize_cut (k : Fin 4) (A : Finset Label)
    (c : A.card=5) (a : 0∈A)
    (p : (clique.filter (opposite A 0)).card=2)
    (q : ((diamond k).filter (opposite A 4)).card=2) :
    ∃ (e : Label ≃ Label) (m : Nat), e 0=0 ∧ e 4=4 ∧ m∈allowedCuts k ∧
      (∀ i : Label,e i∈A ↔ m.testBit i.val=true) ∧
      (∀ i j,motif k i j=motif k (e i) (e j)) := by
  let n := encode A
  have h := cutCond_true k A c a p q
  have step : ∃ (e : Label ≃ Label) (m : Nat), e 0=0 ∧ e 4=4 ∧ m∈allowedCuts k ∧
      (∀ i : Label,m.testBit i.val=n.val.testBit (e i).val) ∧
      (∀ i j,motif k i j=motif k (e i) (e j)) := by
    fin_cases k
    · exact cert 0 perms0 rows0 n (covered0 n) rowsChecked0 permsChecked0 h
    · exact cert 1 perms1 rows1 n (covered1 n) rowsChecked1 permsChecked1 h
    · exact cert 2 perms2 rows2 n (covered2 n) rowsChecked2 permsChecked2 h
    · exact cert 3 perms3 rows3 n (covered3 n) rowsChecked3 permsChecked3 h

  obtain ⟨e,m,e0,e4,mm,bit,spec⟩ := step
  refine ⟨e,m,e0,e4,mm,?_,spec⟩
  intro i
  rw [bit i,← mem_maskSet,show n=encode A from rfl,maskSet_encode]

end Graffiti384b.T11TenNormalize
#print axioms Graffiti384b.T11TenNormalize.normalize_cut
