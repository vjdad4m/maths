import CompactRows

namespace Graffiti199Depleted.CompactOmission

set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

def coreRows : Fin 6 → Row :=
  ![⟨false,true,true,false,false,true,false⟩,
    ⟨false,true,true,true,false,true,false⟩,
    ⟨false,true,true,false,true,true,false⟩,
    ⟨false,true,true,true,true,true,false⟩,
    ⟨true,true,true,true,false,false,true⟩,
    ⟨true,false,true,false,true,true,true⟩]

private def rowIndex (r : Row) : Fin 6 :=
  match mask r with
  | 46 => 1
  | 54 => 2
  | 62 => 3
  | 79 => 4
  | 117 => 5
  | _ => 0

theorem allowed_core_row (r : Row) (h : allowed r = true) : ∃ k, r = coreRows k :=
  ⟨rowIndex r, by
    rcases r with ⟨a,b,c,d,e,f,g⟩
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;>
      first | rfl | exact False.elim (Bool.noConfusion h)⟩

def mate : Fin 6 → Fin 8 := ![3,3,3,3,1,5]

theorem mate_of_slot (k : Fin 6) :
    (adjacent (coreRows k) 1 4 = false ∧ adjacent (coreRows k) 1 6 = false → mate k = 1) ∧
    (adjacent (coreRows k) 3 0 = false ∧ adjacent (coreRows k) 3 6 = false → mate k = 3) ∧
    (adjacent (coreRows k) 5 0 = false ∧ adjacent (coreRows k) 5 2 = false → mate k = 5) := by
  fin_cases k <;> decide

abbrev Profile := Fin 128

def contact (m : Profile) (i : Fin 8) : Bool := m.val.testBit i.val

def code (r : Row) : Profile :=
  ⟨mask r, (show ∀ r : Row, mask r < 128 by decide) r⟩

theorem contact_code : ∀ (r : Row) (i : Fin 7), contact (code r) i.castSucc = flags r i := by
  decide

theorem contact_omission (m : Profile) : contact m 7 = false := by
  exact (show ∀ m : Profile, contact m 7 = false by decide) m

def boundary (k : Fin 6) : Profile := ![99,99,99,99,105,75] k

theorem boundary_outer (k : Fin 6) : contact (boundary k) 6 = true := by fin_cases k <;> decide

def extension {n : ℕ} (k : Fin 6) (profiles : Fin n → Profile)
    (links : Fin n → Fin n → Bool) : Fin (8+n) → Fin (8+n) → Bool :=
  Fin.addCases (fun i => Fin.addCases (adjacent (coreRows k) i) (fun u => contact (profiles u) i))
    (fun u => Fin.addCases (contact (profiles u)) (links u))

def oneEdge (k : Fin 6) (m : Profile) : Fin 9 → Fin 9 → Bool :=
  extension k (fun _ : Fin 1 => m) (fun _ _ => false)

def pairEdge (k : Fin 6) (m n : Profile) (b : Bool) : Fin 10 → Fin 10 → Bool :=
  extension k (![m,n] : Fin 2 → Profile) (fun u v => (u != v) && b)

def stepEdge (k : Fin 6) (m : Profile) (b : Bool) : Fin 11 → Fin 11 → Bool :=
  extension k (![boundary k,boundary k,m] : Fin 3 → Profile)
    (fun u v => (u != v) && ((u == 0 || v == 0) || b))

def SixTree {n : ℕ} (e : Fin n → Fin n → Bool) (T : Fin 6 → Fin n) : Prop :=
  (∀ i j, T i = T j → i = j) ∧
  ∀ i, i ≠ 0 → ∃ j, e (T i) (T j) = true ∧ j < i ∧
    ∀ h, e (T i) (T h) = true → h < i → h = j

instance {n : ℕ} (e : Fin n → Fin n → Bool) (T : Fin 6 → Fin n) :
    Decidable (SixTree e T) := by unfold SixTree; infer_instance

def PairRoute (e : Fin 10 → Fin 10 → Bool) (P : List (Fin 8)) : Prop :=
  P.Perm (List.finRange 8) ∧
    (8 :: P.map (Fin.castAdd 2) ++ [9]).Chain' (fun i j => e i j = true)

instance (e : Fin 10 → Fin 10 → Bool) (P : List (Fin 8)) :
    Decidable (PairRoute e P) := by unfold PairRoute; infer_instance

def stepOrder (P : List (Fin 8)) (front : Bool) : List (Fin 11) :=
  if front then 10 :: 8 :: P.map (Fin.castAdd 3) ++ [9]
  else 10 :: P.map (Fin.castAdd 3) ++ [8,9]

def StepRoute (e : Fin 11 → Fin 11 → Bool) (P : List (Fin 8)) (front : Bool) : Prop :=
  P.Perm (List.finRange 8) ∧ (stepOrder P front).Chain' (fun i j => e i j = true)

instance (e : Fin 11 → Fin 11 → Bool) (P : List (Fin 8)) (front : Bool) :
    Decidable (StepRoute e P front) := by unfold StepRoute; infer_instance

inductive Certificate (n : ℕ)
  | tree (order : Fin 6 → Fin n)
  | route (order : List (Fin 8)) (front : Bool)
  | pass

def Certificate.Valid {n : ℕ} (e : Fin n → Fin n → Bool)
    (route : List (Fin 8) → Bool → Prop) (pass : Prop) : Certificate n → Prop
  | .tree T => SixTree e T
  | .route P front => route P front
  | .pass => pass

instance {n : ℕ} (e : Fin n → Fin n → Bool) (route : List (Fin 8) → Bool → Prop)
    (p : Prop) [Decidable p] [∀ P f, Decidable (route P f)] (C : Certificate n) :
    Decidable (C.Valid e route p) := by cases C <;> unfold Certificate.Valid <;> infer_instance

def profiles (k : Fin 6) : List Profile :=
  match k.val with
  | 0 => [0,54,85,87,99,117,119]
  | 1 => [0,22,54,85,87,99,117,119]
  | 2 => [0,52,54,85,87,99,117,119]
  | 3 => [0,20,22,38,50,52,54,85,87,99,117,119]
  | 4 => [0,56,105,108,109]
  | 5 => [0,14,27,75,91]
  | _ => []


end Graffiti199Depleted.CompactOmission
