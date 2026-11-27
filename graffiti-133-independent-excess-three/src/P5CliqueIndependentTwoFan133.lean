import P5CliqueIndependentFanWitness133
import P5CliqueFourPortCommonRelayFans133

namespace Graffiti133P5CliqueArms.TwoFan
open SimpleGraph Graffiti133 Graffiti133Camby IndependentFanFinite
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxRecDepth 140000
set_option maxHeartbeats 3000000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {D : Set V} {p : Fin 4→V} {A : Finset V} {f : V→Fin 4→V}

private theorem fan_port_adj (H : PortFanFamily G D p A f) (u : V) (um : u∈A) (i : Fin 4) :
    G.Adj (f u i) (p i) := (H.onlyPort u um i _ (H.portsIn i)).mpr rfl

private theorem fan_role_eq (H : PortFanFamily G D p A f) (u v : V) (um : u∈A) (vm : v∈A)
    (i j : Fin 4) (eq : f u i=f v j) : i=j :=
  H.distinctPorts ((H.onlyPort v vm j _ (H.portsIn i)).mp (eq ▸ fan_port_adj H u um i))

private theorem fan_center_adj (H : PortFanFamily G D p A f) (u : V) (um : u∈A)
    (i : Fin 4) (i0 : i≠0) : G.Adj (f u 0) (f u i) :=
  (H.star u um 0 i (Fin.pos_iff_ne_zero.mpr i0)).mpr rfl

private theorem same_role_in_fans (h4 : FourCycleFree G) (H : PortFanFamily G D p A f)
    (u v : V) (um : u∈A) (vm : v∈A) (i : Fin 4) (eq : f u i=f v i) : u=v := by
  by_cases i0 : i=0
  · subst i
    exact (H.center u um).symm.trans (eq.trans (H.center v vm))
  have ne : p 0≠f u i := fun e=>H.outer u um i (e ▸ H.portsIn 0)
  have e := h4 (p 0) (f u i) (f u 0) (f v 0) ne (fan_port_adj H u um 0).symm
    (fan_center_adj H u um i i0).symm (fan_port_adj H v vm 0).symm
    (eq.symm ▸ (fan_center_adj H v vm i i0).symm)
  exact (H.center u um).symm.trans (e.trans (H.center v vm))

private theorem outer_other_fan_center_not_adj (h4 : FourCycleFree G) (H : PortFanFamily G D p A f)
    (u v : V) (um : u∈A) (vm : v∈A) (uv : u≠v) (i : Fin 4) (i0 : i≠0) :
    ¬G.Adj (f u 0) (f v i) := by
  intro bad
  have ne : f u 0≠p i := fun e=>H.outer u um 0 (e.symm ▸ H.portsIn i)
  have eq := h4 (f u 0) (p i) (f u i) (f v i) ne (fan_center_adj H u um i i0)
    (fan_port_adj H u um i).symm bad (fan_port_adj H v vm i).symm
  exact uv (same_role_in_fans h4 H u v um vm i eq)

private theorem outer_wrong_port (H : PortFanFamily G D p A f)
    (u : V) (um : u∈A) (i j : Fin 4) (ij : i≠j) : ¬G.Adj (f u i) (p j) :=
  fun e=>ij (H.distinctPorts ((H.onlyPort u um i _ (H.portsIn j)).mp e)).symm

private theorem two_fans_center_excludes_cross_edge (h4 : FourCycleFree G) (H : PortFanFamily G D p A f)
    (u v : V) (um : u∈A) (vm : v∈A) (i j : Fin 4) (i0 : i≠0) (j0 : j≠0) :
    ¬(G.Adj (f u 0) (f v 0) ∧ G.Adj (f u i) (f v j)) := by
  rintro ⟨e,g⟩
  have ne : f u 0≠f v j := fun h=>j0 (fan_role_eq H u v um vm _ _ h).symm
  have eq := h4 (f u 0) (f v j) (f v 0) (f u i) ne e
    (fan_center_adj H v vm j j0).symm (fan_center_adj H u um i i0) g.symm
  exact i0 (fan_role_eq H v u vm um _ _ eq).symm

private theorem two_fans_row_excludes_two (h4 : FourCycleFree G) (H : PortFanFamily G D p A f)
    (u v : V) (um : u∈A) (vm : v∈A) (i j k : Fin 4) (i0 : i≠0) (j0 : j≠0) (k0 : k≠0) (jk : j≠k) :
    ¬(G.Adj (f u i) (f v j) ∧ G.Adj (f u i) (f v k)) := by
  rintro ⟨a,b⟩
  have ne : f u i≠f v 0 := fun e=>i0 (fan_role_eq H u v um vm _ _ e)
  have eq := h4 (f u i) (f v 0) (f v j) (f v k) ne a (fan_center_adj H v vm j j0) b
    (fan_center_adj H v vm k k0)
  exact jk (fan_role_eq H v v vm vm _ _ eq)

private theorem two_fans_col_excludes_two (h4 : FourCycleFree G) (H : PortFanFamily G D p A f)
    (u v : V) (um : u∈A) (vm : v∈A) (i j k : Fin 4) (i0 : i≠0) (j0 : j≠0) (k0 : k≠0) (ij : i≠j) :
    ¬(G.Adj (f u i) (f v k) ∧ G.Adj (f u j) (f v k)) := by
  rintro ⟨a,b⟩
  exact two_fans_row_excludes_two h4 H v u vm um k i j k0 i0 j0 ij ⟨a.symm,b.symm⟩

private def fanSlot (i j : Fin 4) : Nat := if i=0 then 0 else 1+3*(i.val-1)+(j.val-1)

private noncomputable def fanBlock (G : SimpleGraph V) (f : V→Fin 4→V) (u v : V) : BitVec 10 := by
  classical
  exact BitVec.ofBoolListLE [decide (G.Adj (f u 0) (f v 0)),decide (G.Adj (f u 1) (f v 1)),decide (G.Adj (f u 1) (f v 2)),decide (G.Adj (f u 1) (f v 3)),decide (G.Adj (f u 2) (f v 1)),decide (G.Adj (f u 2) (f v 2)),decide (G.Adj (f u 2) (f v 3)),decide (G.Adj (f u 3) (f v 1)),decide (G.Adj (f u 3) (f v 2)),decide (G.Adj (f u 3) (f v 3))]

private theorem fanBlock_read (u v : V) (i j : Fin 4)
    (valid : (i=0 ∧ j=0) ∨ (i≠0 ∧ j≠0)) :
    (fanBlock G f u v).toNat.testBit (fanSlot i j)=decide (G.Adj (f u i) (f v j)) := by
  classical
  suffices formal : (fanBlock G f u v).getLsbD (fanSlot i j)=decide (G.Adj (f u i) (f v j)) by exact formal
  fin_cases i <;> fin_cases j
  · change (fanBlock G f u v).getLsbD 0=decide (G.Adj (f u 0) (f v 0))
    simp only [fanBlock,BitVec.getLsb_ofBoolListLE]
    rfl
  · exact ((by decide : ¬(((0:Fin 4)=0 ∧ (1:Fin 4)=0) ∨ ((0:Fin 4)≠0 ∧ (1:Fin 4)≠0))) valid).elim
  · exact ((by decide : ¬(((0:Fin 4)=0 ∧ (2:Fin 4)=0) ∨ ((0:Fin 4)≠0 ∧ (2:Fin 4)≠0))) valid).elim
  · exact ((by decide : ¬(((0:Fin 4)=0 ∧ (3:Fin 4)=0) ∨ ((0:Fin 4)≠0 ∧ (3:Fin 4)≠0))) valid).elim
  · exact ((by decide : ¬(((1:Fin 4)=0 ∧ (0:Fin 4)=0) ∨ ((1:Fin 4)≠0 ∧ (0:Fin 4)≠0))) valid).elim
  · change (fanBlock G f u v).getLsbD 1=decide (G.Adj (f u 1) (f v 1))
    simp only [fanBlock,BitVec.getLsb_ofBoolListLE]
    rfl
  · change (fanBlock G f u v).getLsbD 2=decide (G.Adj (f u 1) (f v 2))
    simp only [fanBlock,BitVec.getLsb_ofBoolListLE]
    rfl
  · change (fanBlock G f u v).getLsbD 3=decide (G.Adj (f u 1) (f v 3))
    simp only [fanBlock,BitVec.getLsb_ofBoolListLE]
    rfl
  · exact ((by decide : ¬(((2:Fin 4)=0 ∧ (0:Fin 4)=0) ∨ ((2:Fin 4)≠0 ∧ (0:Fin 4)≠0))) valid).elim
  · change (fanBlock G f u v).getLsbD 4=decide (G.Adj (f u 2) (f v 1))
    simp only [fanBlock,BitVec.getLsb_ofBoolListLE]
    rfl
  · change (fanBlock G f u v).getLsbD 5=decide (G.Adj (f u 2) (f v 2))
    simp only [fanBlock,BitVec.getLsb_ofBoolListLE]
    rfl
  · change (fanBlock G f u v).getLsbD 6=decide (G.Adj (f u 2) (f v 3))
    simp only [fanBlock,BitVec.getLsb_ofBoolListLE]
    rfl
  · exact ((by decide : ¬(((3:Fin 4)=0 ∧ (0:Fin 4)=0) ∨ ((3:Fin 4)≠0 ∧ (0:Fin 4)≠0))) valid).elim
  · change (fanBlock G f u v).getLsbD 7=decide (G.Adj (f u 3) (f v 1))
    simp only [fanBlock,BitVec.getLsb_ofBoolListLE]
    rfl
  · change (fanBlock G f u v).getLsbD 8=decide (G.Adj (f u 3) (f v 2))
    simp only [fanBlock,BitVec.getLsb_ofBoolListLE]
    rfl
  · change (fanBlock G f u v).getLsbD 9=decide (G.Adj (f u 3) (f v 3))
    simp only [fanBlock,BitVec.getLsb_ofBoolListLE]
    rfl

private theorem fanBlock_pairOK (h4 : FourCycleFree G) (H : PortFanFamily G D p A f)
    (u v : V) (um : u∈A) (vm : v∈A) : pairOK (fanBlock G f u v).toNat=true := by
  classical
  apply List.all_eq_true.mpr
  intro ij ijm
  simp only [rejectPairBits,List.mem_cons,List.not_mem_nil,or_false] at ijm
  rcases ijm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 0 0) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 1 1))=true
    rw [fanBlock_read u v 0 0 (by decide),fanBlock_read u v 1 1 (by decide)]
    have notboth := (two_fans_center_excludes_cross_edge h4 H u v um vm 1 1 (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 0 0) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 1 2))=true
    rw [fanBlock_read u v 0 0 (by decide),fanBlock_read u v 1 2 (by decide)]
    have notboth := (two_fans_center_excludes_cross_edge h4 H u v um vm 1 2 (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 0 0) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 1 3))=true
    rw [fanBlock_read u v 0 0 (by decide),fanBlock_read u v 1 3 (by decide)]
    have notboth := (two_fans_center_excludes_cross_edge h4 H u v um vm 1 3 (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 0 0) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 2 1))=true
    rw [fanBlock_read u v 0 0 (by decide),fanBlock_read u v 2 1 (by decide)]
    have notboth := (two_fans_center_excludes_cross_edge h4 H u v um vm 2 1 (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 0 0) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 2 2))=true
    rw [fanBlock_read u v 0 0 (by decide),fanBlock_read u v 2 2 (by decide)]
    have notboth := (two_fans_center_excludes_cross_edge h4 H u v um vm 2 2 (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 0 0) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 2 3))=true
    rw [fanBlock_read u v 0 0 (by decide),fanBlock_read u v 2 3 (by decide)]
    have notboth := (two_fans_center_excludes_cross_edge h4 H u v um vm 2 3 (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 0 0) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 3 1))=true
    rw [fanBlock_read u v 0 0 (by decide),fanBlock_read u v 3 1 (by decide)]
    have notboth := (two_fans_center_excludes_cross_edge h4 H u v um vm 3 1 (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 0 0) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 3 2))=true
    rw [fanBlock_read u v 0 0 (by decide),fanBlock_read u v 3 2 (by decide)]
    have notboth := (two_fans_center_excludes_cross_edge h4 H u v um vm 3 2 (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 0 0) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 3 3))=true
    rw [fanBlock_read u v 0 0 (by decide),fanBlock_read u v 3 3 (by decide)]
    have notboth := (two_fans_center_excludes_cross_edge h4 H u v um vm 3 3 (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 1 1) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 1 2))=true
    rw [fanBlock_read u v 1 1 (by decide),fanBlock_read u v 1 2 (by decide)]
    have notboth := (two_fans_row_excludes_two h4 H u v um vm 1 1 2 (by decide) (by decide) (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 1 1) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 1 3))=true
    rw [fanBlock_read u v 1 1 (by decide),fanBlock_read u v 1 3 (by decide)]
    have notboth := (two_fans_row_excludes_two h4 H u v um vm 1 1 3 (by decide) (by decide) (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 1 2) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 1 3))=true
    rw [fanBlock_read u v 1 2 (by decide),fanBlock_read u v 1 3 (by decide)]
    have notboth := (two_fans_row_excludes_two h4 H u v um vm 1 2 3 (by decide) (by decide) (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 2 1) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 2 2))=true
    rw [fanBlock_read u v 2 1 (by decide),fanBlock_read u v 2 2 (by decide)]
    have notboth := (two_fans_row_excludes_two h4 H u v um vm 2 1 2 (by decide) (by decide) (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 2 1) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 2 3))=true
    rw [fanBlock_read u v 2 1 (by decide),fanBlock_read u v 2 3 (by decide)]
    have notboth := (two_fans_row_excludes_two h4 H u v um vm 2 1 3 (by decide) (by decide) (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 2 2) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 2 3))=true
    rw [fanBlock_read u v 2 2 (by decide),fanBlock_read u v 2 3 (by decide)]
    have notboth := (two_fans_row_excludes_two h4 H u v um vm 2 2 3 (by decide) (by decide) (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 3 1) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 3 2))=true
    rw [fanBlock_read u v 3 1 (by decide),fanBlock_read u v 3 2 (by decide)]
    have notboth := (two_fans_row_excludes_two h4 H u v um vm 3 1 2 (by decide) (by decide) (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 3 1) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 3 3))=true
    rw [fanBlock_read u v 3 1 (by decide),fanBlock_read u v 3 3 (by decide)]
    have notboth := (two_fans_row_excludes_two h4 H u v um vm 3 1 3 (by decide) (by decide) (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 3 2) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 3 3))=true
    rw [fanBlock_read u v 3 2 (by decide),fanBlock_read u v 3 3 (by decide)]
    have notboth := (two_fans_row_excludes_two h4 H u v um vm 3 2 3 (by decide) (by decide) (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 1 1) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 2 1))=true
    rw [fanBlock_read u v 1 1 (by decide),fanBlock_read u v 2 1 (by decide)]
    have notboth := (two_fans_col_excludes_two h4 H u v um vm 1 2 1 (by decide) (by decide) (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 1 1) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 3 1))=true
    rw [fanBlock_read u v 1 1 (by decide),fanBlock_read u v 3 1 (by decide)]
    have notboth := (two_fans_col_excludes_two h4 H u v um vm 1 3 1 (by decide) (by decide) (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 2 1) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 3 1))=true
    rw [fanBlock_read u v 2 1 (by decide),fanBlock_read u v 3 1 (by decide)]
    have notboth := (two_fans_col_excludes_two h4 H u v um vm 2 3 1 (by decide) (by decide) (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 1 2) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 2 2))=true
    rw [fanBlock_read u v 1 2 (by decide),fanBlock_read u v 2 2 (by decide)]
    have notboth := (two_fans_col_excludes_two h4 H u v um vm 1 2 2 (by decide) (by decide) (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 1 2) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 3 2))=true
    rw [fanBlock_read u v 1 2 (by decide),fanBlock_read u v 3 2 (by decide)]
    have notboth := (two_fans_col_excludes_two h4 H u v um vm 1 3 2 (by decide) (by decide) (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 2 2) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 3 2))=true
    rw [fanBlock_read u v 2 2 (by decide),fanBlock_read u v 3 2 (by decide)]
    have notboth := (two_fans_col_excludes_two h4 H u v um vm 2 3 2 (by decide) (by decide) (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 1 3) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 2 3))=true
    rw [fanBlock_read u v 1 3 (by decide),fanBlock_read u v 2 3 (by decide)]
    have notboth := (two_fans_col_excludes_two h4 H u v um vm 1 2 3 (by decide) (by decide) (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 1 3) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 3 3))=true
    rw [fanBlock_read u v 1 3 (by decide),fanBlock_read u v 3 3 (by decide)]
    have notboth := (two_fans_col_excludes_two h4 H u v um vm 1 3 3 (by decide) (by decide) (by decide) (by decide))
    simp
    tauto
  · change Bool.not ((fanBlock G f u v).toNat.testBit (fanSlot 2 3) &&
      (fanBlock G f u v).toNat.testBit (fanSlot 3 3))=true
    rw [fanBlock_read u v 2 3 (by decide),fanBlock_read u v 3 3 (by decide)]
    have notboth := (two_fans_col_excludes_two h4 H u v um vm 2 3 3 (by decide) (by decide) (by decide) (by decide))
    simp
    tauto

private theorem rawEdge_var (m : Nat) (x y : Fin 16) (i : Nat) (il : i<30) (e : code x y=i) :
    rawEdge m x y=m.testBit i := by simp [rawEdge,e,il]

private theorem rawEdge_const (m : Nat) (x y : Fin 16) (v : Bool) (e : code x y=if v then 30 else 31) :
    rawEdge m x y=v := by cases v <;> simp [rawEdge,e]

private theorem rawEdge_symm (m : Nat) (x y : Fin 16) :
    rawEdge m y x=rawEdge m x y := by simp [rawEdge,code,Nat.min_comm,Nat.max_comm]

def castBase (x : Fin 12) : Fin 16 := ⟨x.val,by have q:=x.isLt; omega⟩

private def decode (x : Fin 12) : Fin 4 ⊕ (Fin 2×Fin 4) :=
  if h : x.val<4 then Sum.inl ⟨x.val,h⟩ else
    Sum.inr (⟨(x.val-4)/4,by omega⟩,⟨x.val%4,by omega⟩)

private theorem decode_inj : Function.Injective decode := by
  have checked : ∀ x y : Fin 12,decode x=decode y→x=y := by decide
  exact fun _ _ e=>checked _ _ e

theorem normalize (h4 : FourCycleFree G) (H : PortFanFamily G D p A f)
    (ind : ∀ i j,¬G.Adj (p i) (p j)) (q r : V) (qm : q∈A) (rm : r∈A) (qr : q≠r) :
    ∃ (m : Fin 35) (e : Fin 12→V), Function.Injective e ∧
      (∀ i : Fin 4,e ⟨i.val,by omega⟩=p i) ∧
      (∀ x : Fin 12,4≤x.val→e x∉D) ∧
      (∀ x : Fin 12,4≤x.val→∀ y∈D,G.Adj (e x) y ↔ y=p ⟨x.val%4,by omega⟩) ∧
      ∀ x y : Fin 12,G.Adj (e x) (e y)↔rawEdge (masks m) (castBase x) (castBase y)=true := by
  classical
  have rq : r≠q := qr.symm
  let a := fanBlock G f q r
  let m := a.toNat
  let centers : Fin 2→V := ![q,r]
  have centersIn (i : Fin 2) : centers i∈A := by
    fin_cases i
    · exact qm
    · exact rm
  have centersI : Function.Injective centers := by
    intro i j e
    fin_cases i <;> fin_cases j
    · rfl
    · exact (qr e).elim
    · exact (qr e.symm).elim
    · rfl
  let e (x : Fin 12) : V :=
    match decode x with
    | .inl i=>p i
    | .inr ij=>f (centers ij.1) ij.2
  have ep (i : Fin 4) : e ⟨i.val,by omega⟩=p i := by
    fin_cases i <;> rfl
  have eqOut (x : Fin 12) (hx : 4≤x.val) :
      e x=f (centers ⟨(x.val-4)/4,by omega⟩) ⟨x.val%4,by omega⟩ := by
    simp only [e,decode,dif_neg (by omega : ¬x.val<4)]
  have eo (x : Fin 12) (hx : 4≤x.val) : e x∉D := by
    rw [eqOut x hx]
    exact H.outer _ (centersIn _) _
  have etag (x : Fin 12) (hx : 4≤x.val) (y : V) (yd : y∈D) :
      G.Adj (e x) y ↔ y=p ⟨x.val%4,by omega⟩ := by
    rw [eqOut x hx]
    exact H.onlyPort _ (centersIn _) _ y yd
  have eI : Function.Injective e := by
    intro x y eq
    apply decode_inj
    cases sx : decode x with
    | inl i =>
      cases sy : decode y with
      | inl j =>
        simp only [e,sx,sy] at eq
        exact congrArg Sum.inl (H.distinctPorts eq)
      | inr jt =>
        simp only [e,sx,sy] at eq
        exact (H.outer _ (centersIn jt.1) _ (eq ▸ H.portsIn i)).elim
    | inr it =>
      cases sy : decode y with
      | inl j =>
        simp only [e,sx,sy] at eq
        exact (H.outer _ (centersIn it.1) _ (eq.symm ▸ H.portsIn j)).elim
      | inr jt =>
        simp only [e,sx,sy] at eq
        obtain ⟨i,k⟩ := it
        obtain ⟨j,l⟩ := jt
        have role : k=l := fan_role_eq H _ _ (centersIn i) (centersIn j) k l eq
        subst l
        have center : i=j := centersI (same_role_in_fans h4 H _ _
          (centersIn i) (centersIn j) k eq)
        subst j
        rfl
  have forward (x y : Fin 12) (xy : x.val≤y.val) :
      G.Adj (e x) (e y)↔rawEdge m (castBase x) (castBase y)=true := by
    fin_cases x <;> fin_cases y <;> try (exfalso; exact (by decide : ¬ _ ≤ _) xy)
    · change G.Adj (p 0) (p 0) ↔ rawEdge m 0 0=true
      rw [rawEdge_const m 0 0 false (by decide)]
      exact ⟨fun h=>(G.loopless (p 0) : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 0) (p 1) ↔ rawEdge m 0 1=true
      rw [rawEdge_const m 0 1 false (by decide)]
      exact ⟨fun h=>(ind 0 1 : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 0) (p 2) ↔ rawEdge m 0 2=true
      rw [rawEdge_const m 0 2 false (by decide)]
      exact ⟨fun h=>(ind 0 2 : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 0) (p 3) ↔ rawEdge m 0 3=true
      rw [rawEdge_const m 0 3 false (by decide)]
      exact ⟨fun h=>(ind 0 3 : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 0) (f q 0) ↔ rawEdge m 0 4=true
      rw [rawEdge_const m 0 4 true (by decide)]
      exact ⟨fun _=>rfl,fun _=>(fan_port_adj H q qm 0).symm⟩
    · change G.Adj (p 0) (f q 1) ↔ rawEdge m 0 5=true
      rw [rawEdge_const m 0 5 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H q qm 1 0 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 0) (f q 2) ↔ rawEdge m 0 6=true
      rw [rawEdge_const m 0 6 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H q qm 2 0 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 0) (f q 3) ↔ rawEdge m 0 7=true
      rw [rawEdge_const m 0 7 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H q qm 3 0 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 0) (f r 0) ↔ rawEdge m 0 8=true
      rw [rawEdge_const m 0 8 true (by decide)]
      exact ⟨fun _=>rfl,fun _=>(fan_port_adj H r rm 0).symm⟩
    · change G.Adj (p 0) (f r 1) ↔ rawEdge m 0 9=true
      rw [rawEdge_const m 0 9 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H r rm 1 0 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 0) (f r 2) ↔ rawEdge m 0 10=true
      rw [rawEdge_const m 0 10 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H r rm 2 0 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 0) (f r 3) ↔ rawEdge m 0 11=true
      rw [rawEdge_const m 0 11 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H r rm 3 0 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 1) (p 1) ↔ rawEdge m 1 1=true
      rw [rawEdge_const m 1 1 false (by decide)]
      exact ⟨fun h=>(G.loopless (p 1) : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 1) (p 2) ↔ rawEdge m 1 2=true
      rw [rawEdge_const m 1 2 false (by decide)]
      exact ⟨fun h=>(ind 1 2 : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 1) (p 3) ↔ rawEdge m 1 3=true
      rw [rawEdge_const m 1 3 false (by decide)]
      exact ⟨fun h=>(ind 1 3 : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 1) (f q 0) ↔ rawEdge m 1 4=true
      rw [rawEdge_const m 1 4 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H q qm 0 1 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 1) (f q 1) ↔ rawEdge m 1 5=true
      rw [rawEdge_const m 1 5 true (by decide)]
      exact ⟨fun _=>rfl,fun _=>(fan_port_adj H q qm 1).symm⟩
    · change G.Adj (p 1) (f q 2) ↔ rawEdge m 1 6=true
      rw [rawEdge_const m 1 6 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H q qm 2 1 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 1) (f q 3) ↔ rawEdge m 1 7=true
      rw [rawEdge_const m 1 7 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H q qm 3 1 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 1) (f r 0) ↔ rawEdge m 1 8=true
      rw [rawEdge_const m 1 8 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H r rm 0 1 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 1) (f r 1) ↔ rawEdge m 1 9=true
      rw [rawEdge_const m 1 9 true (by decide)]
      exact ⟨fun _=>rfl,fun _=>(fan_port_adj H r rm 1).symm⟩
    · change G.Adj (p 1) (f r 2) ↔ rawEdge m 1 10=true
      rw [rawEdge_const m 1 10 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H r rm 2 1 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 1) (f r 3) ↔ rawEdge m 1 11=true
      rw [rawEdge_const m 1 11 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H r rm 3 1 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 2) (p 2) ↔ rawEdge m 2 2=true
      rw [rawEdge_const m 2 2 false (by decide)]
      exact ⟨fun h=>(G.loopless (p 2) : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 2) (p 3) ↔ rawEdge m 2 3=true
      rw [rawEdge_const m 2 3 false (by decide)]
      exact ⟨fun h=>(ind 2 3 : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 2) (f q 0) ↔ rawEdge m 2 4=true
      rw [rawEdge_const m 2 4 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H q qm 0 2 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 2) (f q 1) ↔ rawEdge m 2 5=true
      rw [rawEdge_const m 2 5 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H q qm 1 2 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 2) (f q 2) ↔ rawEdge m 2 6=true
      rw [rawEdge_const m 2 6 true (by decide)]
      exact ⟨fun _=>rfl,fun _=>(fan_port_adj H q qm 2).symm⟩
    · change G.Adj (p 2) (f q 3) ↔ rawEdge m 2 7=true
      rw [rawEdge_const m 2 7 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H q qm 3 2 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 2) (f r 0) ↔ rawEdge m 2 8=true
      rw [rawEdge_const m 2 8 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H r rm 0 2 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 2) (f r 1) ↔ rawEdge m 2 9=true
      rw [rawEdge_const m 2 9 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H r rm 1 2 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 2) (f r 2) ↔ rawEdge m 2 10=true
      rw [rawEdge_const m 2 10 true (by decide)]
      exact ⟨fun _=>rfl,fun _=>(fan_port_adj H r rm 2).symm⟩
    · change G.Adj (p 2) (f r 3) ↔ rawEdge m 2 11=true
      rw [rawEdge_const m 2 11 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H r rm 3 2 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 3) (p 3) ↔ rawEdge m 3 3=true
      rw [rawEdge_const m 3 3 false (by decide)]
      exact ⟨fun h=>(G.loopless (p 3) : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 3) (f q 0) ↔ rawEdge m 3 4=true
      rw [rawEdge_const m 3 4 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H q qm 0 3 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 3) (f q 1) ↔ rawEdge m 3 5=true
      rw [rawEdge_const m 3 5 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H q qm 1 3 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 3) (f q 2) ↔ rawEdge m 3 6=true
      rw [rawEdge_const m 3 6 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H q qm 2 3 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 3) (f q 3) ↔ rawEdge m 3 7=true
      rw [rawEdge_const m 3 7 true (by decide)]
      exact ⟨fun _=>rfl,fun _=>(fan_port_adj H q qm 3).symm⟩
    · change G.Adj (p 3) (f r 0) ↔ rawEdge m 3 8=true
      rw [rawEdge_const m 3 8 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H r rm 0 3 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 3) (f r 1) ↔ rawEdge m 3 9=true
      rw [rawEdge_const m 3 9 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H r rm 1 3 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 3) (f r 2) ↔ rawEdge m 3 10=true
      rw [rawEdge_const m 3 10 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_wrong_port H r rm 2 3 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (p 3) (f r 3) ↔ rawEdge m 3 11=true
      rw [rawEdge_const m 3 11 true (by decide)]
      exact ⟨fun _=>rfl,fun _=>(fan_port_adj H r rm 3).symm⟩
    · change G.Adj (f q 0) (f q 0) ↔ rawEdge m 4 4=true
      rw [rawEdge_const m 4 4 false (by decide)]
      exact ⟨fun h=>(G.loopless (f q 0) : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (f q 0) (f q 1) ↔ rawEdge m 4 5=true
      rw [rawEdge_const m 4 5 true (by decide)]
      exact ⟨fun _=>rfl,fun _=>fan_center_adj H q qm 1 (by decide)⟩
    · change G.Adj (f q 0) (f q 2) ↔ rawEdge m 4 6=true
      rw [rawEdge_const m 4 6 true (by decide)]
      exact ⟨fun _=>rfl,fun _=>fan_center_adj H q qm 2 (by decide)⟩
    · change G.Adj (f q 0) (f q 3) ↔ rawEdge m 4 7=true
      rw [rawEdge_const m 4 7 true (by decide)]
      exact ⟨fun _=>rfl,fun _=>fan_center_adj H q qm 3 (by decide)⟩
    · change G.Adj (f q 0) (f r 0) ↔ rawEdge m 4 8=true
      rw [rawEdge_var m 4 8 0 (by decide) (by decide)]

      change G.Adj (f q 0) (f r 0) ↔ a.toNat.testBit (fanSlot 0 0)=true
      rw [fanBlock_read q r 0 0 (by decide)]
      simp
    · change G.Adj (f q 0) (f r 1) ↔ rawEdge m 4 9=true
      rw [rawEdge_const m 4 9 false (by decide)]
      exact ⟨fun h=>(outer_other_fan_center_not_adj h4 H q r qm rm rq.symm 1 (by decide) : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (f q 0) (f r 2) ↔ rawEdge m 4 10=true
      rw [rawEdge_const m 4 10 false (by decide)]
      exact ⟨fun h=>(outer_other_fan_center_not_adj h4 H q r qm rm rq.symm 2 (by decide) : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (f q 0) (f r 3) ↔ rawEdge m 4 11=true
      rw [rawEdge_const m 4 11 false (by decide)]
      exact ⟨fun h=>(outer_other_fan_center_not_adj h4 H q r qm rm rq.symm 3 (by decide) : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (f q 1) (f q 1) ↔ rawEdge m 5 5=true
      rw [rawEdge_const m 5 5 false (by decide)]
      exact ⟨fun h=>(G.loopless (f q 1) : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (f q 1) (f q 2) ↔ rawEdge m 5 6=true
      rw [rawEdge_const m 5 6 false (by decide)]
      exact ⟨fun h=>(fun h=>(by decide : (1:Fin 4)≠0) ((H.star q qm 1 2 (by decide)).mp h) : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (f q 1) (f q 3) ↔ rawEdge m 5 7=true
      rw [rawEdge_const m 5 7 false (by decide)]
      exact ⟨fun h=>(fun h=>(by decide : (1:Fin 4)≠0) ((H.star q qm 1 3 (by decide)).mp h) : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (f q 1) (f r 0) ↔ rawEdge m 5 8=true
      rw [rawEdge_const m 5 8 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_other_fan_center_not_adj h4 H r q rm qm rq 1 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (f q 1) (f r 1) ↔ rawEdge m 5 9=true
      rw [rawEdge_var m 5 9 1 (by decide) (by decide)]

      change G.Adj (f q 1) (f r 1) ↔ a.toNat.testBit (fanSlot 1 1)=true
      rw [fanBlock_read q r 1 1 (by decide)]
      simp
    · change G.Adj (f q 1) (f r 2) ↔ rawEdge m 5 10=true
      rw [rawEdge_var m 5 10 2 (by decide) (by decide)]

      change G.Adj (f q 1) (f r 2) ↔ a.toNat.testBit (fanSlot 1 2)=true
      rw [fanBlock_read q r 1 2 (by decide)]
      simp
    · change G.Adj (f q 1) (f r 3) ↔ rawEdge m 5 11=true
      rw [rawEdge_var m 5 11 3 (by decide) (by decide)]

      change G.Adj (f q 1) (f r 3) ↔ a.toNat.testBit (fanSlot 1 3)=true
      rw [fanBlock_read q r 1 3 (by decide)]
      simp
    · change G.Adj (f q 2) (f q 2) ↔ rawEdge m 6 6=true
      rw [rawEdge_const m 6 6 false (by decide)]
      exact ⟨fun h=>(G.loopless (f q 2) : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (f q 2) (f q 3) ↔ rawEdge m 6 7=true
      rw [rawEdge_const m 6 7 false (by decide)]
      exact ⟨fun h=>(fun h=>(by decide : (2:Fin 4)≠0) ((H.star q qm 2 3 (by decide)).mp h) : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (f q 2) (f r 0) ↔ rawEdge m 6 8=true
      rw [rawEdge_const m 6 8 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_other_fan_center_not_adj h4 H r q rm qm rq 2 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (f q 2) (f r 1) ↔ rawEdge m 6 9=true
      rw [rawEdge_var m 6 9 4 (by decide) (by decide)]

      change G.Adj (f q 2) (f r 1) ↔ a.toNat.testBit (fanSlot 2 1)=true
      rw [fanBlock_read q r 2 1 (by decide)]
      simp
    · change G.Adj (f q 2) (f r 2) ↔ rawEdge m 6 10=true
      rw [rawEdge_var m 6 10 5 (by decide) (by decide)]

      change G.Adj (f q 2) (f r 2) ↔ a.toNat.testBit (fanSlot 2 2)=true
      rw [fanBlock_read q r 2 2 (by decide)]
      simp
    · change G.Adj (f q 2) (f r 3) ↔ rawEdge m 6 11=true
      rw [rawEdge_var m 6 11 6 (by decide) (by decide)]

      change G.Adj (f q 2) (f r 3) ↔ a.toNat.testBit (fanSlot 2 3)=true
      rw [fanBlock_read q r 2 3 (by decide)]
      simp
    · change G.Adj (f q 3) (f q 3) ↔ rawEdge m 7 7=true
      rw [rawEdge_const m 7 7 false (by decide)]
      exact ⟨fun h=>(G.loopless (f q 3) : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (f q 3) (f r 0) ↔ rawEdge m 7 8=true
      rw [rawEdge_const m 7 8 false (by decide)]
      exact ⟨fun h=>(fun h=>outer_other_fan_center_not_adj h4 H r q rm qm rq 3 (by decide) h.symm : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (f q 3) (f r 1) ↔ rawEdge m 7 9=true
      rw [rawEdge_var m 7 9 7 (by decide) (by decide)]

      change G.Adj (f q 3) (f r 1) ↔ a.toNat.testBit (fanSlot 3 1)=true
      rw [fanBlock_read q r 3 1 (by decide)]
      simp
    · change G.Adj (f q 3) (f r 2) ↔ rawEdge m 7 10=true
      rw [rawEdge_var m 7 10 8 (by decide) (by decide)]

      change G.Adj (f q 3) (f r 2) ↔ a.toNat.testBit (fanSlot 3 2)=true
      rw [fanBlock_read q r 3 2 (by decide)]
      simp
    · change G.Adj (f q 3) (f r 3) ↔ rawEdge m 7 11=true
      rw [rawEdge_var m 7 11 9 (by decide) (by decide)]

      change G.Adj (f q 3) (f r 3) ↔ a.toNat.testBit (fanSlot 3 3)=true
      rw [fanBlock_read q r 3 3 (by decide)]
      simp
    · change G.Adj (f r 0) (f r 0) ↔ rawEdge m 8 8=true
      rw [rawEdge_const m 8 8 false (by decide)]
      exact ⟨fun h=>(G.loopless (f r 0) : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (f r 0) (f r 1) ↔ rawEdge m 8 9=true
      rw [rawEdge_const m 8 9 true (by decide)]
      exact ⟨fun _=>rfl,fun _=>fan_center_adj H r rm 1 (by decide)⟩
    · change G.Adj (f r 0) (f r 2) ↔ rawEdge m 8 10=true
      rw [rawEdge_const m 8 10 true (by decide)]
      exact ⟨fun _=>rfl,fun _=>fan_center_adj H r rm 2 (by decide)⟩
    · change G.Adj (f r 0) (f r 3) ↔ rawEdge m 8 11=true
      rw [rawEdge_const m 8 11 true (by decide)]
      exact ⟨fun _=>rfl,fun _=>fan_center_adj H r rm 3 (by decide)⟩
    · change G.Adj (f r 1) (f r 1) ↔ rawEdge m 9 9=true
      rw [rawEdge_const m 9 9 false (by decide)]
      exact ⟨fun h=>(G.loopless (f r 1) : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (f r 1) (f r 2) ↔ rawEdge m 9 10=true
      rw [rawEdge_const m 9 10 false (by decide)]
      exact ⟨fun h=>(fun h=>(by decide : (1:Fin 4)≠0) ((H.star r rm 1 2 (by decide)).mp h) : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (f r 1) (f r 3) ↔ rawEdge m 9 11=true
      rw [rawEdge_const m 9 11 false (by decide)]
      exact ⟨fun h=>(fun h=>(by decide : (1:Fin 4)≠0) ((H.star r rm 1 3 (by decide)).mp h) : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (f r 2) (f r 2) ↔ rawEdge m 10 10=true
      rw [rawEdge_const m 10 10 false (by decide)]
      exact ⟨fun h=>(G.loopless (f r 2) : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (f r 2) (f r 3) ↔ rawEdge m 10 11=true
      rw [rawEdge_const m 10 11 false (by decide)]
      exact ⟨fun h=>(fun h=>(by decide : (2:Fin 4)≠0) ((H.star r rm 2 3 (by decide)).mp h) : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
    · change G.Adj (f r 3) (f r 3) ↔ rawEdge m 11 11=true
      rw [rawEdge_const m 11 11 false (by decide)]
      exact ⟨fun h=>(G.loopless (f r 3) : ¬_) h |>.elim,fun h=>Bool.noConfusion h⟩
  have fit (x y : Fin 12) : G.Adj (e x) (e y)↔rawEdge m (castBase x) (castBase y)=true := by
    by_cases xy : x.val≤y.val
    · exact forward x y xy
    rw [SimpleGraph.adj_comm,rawEdge_symm m (castBase y) (castBase x)]
    exact forward y x (by omega)
  obtain ⟨i,ie⟩ := pair_ok_is_mask ⟨a.toNat,a.isLt⟩ (fanBlock_pairOK h4 H q r qm rm)
  change m=masks i at ie
  refine ⟨i,e,eI,ep,eo,etag,?_⟩
  rw [←ie]
  exact fit

#print axioms normalize
end Graffiti133P5CliqueArms.TwoFan
