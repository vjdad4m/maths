import SixSingletonPortCertificates189
import SixSingletonAdjThreeBoard189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open FiveAdjacent (terminal_route_on_of_local_ore)
abbrev V := Fin 16
abbrev a : V := 0
abbrev b : V := 1
abbrev s : V := 2
def D : Finset V := {9,10,11,12,13,14,15}
private theorem dark7 : D.card=7 := by decide

def e22 (u : Fin 4) : V := ![3,4,5,6] u
def c22 (u : Fin 2) : V := ![7,8] u
def terminal (u : Fin 4) : V := if left u then a else b
def termOther (u : Fin 4) : V := if left u then b else a
private theorem mate_left (u : Fin 4) : left (mate u)=left u := by fin_cases u <;> decide
private theorem term_mate (u : Fin 4) : terminal (mate u)=terminal u := by fin_cases u <;> decide
private theorem opposite_term (u v : Fin 4) (opp : left u≠left v) : terminal (mate v)=termOther u := by
  fin_cases u <;> fin_cases v <;> simp_all [terminal,mate,termOther,left] <;> decide
private theorem certificate22_fun (T : Fin 2→Fin 4→Bool) (A : Fin 4→Bool)
    (valid : pairTwoModel T A) : pairTwoRoute T A := by
  have t : mat24 (T 0 0) (T 0 1) (T 0 2) (T 0 3) (T 1 0) (T 1 1) (T 1 2) (T 1 3)=T := by
    funext k j
    fin_cases k <;> fin_cases j <;> rfl
  have a : row4 (A 0) (A 1) (A 2) (A 3)=A := by
    funext k
    fin_cases k <;> rfl
  have cert := pair_two_certificate (T 0 0) (T 0 1) (T 0 2) (T 0 3) (T 1 0) (T 1 1) (T 1 2) (T 1 3)
    (A 0) (A 1) (A 2) (A 3)
  rw [t,a] at cert
  exact cert valid

private theorem plan22 :
    ∀ (u v : Fin 4) (k : Fin 2), left u≠left v →
      let A := insert s (insert (terminal u) (insert (e22 u) D))
      let B := insert (e22 v) A
      let C := insert (c22 k) B
      let E := insert (e22 (mate u)) C
      let F := insert (c22 (other k)) E
      let H := insert (termOther u) F
      e22 u∉D ∧ terminal u∉insert (e22 u) D ∧ s∉insert (terminal u) (insert (e22 u) D) ∧
      e22 v∉A ∧ c22 k∉B ∧ e22 (mate u)∉C ∧ c22 (other k)∉E ∧ termOther u∉F ∧
      e22 (mate v)∉H ∧ ∀ z,z∈insert (e22 (mate v)) H := by decide

variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

structure Board22 (G : SimpleGraph V) [DecidableRel G.Adj] (A : Fin 4→Bool) (L R : Finset V) : Prop where
  sa : G.Adj s a
  sb : G.Adj s b
  port : ∀ u,G.Adj (terminal u) (e22 u)
  commonA : ∀ k,G.Adj a (c22 k)
  commonB : ∀ k,G.Adj b (c22 k)
  root : ∀ u,A u=true → ∃ t∈(if left u then L else R),G.Adj (e22 u) t
  rootL : L⊆D
  rootR : R⊆D
  rootDis : Disjoint L R
  dark : ∀ t∈D,4≤(inside G D t).card
  valid : pairTwoModel (fun k u=>decide (G.Adj (c22 k) (e22 u))) A

theorem traceable_of_double_exclusive_zero_balanced {A : Fin 4→Bool} {L R : Finset V}
    (F : Board22 G A L R) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  obtain ⟨u,v,k,op,ua,va,kv,ks,ls⟩ := certificate22_fun _ _ F.valid
  obtain ⟨i,im,ui⟩ := F.root u ua
  obtain ⟨j,jm,vj⟩ := F.root v va
  have on (z : Fin 4) {p : V} (m : p∈(if left z then L else R)) : p∈D := by
    split at m
    · exact F.rootL m
    exact F.rootR m
  have ij : i≠j := by
    intro e
    subst j
    cases ul : left u <;> cases vl : left v
    · exact op (ul.trans vl.symm)
    · simp [ul,vl] at im jm
      exact disjoint_left.mp F.rootDis jm im
    · simp [ul,vl] at im jm
      exact disjoint_left.mp F.rootDis im jm
    exact op (ul.trans vl.symm)
  have path : RouteOn G D i j :=
    terminal_route_on_of_local_ore D (on u im) (on v jm) ij (by
      intro p pm q qm _ _
      have h := F.dark p pm
      have j := F.dark q qm
      have d := dark7
      omega)
  obtain ⟨n1,n2,n3,n4,n5,n6,n7,n8,n9,all⟩ := plan22 u v k op
  have boot : G.Adj s (terminal u) := by
    unfold terminal
    split <;> first | exact F.sa | exact F.sb
  have lastBridge : G.Adj (c22 (other k)) (termOther u) := by
    unfold termOther
    split <;> first | exact (F.commonB _).symm | exact (F.commonA _).symm
  have tail : G.Adj (termOther u) (e22 (mate v)) := by
    rw [←opposite_term u v op]
    exact F.port _
  have r1 := path.prefix ui n1
  have r2 := r1.prefix (F.port u) n2
  have r3 := r2.prefix boot n3
  have r4 := r3.suffix vj.symm n4
  have r5 := r4.suffix (of_decide_eq_true kv).symm n5
  have r6 := r5.suffix (of_decide_eq_true ks) n6
  have r7 := r6.suffix (of_decide_eq_true ls).symm n7
  have r8 := r7.suffix lastBridge n8
  obtain ⟨p,pp,ps⟩ := r8.suffix tail n9
  exact ⟨s,_,p,pp,fun z=>(ps z).mpr (all z)⟩

def c12 (u : Fin 3) : V := ![6,7,8] u
abbrev x12 : V := 3
def y12 (i : Fin 2) : V := ![4,5] i
def e12 (i : Fin 3) : V := ![3,4,5] i
private theorem y12_index (i : Fin 2) : e12 (yIndex i)=y12 i := by fin_cases i <;> decide

private theorem certificate12_fun (C T : Fin 3→Fin 3→Bool) (A : Fin 2→Bool)
    (Cs : ∀ u v,C u v=C v u) (Cn : ∀ u,C u u=false)
    (valid : oneTwoModel C T A) : oneTwoRoute C T A := by
  have c : rows33 (C 0 1) (C 0 2) (C 1 2)=C := by
    funext k j
    fin_cases k <;> fin_cases j
    · exact (Cn _).symm
    · rfl
    · rfl
    · exact Cs _ _
    · exact (Cn _).symm
    · rfl
    · exact Cs _ _
    · exact Cs _ _
    exact (Cn _).symm
  have t : mat33 (T 0 0) (T 0 1) (T 0 2) (T 1 0) (T 1 1) (T 1 2) (T 2 0) (T 2 1) (T 2 2)=T := by
    funext k j
    fin_cases k <;> fin_cases j <;> rfl
  have a : (![A 0,A 1]:Fin 2→Bool)=A := by
    funext k
    fin_cases k <;> rfl
  have cert := one_two_certificate (C 0 1) (C 0 2) (C 1 2) (T 0 0) (T 0 1) (T 0 2)
    (T 1 0) (T 1 1) (T 1 2) (T 2 0) (T 2 1) (T 2 2) (A 0) (A 1)
  rw [c,t,a] at cert
  exact cert valid

private theorem plan12a :
    ∀ (y : Fin 2) (i j k : Fin 3), i≠j → i≠k → j≠k →
      let A := insert s (insert a (insert x12 D))
      let B := insert (y12 y) A
      let C := insert (c12 i) B
      let E := insert (c12 j) C
      let F := insert (c12 k) E
      let H := insert b F
      x12∉D ∧ a∉insert x12 D ∧ s∉insert a (insert x12 D) ∧
        y12 y∉A ∧ c12 i∉B ∧ c12 j∉C ∧ c12 k∉E ∧ b∉F ∧
        y12 (other y)∉H ∧ ∀ z,z∈insert (y12 (other y)) H := by decide

private theorem plan12b :
    ∀ (y : Fin 2) (i j k : Fin 3), i≠j → i≠k → j≠k →
      let A := insert s (insert b (insert (y12 y) D))
      let B := insert x12 A
      let C := insert (c12 i) B
      let E := insert a C
      let F := insert (c12 j) E
      let H := insert (c12 k) F
      y12 y∉D ∧ b∉insert (y12 y) D ∧ s∉insert b (insert (y12 y) D) ∧
        x12∉A ∧ c12 i∉B ∧ a∉C ∧ c12 j∉E ∧ c12 k∉F ∧
        y12 (other y)∉H ∧ ∀ z,z∈insert (y12 (other y)) H := by
  intro y i j k ij ik jk
  fin_cases y <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first | exact (ij rfl).elim | exact (ik rfl).elim | exact (jk rfl).elim | decide

structure Board12 (G : SimpleGraph V) [DecidableRel G.Adj] (A : Fin 2→Bool) (L R : Finset V) : Prop where
  sa : G.Adj s a
  sb : G.Adj s b
  xa : G.Adj a x12
  yb : ∀ u,G.Adj b (y12 u)
  commonA : ∀ k,G.Adj a (c12 k)
  commonB : ∀ k,G.Adj b (c12 k)
  rootA : ∃ t∈L,G.Adj x12 t
  rootB : ∀ u,A u=true → ∃ t∈R,G.Adj (y12 u) t
  rootL : L⊆D
  rootR : R⊆D
  rootDis : Disjoint L R
  dark : ∀ t∈D,4≤(inside G D t).card
  valid : oneTwoModel (fun k i=>decide (G.Adj (c12 k) (c12 i))) (fun k i=>decide (G.Adj (c12 k) (e12 i))) A

theorem traceable_of_one_two_exclusive_zero_balanced {A : Fin 2→Bool} {L R : Finset V}
    (F : Board12 G A L R) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have cs (u v : Fin 3) :
      decide (G.Adj (c12 u) (c12 v))=decide (G.Adj (c12 v) (c12 u)) := by
    congr 1
    exact propext ⟨Adj.symm,Adj.symm⟩
  have cn (u : Fin 3) : decide (G.Adj (c12 u) (c12 u))=false := decide_eq_false_iff_not.mpr (G.loopless _)
  obtain ⟨y,i,j,k,ya,ij,ik,jk,tail⟩ := certificate12_fun _ _ A cs cn F.valid
  obtain ⟨l,ll,xl⟩ := F.rootA
  obtain ⟨r,rr,yr⟩ := F.rootB y ya
  have lr : l≠r := fun e=>disjoint_left.mp F.rootDis ll (e.symm ▸ rr)
  have path : RouteOn G D l r :=
    terminal_route_on_of_local_ore D (F.rootL ll) (F.rootR rr) lr (by
      intro p pm q qm _ _
      have h := F.dark p pm
      have j := F.dark q qm
      have d := dark7
      omega)
  rcases tail with ⟨iy,ji,kj⟩|⟨ix,kj,ky⟩
  · obtain ⟨n1,n2,n3,n4,n5,n6,n7,n8,n9,all⟩ := plan12a y i j k ij ik jk
    have eiy : G.Adj (c12 i) (y12 y) := by
      have h : G.Adj (c12 i) (e12 (yIndex y)) := of_decide_eq_true iy
      rwa [y12_index] at h
    have r1 := path.prefix xl n1
    have r2 := r1.prefix F.xa n2
    have r3 := r2.prefix F.sa n3
    have r4 := r3.suffix yr.symm n4
    have r5 := r4.suffix eiy.symm n5
    have r6 := r5.suffix (of_decide_eq_true ji) n6
    have r7 := r6.suffix (of_decide_eq_true kj) n7
    have r8 := r7.suffix (F.commonB k).symm n8
    obtain ⟨p,pp,ps⟩ := r8.suffix (F.yb (other y)) n9
    exact ⟨s,_,p,pp,fun z=>(ps z).mpr (all z)⟩
  obtain ⟨n1,n2,n3,n4,n5,n6,n7,n8,n9,all⟩ := plan12b y i j k ij ik jk
  have ey : G.Adj (c12 k) (y12 (other y)) := by
    have h : G.Adj (c12 k) (e12 (yIndex (other y))) := of_decide_eq_true ky
    rwa [y12_index] at h
  have ex : G.Adj (c12 i) x12 := of_decide_eq_true ix
  have r1 := path.reverse.prefix yr n1
  have r2 := r1.prefix (F.yb y) n2
  have r3 := r2.prefix F.sb n3
  have r4 := r3.suffix xl.symm n4
  have r5 := r4.suffix ex.symm n5
  have r6 := r5.suffix (F.commonA i).symm n6
  have r7 := r6.suffix (F.commonA j) n7
  have r8 := r7.suffix (of_decide_eq_true kj) n8
  obtain ⟨p,pp,ps⟩ := r8.suffix ey n9
  exact ⟨s,_,p,pp,fun z=>(ps z).mpr (all z)⟩

#print axioms traceable_of_double_exclusive_zero_balanced
#print axioms traceable_of_one_two_exclusive_zero_balanced
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates
