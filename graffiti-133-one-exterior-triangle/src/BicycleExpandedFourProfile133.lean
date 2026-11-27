import BicycleExpandedThreeProfiles133
namespace Graffiti133TriangleCritical
open SimpleGraph Finset Graffiti133 Graffiti133Bicycle
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
variable {V : Type*} {G : SimpleGraph V}

structure TrianglePortRoute (G : SimpleGraph V) (S : Finset V) (l r : V) where
  n : ℕ
  nontriv : 2 ≤ n
  f : Fin n → V
  path : InducedPath G f
  exterior : ∀ i, f i∉S
  attaches : ∀ v∈S, ∀ i, G.Adj v (f i) ↔ (v=l ∧ i.val=0) ∨ (v=r ∧ i.val+1=n)

structure TrianglePortPair (G : SimpleGraph V) (S : Finset V) (a b c d : V) where
  one : TrianglePortRoute G S a b
  two : TrianglePortRoute G S c d
  disjoint : ∀ i j, one.f i ≠ two.f j
  anticomplete : ∀ i j, ¬ G.Adj (one.f i) (two.f j)

variable [Fintype V]

namespace TrianglePortRoute

def reverse {S : Finset V} {a b : V} (P : TrianglePortRoute G S a b) :
    TrianglePortRoute G S b a where
  n := P.n
  nontriv := P.nontriv
  f := P.f ∘ Fin.rev
  path := ⟨P.path.1.comp Fin.rev_injective,by
    intro i j ij
    change G.Adj (P.f i.rev) (P.f j.rev) ↔ i.val+1=j.val
    rw [induced_adj_both_orders P.path]
    simp only [Fin.val_rev]
    change i.val < j.val at ij
    have hi := i.isLt
    have hj := j.isLt
    omega⟩
  exterior := fun i => P.exterior i.rev
  attaches := by
    intro v hv i
    change G.Adj v (P.f i.rev) ↔ _
    rw [P.attaches v hv]
    have hi := i.isLt
    have hp := P.nontriv
    have e₀ : i.rev.val=0 ↔ i.val+1=P.n := by simp only [Fin.val_rev]; omega
    have e₁ : i.rev.val+1=P.n ↔ i.val=0 := by simp only [Fin.val_rev]; omega
    rw [e₀,e₁,or_comm]
end TrianglePortRoute

namespace TrianglePortPair
variable {S : Finset V} {a b c d : V}
def swap (P : TrianglePortPair G S a b c d) : TrianglePortPair G S c d a b :=
  ⟨P.two,P.one,fun i j e => P.disjoint j i e.symm,fun i j e => P.anticomplete j i e.symm⟩
def flipLeft (P : TrianglePortPair G S a b c d) : TrianglePortPair G S b a c d :=
  ⟨P.one.reverse,P.two,fun i j => P.disjoint i.rev j,fun i j => P.anticomplete i.rev j⟩
def flipRight (P : TrianglePortPair G S a b c d) : TrianglePortPair G S a b d c :=
  ⟨P.one,P.two.reverse,fun i j => P.disjoint i j.rev,fun i j => P.anticomplete i j.rev⟩
end TrianglePortPair

private def orient (q : Fin 4 → Fin 3) (s x y : Bool) : Fin 4 → Fin 3 :=
  let a := if s then q 2 else q 0
  let b := if s then q 3 else q 1
  let c := if s then q 0 else q 2
  let d := if s then q 1 else q 3
  ![if x then b else a, if x then a else b, if y then d else c, if y then c else d]

private def countAt (q : Fin 4 → Fin 3) (i : Fin 3) : ℕ :=
  (Finset.univ.filter fun j => q j=i).card

private lemma orient_ports : ∀ q : Fin 4 → Fin 3, countAt q 0≤2 → countAt q 1≤1 → countAt q 2≤1 →
    ∃ s x y : Bool, (∀ i, orient q s x y i=(![0,0,1,2] : Fin 4 → Fin 3) i) ∨
      (∀ i, orient q s x y i=(![0,1,0,2] : Fin 4 → Fin 3) i) := by decide

private def orientPair {S : Finset V} {t : Fin 3 → V} {q : Fin 4 → Fin 3}
    (P : TrianglePortPair G S (t (q 0)) (t (q 1)) (t (q 2)) (t (q 3)))
    (s x y : Bool) :
    TrianglePortPair G S (t (orient q s x y 0)) (t (orient q s x y 1))
      (t (orient q s x y 2)) (t (orient q s x y 3)) := by
  cases s <;> cases x <;> cases y
  · exact P
  · exact P.flipRight
  · exact P.flipLeft
  · exact P.flipLeft.flipRight
  · exact P.swap
  · exact P.swap.flipRight
  · exact P.swap.flipLeft
  · exact P.swap.flipLeft.flipRight


private def headIdx {n : ℕ} (ge : 2≤n) : Fin n := ⟨0,by omega⟩
private def endIdx {n : ℕ} (ge : 2≤n) : Fin n := ⟨n-1,by omega⟩

private lemma head_ne_end {n : ℕ} (ge : 2≤n) : headIdx ge≠endIdx ge := by
  intro h
  have e := congrArg Fin.val h
  change 0=n-1 at e
  omega

section Extraction
variable [DecidableEq V] [DecidableRel G.Adj]

private def outsideGet {S : Finset V} (u : Option {x : V // x∉S}) (h : u≠none) : {x : V // x∉S} :=
  u.get (by cases u <;> simp_all)

private lemma some_get {S : Finset V} (u : Option {x : V // x∉S}) (h : u≠none) :
    some (outsideGet u h)=u := by
  cases u
  · exact (h rfl).elim
  · rfl

private def hubGet {S : Finset V} {T : Finset (Option {x : V // x∉S})}
    (P : HubPath (TriangleContraction G S) none T) (off : none∉T) (i : Fin P.n) :
    {x : V // x∉S} := outsideGet (P.f i).val (fun eq => off (eq ▸ (P.f i).property))

private lemma hubSome {S : Finset V} {T : Finset (Option {x : V // x∉S})}
    (P : HubPath (TriangleContraction G S) none T) (off : none∉T) (i : Fin P.n) :
    some (hubGet P off i)=(P.f i).val := some_get _ _

private def hubFn {S : Finset V} {T : Finset (Option {x : V // x∉S})}
    (P : HubPath (TriangleContraction G S) none T) (off : none∉T) (i : Fin P.n) : V :=
  (hubGet P off i).val

private theorem hubFn_path {S : Finset V} {T : Finset (Option {x : V // x∉S})}
    (P : HubPath (TriangleContraction G S) none T) (off : none∉T) :
    InducedPath G (hubFn P off) := by
  constructor
  · intro i j e
    apply P.path.1
    apply Subtype.ext
    rw [←hubSome P off,←hubSome P off]
    exact congrArg some (Subtype.ext e)
  · intro i j lt
    have e := P.path.2 i j lt
    change (TriangleContraction G S).Adj (P.f i).val (P.f j).val ↔ i.val+1=j.val at e
    rw [←hubSome P off,←hubSome P off] at e
    exact e

private theorem hub_has_port {S : Finset V} {T : Finset (Option {x : V // x∉S})}
    (P : HubPath (TriangleContraction G S) none T) (off : none∉T) (i : Fin P.n)
    (hi : i.val=0 ∨ i.val+1=P.n) : ∃ v∈S,G.Adj v (hubFn P off i) := by
  have e := (P.attached i).mpr hi
  rw [←hubSome P off] at e
  exact e

private def route_from_ports (h4 : FourCycleFree G) (a b c : V)
    (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a)
    {T : Finset (Option {x : V // x∉({a,b,c}:Finset V)})}
    (P : HubPath (TriangleContraction G ({a,b,c}:Finset V)) none T) (off : none∉T)
    {l r : V} (hl : l∈({a,b,c}:Finset V)) (hr : r∈({a,b,c}:Finset V))
    (el : G.Adj l (hubFn P off (headIdx P.nontriv)))
    (er : G.Adj r (hubFn P off (endIdx P.nontriv))) :
    TrianglePortRoute G ({a,b,c}:Finset V) l r where
  n := P.n
  nontriv := P.nontriv
  f := hubFn P off
  path := hubFn_path P off
  exterior := fun i => (hubGet P off i).property
  attaches := by
    intro v hv i
    constructor
    · intro e
      have e' : (TriangleContraction G ({a,b,c}:Finset V)).Adj none (P.f i).val := by
        rw [←hubSome P off]
        exact ⟨v,hv,e⟩
      rcases (P.attached i).mp e' with z | w
      · have eq : i=headIdx P.nontriv := Fin.ext z
        have le : G.Adj l (hubFn P off i) := eq.symm ▸ el
        exact Or.inl ⟨triangle_single_external_neighbor G h4 a b c ab bc ca _
          (hubGet P off i).property v l hv hl e.symm le.symm,z⟩
      · have eq : i=endIdx P.nontriv := by
          apply Fin.ext
          change i.val=P.n-1
          omega
        have re : G.Adj r (hubFn P off i) := eq.symm ▸ er
        exact Or.inr ⟨triangle_single_external_neighbor G h4 a b c ab bc ca _
          (hubGet P off i).property v r hv hr e.symm re.symm,w⟩
    · rintro (⟨rfl,z⟩ | ⟨rfl,w⟩)
      · have eq : i=headIdx P.nontriv := Fin.ext z
        exact eq.symm ▸ el
      · have eq : i=endIdx P.nontriv := by
          apply Fin.ext
          change i.val=P.n-1
          omega
        exact eq.symm ▸ er


private theorem exterior_count_le_degree (S T : Finset V) {v u w : V}
    (off : ∀ x∈T, x∉S) (insideU : u∈S) (insideW : w∈S) (ne : u≠w)
    (first : G.Adj v u) (second : G.Adj v w)
    (att : ∀ x∈T,G.Adj v x) : T.card+2 ≤ G.degree v := by
  classical
  have sep : Disjoint T ({u,w}:Finset V) := Finset.disjoint_left.mpr fun x hx hu => by
    have m : x=u ∨ x=w := by simpa using hu
    exact (off x hx) (m.elim (fun e => e.symm ▸ insideU) (fun e => e.symm ▸ insideW))
  have sub : T ∪ ({u,w}:Finset V) ⊆ G.neighborFinset v := by
    intro x hx
    apply (G.mem_neighborFinset _ _).mpr
    rcases Finset.mem_union.mp hx with hx | hx
    · exact att _ hx
    · have m : x=u ∨ x=w := by simpa using hx
      rcases m with rfl | rfl
      · exact first
      · exact second
  have bound := Finset.card_le_card sub
  rwa [Finset.card_union_of_disjoint sep,Finset.card_pair ne,G.card_neighborFinset_eq_degree] at bound

/-- Lift the two hub routes in a contracted triangle and normalize the
four attachment ports. No edges between route interiors are introduced. -/
theorem triangle_figure_normalize (h4 : FourCycleFree G) (a b c : V)
    (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a)
    (da : G.degree a=4) (db : G.degree b=3) (dc : G.degree c=3)
    (P : TwoHubPaths (TriangleContraction G ({a,b,c}:Finset V)) none) :
    Nonempty (TrianglePortPair G ({a,b,c}:Finset V) a a b c) ∨
    Nonempty (TrianglePortPair G ({a,b,c}:Finset V) a b a c) := by
  classical
  let S : Finset V := {a,b,c}
  let f := hubFn P.one P.offS
  let g := hubFn P.two P.offT
  let d : Fin 4 → V :=
    ![f (headIdx P.one.nontriv),f (endIdx P.one.nontriv),
      g (headIdx P.two.nontriv),g (endIdx P.two.nontriv)]
  let t : Fin 3 → V := ![a,b,c]
  have inS (i : Fin 3) : t i∈S := by fin_cases i <;> simp [S,t]
  have td : ∀ x∈S, ∃ i : Fin 3, t i=x := by
    intro x hx
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
  have start (n : ℕ) (ge : 2≤n) : (headIdx ge).val=0 := rfl
  have last (n : ℕ) (ge : 2≤n) : (endIdx ge).val+1=n := by
    change n-1+1=n
    omega
  have hd (i : Fin 4) : ∃ x∈S,G.Adj x (d i) := by
    fin_cases i
    · exact hub_has_port P.one P.offS _ (Or.inl (start _ _))
    · exact hub_has_port P.one P.offS _ (Or.inr (last _ _))
    · exact hub_has_port P.two P.offT _ (Or.inl (start _ _))
    · exact hub_has_port P.two P.offT _ (Or.inr (last _ _))
  have each (i : Fin 4) : ∃ j : Fin 3, G.Adj (t j) (d i) := by
    obtain ⟨x,hx,e⟩ := hd i
    obtain ⟨j,rfl⟩ := td x hx
    exact ⟨j,e⟩
  let q (i : Fin 4) : Fin 3 := Classical.choose (each i)
  have pq (i : Fin 4) : G.Adj (t (q i)) (d i) := Classical.choose_spec (each i)
  have noCross (i : Fin P.one.n) (j : Fin P.two.n) : ¬ G.Adj (f i) (g j) := by
    intro e
    apply P.noCross _ (P.one.f i).property _ (P.two.f j).property
    rw [←hubSome P.one P.offS i,←hubSome P.two P.offT j]
    exact e
  have distinct (i : Fin P.one.n) (j : Fin P.two.n) : f i≠g j := by
    intro e
    have eq : (P.one.f i).val=(P.two.f j).val := by
      rw [←hubSome P.one P.offS i,←hubSome P.two P.offT j]
      exact congrArg some (Subtype.ext e)
    exact Finset.disjoint_left.mp P.sep (P.one.f i).property (eq.symm ▸ (P.two.f j).property)
  let U : TrianglePortPair G S (t (q 0)) (t (q 1)) (t (q 2)) (t (q 3)) :=
    ⟨route_from_ports h4 a b c ab bc ca P.one P.offS (inS _) (inS _) (pq 0) (pq 1),
      route_from_ports h4 a b c ab bc ca P.two P.offT (inS _) (inS _) (pq 2) (pq 3),
      distinct,noCross⟩
  have ha : f (headIdx P.one.nontriv) ≠ f (endIdx P.one.nontriv) :=
    (hubFn_path P.one P.offS).1.ne (head_ne_end _)
  have hb : g (headIdx P.two.nontriv) ≠ g (endIdx P.two.nontriv) :=
    (hubFn_path P.two P.offT).1.ne (head_ne_end _)
  have dinj : Function.Injective d := List.nodup_ofFn.mp (by
    simpa [d,List.ofFn_succ] using (show
      [f (headIdx P.one.nontriv),f (endIdx P.one.nontriv),
        g (headIdx P.two.nontriv),g (endIdx P.two.nontriv)].Nodup by simp [ha,hb,distinct]))
  have doff (i : Fin 4) : d i∉S := by
    fin_cases i
    · exact (hubGet P.one P.offS _).property
    · exact (hubGet P.one P.offS _).property
    · exact (hubGet P.two P.offT _).property
    · exact (hubGet P.two P.offT _).property
  let A (j : Fin 3) := (Finset.univ.filter fun i => q i=j).image d
  have off (j : Fin 3) (x : V) (hx : x∈A j) : x∉S := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact doff i
  have bound (j : Fin 3) (x : V) (hx : x∈A j) : G.Adj (t j) x := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    have eq := (Finset.mem_filter.mp hi).2
    exact eq ▸ pq i
  have size (j : Fin 3) : (A j).card=countAt q j :=
    Finset.card_image_of_injective _ dinj
  have cap0 : countAt q 0≤2 := by
    have h := exterior_count_le_degree S (A 0) (off 0) (inS 1) (inS 2) bc.ne ab ca.symm (bound 0)
    rw [size,da] at h
    omega
  have cap1 : countAt q 1≤1 := by
    have h := exterior_count_le_degree S (A 1) (off 1) (inS 0) (inS 2) ca.ne.symm ab.symm bc (bound 1)
    rw [size,db] at h
    omega
  have cap2 : countAt q 2≤1 := by
    have h := exterior_count_le_degree S (A 2) (off 2) (inS 0) (inS 1) ab.ne ca bc.symm (bound 2)
    rw [size,dc] at h
    omega
  obtain ⟨s,x,y,k|k⟩ := orient_ports q cap0 cap1 cap2
  · exact Or.inl ⟨by simpa [t,k 0,k 1,k 2,k 3] using orientPair U s x y⟩
  · exact Or.inr ⟨by simpa [t,k 0,k 1,k 2,k 3] using orientPair U s x y⟩

end Extraction

#print axioms triangle_figure_normalize
end Graffiti133TriangleCritical


namespace Graffiti133ExpandedTriangle
open SimpleGraph Graffiti133 Graffiti133NoFive Graffiti133Bicycle
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev FigIndex (a b : Nat) := Sum (Fin 3) (Sum (Fin a) (Fin b))

def figPort (pattern side endp : Bool) : Fin 3 :=
  match pattern,side,endp with
  | false,false,_ => 0
  | false,true,false => 1
  | false,true,true => 2
  | true,false,false => 0
  | true,false,true => 1
  | true,true,false => 0
  | true,true,true => 2

def figAdj (a b : Nat) (pattern : Bool) : FigIndex a b → FigIndex a b → Prop
  | .inl i,.inl j => i≠j
  | .inl q,.inr (.inl i) | .inr (.inl i),.inl q =>
      (i.val=0 ∧ q=figPort pattern false false) ∨ (i.val+1=a ∧ q=figPort pattern false true)
  | .inl q,.inr (.inr i) | .inr (.inr i),.inl q =>
      (i.val=0 ∧ q=figPort pattern true false) ∨ (i.val+1=b ∧ q=figPort pattern true true)
  | .inr (.inl i),.inr (.inl j) => i.val+1=j.val ∨ j.val+1=i.val
  | .inr (.inr i),.inr (.inr j) => i.val+1=j.val ∨ j.val+1=i.val
  | _,_ => False

instance (a b : Nat) (pattern : Bool) (i j : FigIndex a b) :
    Decidable (figAdj a b pattern i j) := by
  rcases i with i|(i|i) <;> rcases j with j|(j|j) <;> unfold figAdj <;> infer_instance

def figNum (a b : Nat) (i : Fin (3+a+b)) : FigIndex a b :=
  if h : i.val<3 then .inl ⟨i.val,h⟩ else
  if h' : i.val<3+a then .inr (.inl ⟨i.val-3,by omega⟩) else
  .inr (.inr ⟨i.val-(3+a),by have := i.isLt; omega⟩)

def figIdx (a b i : Nat) : FigIndex a b := figNum a b ⟨i%(3+a+b),Nat.mod_lt _ (by omega)⟩

def FigIndex.onTriangle {a b : Nat} : FigIndex a b → Bool
  | .inl _ => true
  | .inr _ => false

def figWitness (p : Bool) (a b : Nat) : List Nat → Prop
  | [0,i,j,x,y] =>
      figIdx a b i≠figIdx a b j ∧ figIdx a b x≠figIdx a b y ∧
      figAdj a b p (figIdx a b i) (figIdx a b x) ∧ figAdj a b p (figIdx a b j) (figIdx a b x) ∧
      figAdj a b p (figIdx a b i) (figIdx a b y) ∧ figAdj a b p (figIdx a b j) (figIdx a b y)
  | 1::L =>
      (∀ i j : Fin 9, figIdx a b (L.getD i.val 0)=figIdx a b (L.getD j.val 0) → i=j) ∧
      ∀ i j : Fin 9, i<j →
        (figAdj a b p (figIdx a b (L.getD i.val 0)) (figIdx a b (L.getD j.val 0)) ↔ i.val+1=j.val)
  | [2,i,j,k] =>
      (figIdx a b k).onTriangle=false ∧ figAdj a b p (figIdx a b i) (figIdx a b j) ∧
        figAdj a b p (figIdx a b j) (figIdx a b k) ∧ figAdj a b p (figIdx a b k) (figIdx a b i)
  | _ => False

instance (p : Bool) (a b : Nat) (L : List Nat) : Decidable (figWitness p a b L) := by
  unfold figWitness
  split <;> infer_instance

def figAtlas : List ((Bool×Nat×Nat)×List Nat) := [
 ((true,2,2),[0,3,1,0,4]),
 ((true,2,3),[0,3,1,0,4]),
 ((true,2,4),[0,3,1,0,4]),
 ((true,2,5),[0,3,1,0,4]),
 ((true,2,6),[0,3,1,0,4]),
 ((true,2,7),[0,3,1,0,4]),
 ((true,2,8),[0,3,1,0,4]),
 ((true,3,2),[0,6,2,0,7]),
 ((true,3,4),[1,3,4,5,1,2,9,8,7,6]),
 ((true,3,5),[1,3,4,5,1,2,10,9,8,7]),
 ((true,3,6),[1,3,4,5,1,2,11,10,9,8]),
 ((true,3,7),[1,1,0,6,7,8,9,10,11,12]),
 ((true,3,8),[1,0,2,13,12,11,10,9,8,7]),
 ((true,4,2),[0,7,2,0,8]),
 ((true,4,3),[1,3,4,5,6,1,2,9,8,7]),
 ((true,4,4),[1,3,4,5,6,1,2,10,9,8]),
 ((true,4,5),[1,3,4,5,6,1,2,11,10,9]),
 ((true,4,6),[1,3,4,5,6,1,2,12,11,10]),
 ((true,4,7),[1,1,0,7,8,9,10,11,12,13]),
 ((true,4,8),[1,0,2,14,13,12,11,10,9,8]),
 ((true,5,2),[0,8,2,0,9]),
 ((true,5,3),[1,3,4,5,6,7,1,2,10,9]),
 ((true,5,4),[1,3,4,5,6,7,1,2,11,10]),
 ((true,5,5),[1,3,4,5,6,7,1,2,12,11]),
 ((true,5,6),[1,3,4,5,6,7,1,2,13,12]),
 ((true,5,7),[1,1,0,8,9,10,11,12,13,14]),
 ((true,5,8),[1,0,2,15,14,13,12,11,10,9]),
 ((true,6,2),[0,9,2,0,10]),
 ((true,6,3),[1,3,4,5,6,7,8,1,2,11]),
 ((true,6,4),[1,3,4,5,6,7,8,1,2,12]),
 ((true,6,5),[1,3,4,5,6,7,8,1,2,13]),
 ((true,6,6),[1,3,4,5,6,7,8,1,2,14]),
 ((true,6,7),[1,1,0,9,10,11,12,13,14,15]),
 ((true,6,8),[1,0,2,16,15,14,13,12,11,10]),
 ((true,7,2),[0,10,2,0,11]),
 ((true,7,3),[1,2,0,3,4,5,6,7,8,9]),
 ((true,7,4),[1,2,0,3,4,5,6,7,8,9]),
 ((true,7,5),[1,2,0,3,4,5,6,7,8,9]),
 ((true,7,6),[1,2,0,3,4,5,6,7,8,9]),
 ((true,7,7),[1,1,0,10,11,12,13,14,15,16]),
 ((true,7,8),[1,0,2,17,16,15,14,13,12,11]),
 ((true,8,2),[0,11,2,0,12]),
 ((true,8,3),[1,0,1,10,9,8,7,6,5,4]),
 ((true,8,4),[1,0,1,10,9,8,7,6,5,4]),
 ((true,8,5),[1,0,1,10,9,8,7,6,5,4]),
 ((true,8,6),[1,0,1,10,9,8,7,6,5,4]),
 ((true,8,7),[1,0,1,10,9,8,7,6,5,4]),
 ((true,8,8),[1,0,1,10,9,8,7,6,5,4]),
 ((false,2,2),[0,5,2,1,6]),
 ((false,2,3),[2,0,3,4]),
 ((false,2,4),[2,0,3,4]),
 ((false,2,5),[2,0,3,4]),
 ((false,2,6),[2,0,3,4]),
 ((false,2,7),[2,0,3,4]),
 ((false,2,8),[2,0,3,4]),
 ((false,3,2),[0,4,0,3,5]),
 ((false,3,3),[0,4,0,3,5]),
 ((false,3,4),[0,4,0,3,5]),
 ((false,3,5),[0,4,0,3,5]),
 ((false,3,6),[0,4,0,3,5]),
 ((false,3,7),[0,4,0,3,5]),
 ((false,3,8),[0,4,0,3,5]),
 ((false,4,2),[0,7,2,1,8]),
 ((false,4,4),[1,4,5,6,0,1,7,8,9,10]),
 ((false,4,5),[1,4,3,0,1,7,8,9,10,11]),
 ((false,4,6),[1,3,0,1,7,8,9,10,11,12]),
 ((false,4,7),[1,0,1,7,8,9,10,11,12,13]),
 ((false,4,8),[1,0,1,7,8,9,10,11,12,13]),
 ((false,5,2),[0,8,2,1,9]),
 ((false,5,3),[1,4,5,6,7,0,1,8,9,10]),
 ((false,5,4),[1,4,5,6,7,0,1,8,9,10]),
 ((false,5,5),[1,4,3,0,1,8,9,10,11,12]),
 ((false,5,6),[1,3,0,1,8,9,10,11,12,13]),
 ((false,5,7),[1,0,1,8,9,10,11,12,13,14]),
 ((false,5,8),[1,0,1,8,9,10,11,12,13,14]),
 ((false,6,2),[0,9,2,1,10]),
 ((false,6,3),[1,4,5,6,7,8,0,1,9,10]),
 ((false,6,4),[1,4,5,6,7,8,0,1,9,10]),
 ((false,6,5),[1,4,3,0,1,9,10,11,12,13]),
 ((false,6,6),[1,3,0,1,9,10,11,12,13,14]),
 ((false,6,7),[1,0,1,9,10,11,12,13,14,15]),
 ((false,6,8),[1,0,1,9,10,11,12,13,14,15]),
 ((false,7,2),[0,10,2,1,11]),
 ((false,7,3),[1,4,5,6,7,8,9,0,1,10]),
 ((false,7,4),[1,4,5,6,7,8,9,0,1,10]),
 ((false,7,5),[1,4,3,0,1,10,11,12,13,14]),
 ((false,7,6),[1,3,0,1,10,11,12,13,14,15]),
 ((false,7,7),[1,0,1,10,11,12,13,14,15,16]),
 ((false,7,8),[1,0,1,10,11,12,13,14,15,16]),
 ((false,8,2),[0,11,2,1,12]),
 ((false,8,3),[1,1,0,3,4,5,6,7,8,9]),
 ((false,8,4),[1,1,0,3,4,5,6,7,8,9]),
 ((false,8,5),[1,1,0,3,4,5,6,7,8,9]),
 ((false,8,6),[1,1,0,3,4,5,6,7,8,9]),
 ((false,8,7),[1,0,1,11,12,13,14,15,16,17]),
 ((false,8,8),[1,0,1,11,12,13,14,15,16,17])
]
def figLookup (p : Bool) (a b : Nat) := (figAtlas.lookup (p,a,b)).getD []
def figGood (p : Bool) (a b : Nat) : Prop := (p=false ∧ a=4 ∧ b=3) ∨ (p=true ∧ a=3 ∧ b=3)

instance (p : Bool) (a b : Nat) : Decidable (figGood p a b) := by unfold figGood; infer_instance

theorem fig_checked : ∀ p : Bool, ∀ a b : Fin 9, 2≤a.val → 2≤b.val →
    figGood p a.val b.val ∨ figWitness p a.val b.val (figLookup p a.val b.val) := by decide

theorem fig_reject_lift {V : Type*} {G : SimpleGraph V} (p : Bool) (a b : Nat)
    (f : FigIndex a b→V) (fi : Function.Injective f)
    (adj : ∀ i j,G.Adj (f i) (f j) ↔ figAdj a b p i j)
    (four : FourCycleFree G) (nine : ¬∃ q : Fin 9→V,InducedPath G q)
    (tri : ∀ i j k, (FigIndex.onTriangle k=false) →
      G.Adj (f i) (f j) → G.Adj (f j) (f k) → G.Adj (f k) (f i) → False)
    (L : List Nat) (bad : figWitness p a b L) : False := by
  unfold figWitness at bad
  split at bad
  · obtain ⟨ne,ne2,e1,e2,e3,e4⟩ := bad
    exact ne2 (fi (four _ _ _ _ (fi.ne ne) ((adj _ _).mpr e1) ((adj _ _).mpr e2)
      ((adj _ _).mpr e3) ((adj _ _).mpr e4)))
  · exact nine ⟨_, fun i j eq=>bad.1 i j (fi eq),fun i j lt=>(adj _ _).trans (bad.2 i j lt)⟩
  · exact tri _ _ _ bad.1 ((adj _ _).mpr bad.2.1) ((adj _ _).mpr bad.2.2.1)
      ((adj _ _).mpr bad.2.2.2)
  · exact bad

theorem fig_good_lift {V : Type*} [Fintype V] {G : SimpleGraph V}
    (H : Hole G 7) (four : FourCycleFree G) (p : Bool) (a b : Nat)
    (f : FigIndex a b→V) (fi : Function.Injective f)
    (adj : ∀ i j,G.Adj (f i) (f j) ↔ figAdj a b p i j)
    (out : ∀ i,Outside H.c (f i))
    (single : ∀ i,∃ k,∀ j,G.Adj (f i) (H.c j) ↔ k=j)
    (good : figGood p a b) : ∃ q : Fin 9→V,InducedPath G q := by
  choose site attach using single
  rcases good with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
  · have numinj : ∀ i j : Fin 10, figNum 4 3 i=figNum 4 3 j → i=j := by decide
    have numadj : ∀ i j : Fin 10, figAdj 4 3 false (figNum 4 3 i) (figNum 4 3 j) ↔
        bit Triangle254.canonicalRows i.val j.val=true := by decide
    exact Triangle254.extension H four (f ∘ figNum 4 3) (fi.comp (fun _ _=>numinj _ _))
      (fun i=>out (figNum 4 3 i)) (site ∘ figNum 4 3) (fun i=>attach (figNum 4 3 i))
      (fun i j=>(adj _ _).trans (numadj i j))
  · have numinj : ∀ i j : Fin 9, figNum 3 3 i=figNum 3 3 j → i=j := by decide
    have numadj : ∀ i j : Fin 9, figAdj 3 3 true (figNum 3 3 i) (figNum 3 3 j) ↔
        bit Triangle344.canonicalRows i.val j.val=true := by decide
    exact Triangle344.extension H four (f ∘ figNum 3 3) (fi.comp (fun _ _=>numinj _ _))
      (fun i=>out (figNum 3 3 i)) (site ∘ figNum 3 3) (fun i=>attach (figNum 3 3 i))
      (fun i j=>(adj _ _).trans (numadj i j))

#print axioms fig_checked
#print axioms fig_reject_lift
#print axioms fig_good_lift
end Graffiti133ExpandedTriangle


namespace Graffiti133ExpandedTriangle
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Bicycle Graffiti133TriangleCritical
open scoped Classical
set_option linter.unusedSectionVars false
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A : SimpleGraph W}

theorem figure_routes_excluded
    (S : Finset V) (t : Fin 3→V) (ts : ∀ i,t i∈S) (ti : Function.Injective t)
    (tc : ∀ i j,i≠j→G.Adj (t i) (t j)) (pat : Bool)
    (P : TrianglePortPair G S (t (figPort pat false false)) (t (figPort pat false true))
      (t (figPort pat true false)) (t (figPort pat true true)))
    (only : ∀ x y z,G.Adj x y→G.Adj y z→G.Adj z x→z∈S)
    (emb : V→W) (ei : Function.Injective emb)
    (ind : ∀ x y,A.Adj (emb x) (emb y) ↔ G.Adj x y)
    (H : Hole A 7) (four : FourCycleFree A) (nine : ¬∃ p : Fin 9→W,InducedPath A p)
    (out : ∀ x,Outside H.c (emb x))
    (single : ∀ x,∃ k,∀ j,A.Adj (emb x) (H.c j) ↔ k=j) : False := by
  have fourG : FourCycleFree G := by
    intro u v x y ne ux vx uy vy
    exact ei (four _ _ _ _ (ei.ne ne) ((ind _ _).mpr ux) ((ind _ _).mpr vx) ((ind _ _).mpr uy) ((ind _ _).mpr vy))
  have nineG : ¬∃ p : Fin 9→V,InducedPath G p := by
    rintro ⟨p,h⟩
    exact nine ⟨emb ∘ p,ei.comp h.1,fun i j lt=>(ind _ _).trans (h.2 i j lt)⟩
  let a := P.one.n
  let b := P.two.n
  have a8 : a<9 := by
    by_contra! k
    exact nineG (Graffiti133Revisit.trim_path k P.one.path)
  have b8 : b<9 := by
    by_contra! k
    exact nineG (Graffiti133Revisit.trim_path k P.two.path)
  let f : FigIndex a b→V
    | .inl i => t i
    | .inr (.inl i) => P.one.f i
    | .inr (.inr i) => P.two.f i
  have fi : Function.Injective f := by
    rintro (i|(i|i)) (j|(j|j)) e
    · exact congrArg Sum.inl (ti e)
    · change t i=P.one.f j at e
      exact (P.one.exterior j (Eq.mp (congrArg (fun x=>x∈S) e) (ts i))).elim
    · change t i=P.two.f j at e
      exact (P.two.exterior j (Eq.mp (congrArg (fun x=>x∈S) e) (ts i))).elim
    · change P.one.f i=t j at e
      exact (P.one.exterior i (Eq.mp (congrArg (fun x=>x∈S) e.symm) (ts j))).elim
    · exact congrArg Sum.inr (congrArg Sum.inl (P.one.path.1 e))
    · exact (P.disjoint i j e).elim
    · change P.two.f i=t j at e
      exact (P.two.exterior i (Eq.mp (congrArg (fun x=>x∈S) e.symm) (ts j))).elim
    · exact (P.disjoint j i e.symm).elim
    · exact congrArg Sum.inr (congrArg Sum.inr (P.two.path.1 e))
  have adj (i j : FigIndex a b) : G.Adj (f i) (f j) ↔ figAdj a b pat i j := by
    rcases i with i|(i|i) <;> rcases j with j|(j|j)
    · exact ⟨fun e ne=>e.ne (congrArg t ne),tc i j⟩
    · change G.Adj (t i) (P.one.f j) ↔ _
      rw [P.one.attaches _ (ts i),figAdj]
      simp only [ti.eq_iff,and_comm,a,b]
    · change G.Adj (t i) (P.two.f j) ↔ _
      rw [P.two.attaches _ (ts i),figAdj]
      simp only [ti.eq_iff,and_comm,a,b]
    · change G.Adj (P.one.f i) (t j) ↔ _
      rw [G.adj_comm,P.one.attaches _ (ts j),figAdj]
      simp only [ti.eq_iff,and_comm,a,b]
    · exact induced_adj_both_orders P.one.path i j
    · exact ⟨fun e=>(P.anticomplete i j e).elim,False.elim⟩
    · change G.Adj (P.two.f i) (t j) ↔ _
      rw [G.adj_comm,P.two.attaches _ (ts j),figAdj]
      simp only [ti.eq_iff,and_comm,a,b]
    · exact ⟨fun e=>(P.anticomplete j i e.symm).elim,False.elim⟩
    · exact induced_adj_both_orders P.two.path i j
  have outside (k : FigIndex a b) (off : k.onTriangle=false) : f k∉S := by
    rcases k with k|(k|k)
    · contradiction
    · exact P.one.exterior k
    · exact P.two.exterior k
  rcases fig_checked pat ⟨a,a8⟩ ⟨b,b8⟩ P.one.nontriv P.two.nontriv with good|bad
  · exact nine (fig_good_lift H four pat a b (emb ∘ f) (ei.comp fi)
      (fun i j=>(ind _ _).trans (adj i j)) (fun i=>out (f i)) (fun i=>single (f i)) good)
  · exact fig_reject_lift pat a b f fi adj fourG nineG
      (fun i j k ko ij jk ki=>outside k ko (only _ _ _ ij jk ki)) _ bad

#print axioms figure_routes_excluded
end Graffiti133ExpandedTriangle


namespace Graffiti133ExpandedTriangle
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Bicycle Graffiti133TriangleCritical
open scoped Classical
set_option linter.unusedSectionVars false
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A : SimpleGraph W}

theorem four_three_three_excluded
    (a b c : V) (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a)
    (da : G.degree a=4) (db : G.degree b=3) (dc : G.degree c=3)
    (rest : ∀ x∉({a,b,c}:Finset V),G.degree x=2)
    (only : ∀ x y z,G.Adj x y→G.Adj y z→G.Adj z x→z∈({a,b,c}:Finset V))
    (emb : V→W) (ei : Function.Injective emb)
    (ind : ∀ x y,A.Adj (emb x) (emb y) ↔ G.Adj x y)
    (H : Hole A 7) (four : FourCycleFree A) (nine : ¬∃ p : Fin 9→W,InducedPath A p)
    (out : ∀ x,Outside H.c (emb x))
    (single : ∀ x,∃ k,∀ j,A.Adj (emb x) (H.c j) ↔ k=j) : False := by
  let S : Finset V := {a,b,c}
  let J := TriangleContraction G S
  have fourG : FourCycleFree G := by
    intro u v x y ne ux vx uy vy
    exact ei (four _ _ _ _ (ei.ne ne) ((ind _ _).mpr ux) ((ind _ _).mpr vx) ((ind _ _).mpr uy) ((ind _ _).mpr vy))
  have hubDeg : J.degree none=4 := by
    have e := triangle_hub_degree G fourG a b c ab bc ca
    change J.degree none+6=_ at e
    omega
  have outsideDeg (x : {x : V // x∉S}) : J.degree (some x)=G.degree x.val :=
    external_degree_in_contraction G S x (triangle_single_external_neighbor G fourG a b c ab bc ca _ x.property)
  have low (x : Option {x : V // x∉S}) (na : x≠none) : J.degree x=2 := by
    cases x with
    | none => exact (na rfl).elim
    | some x => exact (outsideDeg x).trans (rest _ x.property)
  obtain ⟨P⟩ := degree_four_single_branch_has_two_paths none hubDeg low
  let t : Fin 3→V := ![a,b,c]
  have ts (i : Fin 3) : t i∈S := by fin_cases i <;> simp [t,S]
  have ti : Function.Injective t := List.nodup_ofFn.mp (by
    simpa [t,List.ofFn_succ] using (show [a,b,c].Nodup by
      simp [ab.ne,bc.ne,ca.ne.symm]))
  have tc (i j : Fin 3) (ij : i≠j) : G.Adj (t i) (t j) := by
    fin_cases i <;> fin_cases j
    all_goals first | contradiction | exact ab | exact ab.symm | exact bc | exact bc.symm | exact ca | exact ca.symm
  rcases triangle_figure_normalize (G:=G) fourG a b c ab bc ca da db dc P with first|second
  · obtain ⟨R⟩ := first
    exact figure_routes_excluded S t ts ti tc false R only emb ei ind H four nine out single
  · obtain ⟨R⟩ := second
    exact figure_routes_excluded S t ts ti tc true R only emb ei ind H four nine out single

#print axioms four_three_three_excluded
end Graffiti133ExpandedTriangle
