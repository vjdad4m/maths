import PortHall189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath Graffiti189LongestPath.Rigidity
open Graffiti189LongestPath.WideWing Graffiti189LongestPath.PortHall
open Graffiti189LongestPath.OneSlack
open private Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.mem_omittedStar from Rigidity189
open private Graffiti189LongestPath.WideWing.terminalOre from WideWing189
set_option warningAsError true
namespace Graffiti189LongestPath.DenseStar
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A large induced subgraph with a universal vertex is Hamilton-connected
under the global radius-two cap. No upper bound on the full graph is used. -/
theorem universal_terminal_paths (hc : G.Connected) (A : Finset V) (d : Nat)
    (cap : ∀ v, (DistanceTwo G v).card ≤ d)
    (large : 2*d+3≤A.card)
    {x : V} (root : ∀ z∈A, z = x ∨ G.Adj x z)
    {u v : V} (hu : u∈A) (hv : v∈A) (ne : u≠v) :
    ∃ q : G.Walk u v, q.IsPath ∧ (∀ w∈q.support,w∈A) ∧ q.length+1=A.card := by
  classical
  let W := ↥(A : Set V)
  let J := G.induce (A : Set V)
  have ac : Fintype.card W = A.card := Fintype.card_coe _
  have bound (w : W) : A.card ≤ J.degree w + d + 1 := by
    let N : Finset W := univ.filter (fun z => z ≠ w ∧ ¬J.Adj w z)
    have sub : N.image Subtype.val ⊆ DistanceTwo G w.val := by
      intro t ht
      obtain ⟨z,hz,rfl⟩ := mem_image.mp ht
      obtain ⟨hneq,hno⟩ := (mem_filter.mp hz).2
      have ne' : w.val≠z.val := fun he => hneq (Subtype.ext he.symm)
      have no' : ¬G.Adj w.val z.val := hno
      rcases root w.val w.property with e|ex
      · rcases root z.val z.property with e'|e'
        · exact (ne' (e.trans e'.symm)).elim
        · exact (no' (e.symm ▸ e')).elim
      rcases root z.val z.property with e|ez
      · exact (no' (e.symm ▸ ex.symm)).elim
      exact Graffiti189LongestPath.mem_distanceTwo.mpr
        (Graffiti189LongestPath.dist_two hc ne' no' ex.symm ez)
    have cd := card_le_card sub
    rw [card_image_of_injective N Subtype.val_injective] at cd
    have cover : (univ : Finset W) ⊆ insert w (J.neighborFinset w ∪ N) := by
      intro z _
      by_cases e : z=w
      · exact mem_insert.mpr (Or.inl e)
      by_cases ed : J.Adj w z
      · exact mem_insert.mpr (Or.inr (mem_union.mpr (Or.inl ((J.mem_neighborFinset w z).mpr ed))))
      · exact mem_insert.mpr (Or.inr (mem_union.mpr (Or.inr (mem_filter.mpr ⟨mem_univ _,e,ed⟩))))
    have c₁ := card_le_card cover
    have c₂ := card_insert_le w (J.neighborFinset w ∪ N)
    have c₃ := card_union_le (J.neighborFinset w) N
    rw [card_univ,ac] at c₁
    rw [J.card_neighborFinset_eq_degree] at c₃
    have c₄ := cap w.val
    omega
  have ore (s t : W) (_ : s≠t) (_ : ¬J.Adj s t) :
      Fintype.card W+1≤J.degree s+J.degree t := by
    have bs := bound s
    have bt := bound t
    omega
  let u' : W := ⟨u,hu⟩
  let v' : W := ⟨v,hv⟩
  obtain ⟨q,hq,all⟩ := Graffiti189LongestPath.WideWing.terminalOre (G:=J) ore
    (show u'≠v' from fun h => ne (congrArg Subtype.val h))
  let f : J →g G := ⟨Subtype.val,fun e => e⟩
  refine ⟨q.map f,map_isPath_of_injective Subtype.val_injective hq,?_,?_⟩
  · intro w hw
    rw [support_map] at hw
    obtain ⟨s,_,rfl⟩ := List.mem_map.mp hw
    exact s.property
  · have es : q.support.toFinset = univ := ext fun w =>
      ⟨fun _ => mem_univ _,fun _ => List.mem_toFinset.mpr (all w)⟩
    have c := congrArg card es
    rw [List.toFinset_card_of_nodup hq.support_nodup,length_support,card_univ,ac] at c
    simpa only [length_map] using c

/-- In the separated-pair case, a large omitted star can replace the interval
between any two of its boundary ports on the path, not just x's own pins. -/
theorem large_star_boundary_gap (hc : G.Connected) (k : Nat)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (cap : ∀ v, (EvenFrom G v).card≤k+3)
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x∉p.support)
    (hy : y∉p.support) (xy : G.Adj x y)
    (high : k+2≤G.degree x) (two : (Pins p x).card=2) (sep : PairedPins p x=∅)
    (large : 2*(k+2)+3≤(OmittedStar p x).card)
    {i j : Nat} (ij : i<j) (jp : j<p.length)
    (hi : p.getVert i∈External G (OmittedStar p x))
    (hj : p.getVert j∈External G (OmittedStar p x)) :
    i+(OmittedStar p x).card+1≤j := by
  classical
  let A := OmittedStar p x
  let B := External G A
  obtain ⟨f,inj,nb⟩ := separated_double_port_matching hc k conn hp hx hy xy high (cap x) two sep
  let u : ↥(B : Set V) := ⟨p.getVert i,hi⟩
  let v : ↥(B : Set V) := ⟨p.getVert j,hj⟩
  have nuv : u ≠ v := by
    intro e
    have he := congrArg Subtype.val e
    have eq := (Walk.IsPath.getVert_injOn hp.1) (by omega : i≤p.length) (by omega : j≤p.length) he
    omega
  have pins {l : Nat} (hl : l<p.length) (b : ↥(B : Set V)) (e : b.val=p.getVert l) :
      l∈Pins p (f b) :=
    mem_filter.mpr ⟨mem_range.mpr hl,e ▸ (nb b).2.symm⟩
  obtain ⟨q,hq,qa,ql⟩ := universal_terminal_paths hc A (k+2)
    (fun z => distanceTwo_le_of_even (k+2) z (cap z)) large
    (fun z hz => (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp hz).2)
    (nb u).1 (nb v).1 (fun e => nuv (inj e))
  have gap := terminal_length_le_gap hp (pins (by omega) u rfl) (pins jp v rfl) ij q hq
    (fun z hz => (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp (qa z hz)).1)
  change q.length+1=(OmittedStar p x).card at ql
  omega
#print axioms universal_terminal_paths
#print axioms large_star_boundary_gap
end Graffiti189LongestPath.DenseStar
