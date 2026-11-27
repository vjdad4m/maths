import NestedCorePrivateCrossRows133

namespace Graffiti133PrivateCross
open SimpleGraph Finset Graffiti133 Graffiti133NoFive
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1100000
set_option maxRecDepth 100000
variable {V : Type*} {G : SimpleGraph V}

def embedCore (i : Fin 9) : Fin 18 := Fin.castLE (by decide) i
def embedPrivate (i : Fin 9) : Fin 18 := ⟨i.val+9,by have := i.isLt; omega⟩

def stitch (core priv : Fin 9→V) (i : Fin 18) : V :=
  if hi : i.val < 9 then core ⟨i.val,hi⟩ else priv ⟨i.val-9,by have := i.isLt; omega⟩

theorem stitch_injective {core priv : Fin 9→V} (ci : Function.Injective core)
    (dis : ∀ i j,priv i≠core j)
    (site : ∀ i j,G.Adj (priv i) (core j)↔i=j) : Function.Injective (stitch core priv) := by
  intro a b eq
  by_cases alo : a.val < 9 <;> by_cases blo : b.val < 9
  · rw [stitch,dif_pos alo,stitch,dif_pos blo] at eq
    exact Fin.ext (congrArg (fun i : Fin 9=>i.val) (ci eq))
  · rw [stitch,dif_pos alo,stitch,dif_neg blo] at eq
    exact (dis _ _ eq.symm).elim
  · rw [stitch,dif_neg alo,stitch,dif_pos blo] at eq
    exact (dis _ _ eq).elim
  · rw [stitch,dif_neg alo,stitch,dif_neg blo] at eq
    let i : Fin 9 := ⟨a.val-9,by have := a.isLt; omega⟩
    let j : Fin 9 := ⟨b.val-9,by have := b.isLt; omega⟩
    have ij : priv i=priv j := eq
    have adj := (site i i).mpr rfl
    have j_i := (site j i).mp (ij ▸ adj)
    have val : b.val-9=a.val-9 := congrArg Fin.val j_i
    exact Fin.ext (by omega)

theorem stitch_known_core_pairs {core priv : Fin 9→V} (m : Bool)
    (fit : ∀ a b,G.Adj (core a) (core b)↔base m (embedCore a) (embedCore b)=true)
    (site : ∀ i j,G.Adj (priv i) (core j)↔i=j) :
    ∀ a b : Fin 18, a.val < 9 ∨ b.val < 9 →
      (G.Adj (stitch core priv a) (stitch core priv b)↔base m a b=true) := by
  intro a b one
  by_cases alo : a.val < 9 <;> by_cases blo : b.val < 9
  · rw [stitch,dif_pos alo,stitch,dif_pos blo]
    exact fit ⟨a.val,alo⟩ ⟨b.val,blo⟩
  · rw [stitch,dif_pos alo,stitch,dif_neg blo,G.adj_comm,site]
    have h : a.val≤b.val := by omega
    have n7 : ¬b.val < 7 := by omega
    simp only [base,Nat.min_eq_left h,Nat.max_eq_right h,n7,blo,if_false,alo,true_and,
      decide_eq_true_eq,Fin.ext_iff]
    omega
  · rw [stitch,dif_neg alo,stitch,dif_pos blo,site]
    have h : b.val≤a.val := by omega
    have n7 : ¬a.val < 7 := by omega
    simp only [base,Nat.min_eq_right h,Nat.max_eq_left h,n7,alo,if_false,blo,true_and,
      decide_eq_true_eq,Fin.ext_iff]
    omega
  · exact (one.elim alo blo).elim

theorem normalized_control_and_cycle_private_witnesses_nonadjacent
    (h4 : FourCycleFree G) (h9 : ¬∃ f : Fin 9→V,InducedPath G f)
    (m : Bool) (core priv : Fin 9→V)
    (ci : Function.Injective core)
    (fit : ∀ a b,G.Adj (core a) (core b)↔base m (embedCore a) (embedCore b)=true)
    (dis : ∀ i j,priv i≠core j)
    (site : ∀ i j,G.Adj (priv i) (core j)↔i=j)
    (c : Fin 2) (i : Fin 7) :
    ¬G.Adj (priv (Fin.castLE (by decide) i)) (priv ⟨c.val+7,by have := c.isLt; omega⟩) := by
  intro crossing
  have inj := stitch_injective ci dis site
  have model := stitch_known_core_pairs m fit site
  have force : G.Adj (stitch core priv (forcedSite i)) (stitch core priv (forcedControl c)) := by
    have x : ¬(forcedSite i).val < 9 := by simp [forcedSite]
    have y : ¬(forcedControl c).val < 9 := by unfold forcedControl; simp
    rw [stitch,dif_neg x,stitch,dif_neg y]
    have ex : (⟨(forcedSite i).val-9,by have := (forcedSite i).isLt; omega⟩ : Fin 9)
        = Fin.castLE (by decide) i := Fin.ext (by simp [forcedSite])
    have ey : (⟨(forcedControl c).val-9,by have := (forcedControl c).isLt; omega⟩ : Fin 9)
        = ⟨c.val+7,by have := c.isLt; omega⟩ := Fin.ext (by simp [forcedControl])
    rw [ex,ey]
    exact crossing
  obtain ⟨tree,cert⟩ := all_rows m c i
  exact checked_sound h4 h9 inj m c i model force tree [] (by intro q qm; cases qm) cert

#print axioms normalized_control_and_cycle_private_witnesses_nonadjacent
end Graffiti133PrivateCross

namespace Graffiti133PrivateCross
open SimpleGraph Finset Graffiti133 Graffiti133NoFive
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
variable {V : Type*} {G : SimpleGraph V}

def canonCore (H : Hole G 7) (u v : V) : Fin 9→V :=
  ![H.c 0,H.c 1,H.c 2,H.c 3,H.c 4,H.c 5,H.c 6,u,v]

theorem canonCore_injective (H : Hole G 7) (u v : V)
    (uo : Outside H.c u) (vo : Outside H.c v) (uv : u≠v) :
    Function.Injective (canonCore H u v) := by
  have hu (i : Fin 7) : H.c i≠u := (uo i).symm
  have hv (i : Fin 7) : H.c i≠v := (vo i).symm
  have eq (a b : Fin 7) : H.c a=H.c b↔a=b := H.inj.eq_iff
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [canonCore,eq,hu,hv,uo,vo,uv,uv.symm] at h ⊢ <;>
    first | exact uo _ h | exact vo _ h

theorem canonCore_fits (H : Hole G 7) (u v : V) (m : Bool)
    (noedge : ¬G.Adj u v)
    (up : ∀ i : Fin 7,G.Adj u (H.c i)↔i=0 ∨ i=3)
    (vp : ∀ i : Fin 7,G.Adj v (H.c i)↔ (if m then (i=1 ∨ i=2 ∨ i=5) else (i=1 ∨ i=4))) :
    ∀ a b : Fin 9,G.Adj (canonCore H u v a) (canonCore H u v b)↔base m (embedCore a) (embedCore b)=true := by
  have un (i : Fin 7) : G.Adj (H.c i) u↔ i=0 ∨ i=3 := (G.adj_comm _ _).trans (up i)
  have vn (i : Fin 7) : G.Adj (H.c i) v↔ (if m then (i=1 ∨ i=2 ∨ i=5) else (i=1 ∨ i=4)) :=
    (G.adj_comm _ _).trans (vp i)
  have flip : ¬G.Adj v u := fun e=>noedge e.symm
  intro a b
  cases m <;> fin_cases a <;> fin_cases b <;>
    simp [canonCore,embedCore,base,H.adj,up,vp,un,vn,noedge,flip,Cyclic] <;> decide

def PrivateFor (G : SimpleGraph V) (core : Fin 9→V) (i : Fin 9) (x : V) : Prop :=
  (∀ j,x≠core j) ∧ ∀ j,G.Adj x (core j)↔i=j

theorem canonical_private_witnesses_do_not_cross
    (H : Hole G 7) (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (u v : V) (m : Bool)
    (uo : Outside H.c u) (vo : Outside H.c v) (uv : u≠v)
    (noedge : ¬G.Adj u v)
    (up : ∀ i : Fin 7,G.Adj u (H.c i)↔i=0 ∨ i=3)
    (vp : ∀ i : Fin 7,G.Adj v (H.c i)↔ (if m then (i=1 ∨ i=2 ∨ i=5) else (i=1 ∨ i=4)))
    (has : ∀ i : Fin 9,∃ z,PrivateFor G (canonCore H u v) i z)
    (c : Fin 2) (i : Fin 7) {x y : V}
    (xp : PrivateFor G (canonCore H u v) ⟨c.val+7,by have := c.isLt; omega⟩ x)
    (yp : PrivateFor G (canonCore H u v) (Fin.castLE (by decide) i) y) :
    ¬G.Adj x y := by
  let ci : Fin 9 := ⟨c.val+7,by have := c.isLt; omega⟩
  let si : Fin 9 := Fin.castLE (by decide) i
  have ne : ci≠si := by
    intro e
    have eq := congrArg Fin.val e
    have lt := i.isLt
    change c.val+7=i.val at eq
    omega
  choose w wr using has
  let p (j : Fin 9) := if j=ci then x else if j=si then y else w j
  have p_ci : p ci=x := by simp [p]
  have p_si : p si=y := by simp [p,ne.symm]
  have pp (j : Fin 9) : PrivateFor G (canonCore H u v) j (p j) := by
    by_cases h : j=ci
    · subst j
      simpa only [p_ci] using xp
    · by_cases k : j=si
      · subst j
        simpa only [p_si] using yp
      · simpa only [p,if_neg h,if_neg k] using wr j
  have forbid := normalized_control_and_cycle_private_witnesses_nonadjacent h4 h9 m
    (canonCore H u v) p (canonCore_injective H u v uo vo uv) (canonCore_fits H u v m noedge up vp)
    (fun j=>(pp j).1) (fun j=>(pp j).2) c i
  change ¬G.Adj (p si) (p ci) at forbid
  rw [p_si,p_ci] at forbid
  exact fun e=>forbid e.symm

#print axioms canonical_private_witnesses_do_not_cross
end Graffiti133PrivateCross
