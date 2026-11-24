import GroupWL.IncidenceForward
import GroupWL.IncidenceSize
import GroupWL.IsomorphismTransport
import GroupWL.GraphToGroup
namespace GroupWL.SingleObstruction
open IncidenceTensor FrameResponses DenseTensorEncoding Refinement
open GadgetDecoding in
theorem unaryAt {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H] {d : ℕ}
    {a : Fin d → GadgetVertex G} {b : Fin d → GadgetVertex H}
    (h : SameGraph a b) (i j : Fin d) (hij : i ≠ j) (r : ℕ) :
    neighborColor gadgetAdj r (a i) = neighborColor gadgetAdj r (b i) := by
  classical
  induction r generalizing a b i j with
  | zero => rfl
  | succ r ih =>
    obtain ⟨f,hf,hs⟩ := h.neighborhoods i j hij
    have hm : (neighbors (a i)).map f.toEmbedding = neighbors (b i) := by
      ext y
      simp only [Finset.mem_map,mem_neighbors,Equiv.toEmbedding_apply]
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact (hf x).mp hx
      · intro hy
        exact ⟨f.symm y,(hf _).mpr (by simpa using hy),f.apply_symm_apply y⟩
    change (_, (neighbors (a i)).val.map _) = (_, (neighbors (b i)).val.map _)
    apply Prod.ext (ih h i j hij)
    rw [← hm, Finset.map_val, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro x _
    simpa only [Function.comp_apply,Equiv.coe_toEmbedding,Function.update_self] using
      ih (hs x) j i hij.symm
open GadgetDecoding in
theorem unaryOfTwo {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H]
    [Nontrivial G] [Nontrivial H] (hh : EquivalentIII 2 G H) : EquivalentIII 1 G H := by
  classical
  simp only [EquivalentIII,show 2 ≠ 1 by decide,if_false] at hh
  obtain ⟨b,h⟩ := GraphToGroup.exists_stable_group_tuple hh
  obtain ⟨e,he⟩ := GadgetMatching.group_matching h (0 : Fin 2) 1 (by decide)
  simp only [EquivalentIII,if_true]
  intro r
  have hc (x : G) : neighborColor gadgetAdj r (Sum.inl x) =
      neighborColor gadgetAdj r (Sum.inl (e x)) := by
    simpa only [Function.update_self] using unaryAt (he x) 0 1 (by decide) r
  unfold neighborGroupHistogram
  calc
    _ = Finset.univ.val.map ((fun y : H => neighborColor gadgetAdj r (Sum.inl y)) ∘ e) :=
      Multiset.map_congr rfl fun x _ => hc x
    _ = _ := by rw [← Multiset.map_map,Multiset.map_univ_val_equiv]
theorem nontrivialOfHard {p : ℕ} [Fact p.Prime] {S : Statement.TensorDescription p}
    (h : Statement.HardGroup p S) : Nontrivial S.Carrier := by
  obtain ⟨g,g',hne⟩ := h.2.2.1
  exact ⟨g,g',fun he => hne (he ▸ Commute.refl g')⟩

variable (p : ℕ) [Fact p.Prime] [NeZero (2 : ZMod p)]
def A : AffineSystem (ZMod p) Unit Empty (fun _ => ZMod p) where
  scope _ := ∅
  coefficient _ _ := 0
  coefficient_outside _ _ _ := rfl
def beta (_ : Unit) : ZMod p := 1
omit [NeZero (2 : ZMod p)] in
theorem obstructed : beta p ∉ LinearMap.range (A p).linearMap := by
  rintro ⟨z,hz⟩
  have h := congrFun hz ()
  simp [AffineSystem.linearMap, AffineSystem.equation, A, beta] at h
def atZero : (A p).ExactLocalFamily (beta p) 0 where
  assignments _ := Set.univ
  nonempty _ _ := ⟨0, trivial⟩
  sound S h _ _ i hi := by
    have hS : S=∅ := Finset.card_eq_zero.mp (by omega)
    simp [hS] at hi
  saturated _ _ _ _ _ := Iff.rfl
  restrict _ _ _ _ := Set.Subset.rfl
  extend _ _ _ _ z _ := ⟨z,trivial,fun _ _ => rfl⟩
theorem small {q : ℕ} (hq : 0 < q)
    (f : AlternatingBilinearMap (ZMod p) (PaddedInput (A p) q) (PaddedOutput (A p) q)) :
    let T := incidenceDescription p (A p) q hq f
    T.inputDimension + T.outputDimension ≤ 69*q^4 := by
  let x := IncidenceSize.inputBound (A p) q
  let z := IncidenceSize.outputBound (A p) q
  have h₁ := IncidenceSize.description_inputDimension_le q p (A p) hq f
  have h₂ := IncidenceSize.description_outputDimension_le q p (A p) hq f
  have xval : x ≤ 6*q^2 := by
    simp [x,IncidenceSize.inputBound,IncidenceSize.oldInputBound,IncidenceSize.oldOutputBound,IncidenceSize.vertexBound]
    nlinarith [Nat.le_self_pow (n:=2) (by decide) q]
  have zval : z ≤ 9*q^2 := by
    simp [z,IncidenceSize.inputBound,IncidenceSize.outputBound,IncidenceSize.oldInputBound,IncidenceSize.oldOutputBound,IncidenceSize.vertexBound]
    nlinarith [Nat.le_self_pow (n:=2) (by decide) q]
  apply (Nat.add_le_add h₁ h₂).trans
  change x+x*z+z ≤ 69*q^4
  have h := Nat.add_le_add (Nat.add_le_add xval (Nat.mul_le_mul xval zval)) zval
  apply h.trans
  nlinarith [Nat.pow_le_pow_right (by omega : 1 ≤ q) (by decide : 2 ≤ 4)]
theorem simultaneous (k : ℕ) (hk : 1 ≤ k) :
    ∃ S U : Statement.TensorDescription p,
      S.inputDimension + S.outputDimension ≤ 69*(2*k+6)^4 ∧
      U.inputDimension + U.outputDimension ≤ 69*(2*k+6)^4 ∧
      Statement.HardGroup p S ∧ Statement.HardGroup p U ∧
      ¬ Nonempty (S.Carrier ≃* U.Carrier) ∧ ∀ v, GroupEquivalent v k S.Carrier U.Carrier := by
  classical
  let q := 2*k+6
  have hq : 3≤q := by dsimp [q]; omega
  let f := epsilonCharge (A p) q (by omega) (beta p)
  let S := incidenceDescription p (A p) q (by omega) AlternatingBilinearMap.zero
  let U := incidenceDescription p (A p) q (by omega) f
  let e : ZeroGroup (A p) q (by omega) ≃* S.Carrier :=
    incidenceDescriptionMulEquiv p (A p) q (by omega) _
  let g : ChargedGroup (A p) q (by omega) (beta p) ≃* U.Carrier :=
    incidenceDescriptionMulEquiv p (A p) q (by omega) _
  letI : Fintype (ZeroGroup (A p) q (by omega)) := Fintype.ofEquiv _ e.toEquiv.symm
  letI : Fintype (ChargedGroup (A p) q (by omega) (beta p)) := Fintype.ofEquiv _ g.toEquiv.symm
  have hs : Statement.HardGroup p S := incidenceDescription_hardGroup p (A p) q hq _
  have hu : Statement.HardGroup p U := incidenceDescription_hardGroup p (A p) q hq _
  refine ⟨S,U,small p (by omega : 0<q) _,small p (by omega : 0<q) _,hs,hu,?_,?_⟩
  · rintro ⟨i⟩
    exact obstructed p ((NamedChargeReduction.zero_charge_iso (A p) q (by omega) hq (beta p)).mp
      ⟨e.trans (i.trans g.symm)⟩)
  · have hq2 : 2≤q := by omega
    have hr : 2*k+3+1 < (q-1)*(0+1) := by dsimp only [q]; omega
    have h := IncidenceForward.equivalentII (A p) q hq2 (beta p) 0 (2*k+3)
        hr Empty.elim (fun j => j.elim) (atZero p)
    have hd : EquivalentII (2*k+3) S.Carrier U.Carrier :=
      (groupEquivalent_transport_right (version := .two) g (by omega)).mp
        ((groupEquivalent_transport_left (version := .two) e (by omega)).mp h)
    intro v
    cases v with
    | one => exact PebbleReindex.equivalentI_of_equivalentII_of_le (by omega) hd
    | two => exact PebbleReindex.equivalentII_mono (by omega) hd
    | three =>
      by_cases h1 : k=1
      · subst k
        letI := nontrivialOfHard hs
        letI := nontrivialOfHard hu
        exact unaryOfTwo (ConcreteVersionIII.equivalentIII_of_equivalentI
          (k:=2) (d:=2*1+3) (by decide) (by decide)
          (PebbleReindex.equivalentI_of_equivalentII_of_le (le_refl _) hd))
      · exact ConcreteVersionIII.equivalentIII_of_equivalentI h1 (by omega : 2*k+1≤2*k+3)
          (PebbleReindex.equivalentI_of_equivalentII_of_le (le_refl _) hd)
theorem boundedOrder (k : ℕ) (hk : 1 ≤ k) :
    ∃ S U : Statement.TensorDescription p,
      Fintype.card S.Carrier ≤ p^(69*(2*k+6)^4) ∧
      Fintype.card U.Carrier ≤ p^(69*(2*k+6)^4) ∧
      Statement.HardGroup p S ∧ Statement.HardGroup p U ∧
      ¬ Nonempty (S.Carrier ≃* U.Carrier) ∧ ∀ v, GroupEquivalent v k S.Carrier U.Carrier := by
  obtain ⟨S,U,hS,hU,hs,hu,hn,hv⟩ := simultaneous p k hk
  have hp : 1≤p := (Fact.out : p.Prime).one_lt.le
  refine ⟨S,U,?_,?_,hs,hu,hn,hv⟩
  · rw [Statement.card_carrier]
    exact Nat.pow_le_pow_right hp hS
  · rw [Statement.card_carrier]
    exact Nat.pow_le_pow_right hp hU
end GroupWL.SingleObstruction
