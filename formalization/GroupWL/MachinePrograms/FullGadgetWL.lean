import GroupWL.GadgetDecoding
import GroupWL.GraphToGroup
import GroupWL.NeighborIsomorphism
import GroupWL.MachinePrograms.GroupTupleSemantics
import GroupWL.MachinePrograms.GraphWLCoreCorrectness
import GroupWL.MachinePrograms.GadgetPairTables
import GroupWL.MachinePrograms.WLExponentialBudgets

namespace GroupWL.UnaryOnly
open Refinement GadgetDecoding
variable {G : Type} [Group G] [Fintype G]
def kind : GadgetVertex G → Option (Fin 4)
  | .inl _ => none
  | .inr (_,_,j) => some j
def role (i : Fin 3) : Fin 4 := if i=0 then 0 else if i=1 then 1 else 3
def code (g : G) : Fin 3 × G ↪ GadgetVertex G where
  toFun := fun (i,x) => Sum.inr (if i=0 then (g,x,0) else if i=1 then (x,g,1) else (x,x⁻¹*g,3))
  inj' := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    fin_cases i <;> fin_cases j <;> simp_all
omit [Fintype G] in
theorem code_kind (g : G) (i : Fin 3) (x : G) : kind (code g (i,x))=some (role i) := by
  fin_cases i <;> rfl
theorem neighbors_group (g : G) : neighbors (Sum.inl g) = Finset.univ.map (code g) := by
  classical
  ext v
  simp only [mem_neighbors, Finset.mem_map, Finset.mem_univ, true_and]
  cases v with
  | inl u =>
    constructor
    · simp
    · rintro ⟨⟨i,x⟩,h⟩
      fin_cases i <;> simp [code] at h
  | inr v =>
    rcases v with ⟨a,b,j⟩
    rw [adj_group_internal]
    constructor
    · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
      · exact ⟨(0,b),rfl⟩
      · exact ⟨(1,a),rfl⟩
      · exact ⟨(2,a),by simp [code]⟩
    · rintro ⟨⟨i,x⟩,h⟩
      fin_cases i <;> simp [code] at h <;> obtain ⟨rfl,rfl,rfl⟩ := h <;> simp
def palette (n : ℕ) : (r : ℕ) → Option (Fin 4) → NeighborColor r
  | 0, _ => ()
  | r+1, j =>
    let c := palette n r
    (c j, match j with
      | none => Finset.univ.val.map (fun u : Fin 3 × Fin n => c (some (role u.1)))
      | some 0 => {c none, c (some 1)}
      | some 1 => {c none, c (some 0),c (some 2)}
      | some 2 => {c (some 1),c (some 3)}
      | some 3 => {c none, c (some 2)})
theorem color_kind (r : ℕ) (v : GadgetVertex G) :
    neighborColor gadgetAdj r v = palette (Fintype.card G) r (kind v) := by
  classical
  induction r generalizing v with
  | zero => rfl
  | succ r ih =>
    change (_, (neighbors v).val.map _) = (_, _)
    apply Prod.ext (ih v)
    cases v with
    | inl g =>
      rw [neighbors_group,Finset.map_val,Multiset.map_map]
      let e : Fin 3 × G ≃ Fin 3 × Fin (Fintype.card G) := Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin _)
      calc
        _ = Finset.univ.val.map ((fun u : Fin 3 × Fin (Fintype.card G) => palette (Fintype.card G) r (some (role u.1))) ∘ e) := by
          apply Multiset.map_congr rfl
          rintro ⟨i,x⟩ _
          exact (ih _).trans (by rw [code_kind]; rfl)
        _ = _ := by rw [← Multiset.map_map,Multiset.map_univ_val_equiv]; rfl
    | inr a =>
      rcases a with ⟨g,h,j⟩
      fin_cases j <;>
        simp [neighbors_zero,neighbors_one,neighbors_two,neighbors_three,
          ih, kind]
theorem unary_iff_card {H : Type} [Group H] [Fintype H] :
    EquivalentIII 1 G H ↔ Fintype.card G=Fintype.card H := by
  classical
  rw [EquivalentIII,if_pos rfl]
  constructor
  · intro hh
    exact congrArg Multiset.card (hh 0) |> (by simpa [neighborGroupHistogram] using ·)
  · intro h r
    simp only [neighborGroupHistogram,color_kind,kind,Multiset.map_const',Finset.card_val,Finset.card_univ,h]
end GroupWL.UnaryOnly
namespace GroupWL.SimpleGadgetSemantics
open Refinement InitialIWords GadgetDecoding
set_option linter.unusedSectionVars false
variable {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H] {k : ℕ}
def allGraph (k : ℕ) (G H : Type) [Group G] [Group H] [Fintype G] [Fintype H] : Prop :=
  Equivalent (graphInitial (gadgetAdj (G:=G)) k) (graphInitial (gadgetAdj (G:=H)) k)

private theorem card_eq (hk : k ≠ 0) (h : allGraph k G H) : Fintype.card G = Fintype.card H := by
  have hc := card_eq_of_equivalent hk h
  simp only [GadgetVertex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at hc
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := Nat.mul_le_mul hlt.le (Nat.mul_le_mul_right 4 hlt.le); omega
  · have := Nat.mul_le_mul hgt.le (Nat.mul_le_mul_right 4 hgt.le); omega

private def unwrap (v : GadgetVertex G) : G := v.elim id (fun _ => 1)
private theorem wrap_unwrap (v : GadgetVertex G) (hv : IsGroup v) : Sum.inl (unwrap v) = v := by
  cases v <;> first | rfl | cases hv

private def coded (G : Type) [Group G] [Fintype G] (k : ℕ) :
    (Fin k → G) ≃ {a : Fin k → GadgetVertex G // ∀i, IsGroup (a i)} where
  toFun a := ⟨Sum.inl ∘ a,fun _ => trivial⟩
  invFun a := unwrap ∘ a.1
  left_inv _ := rfl
  right_inv a := Subtype.ext (funext fun i => wrap_unwrap (a.val i) (a.property i))

private theorem restrict_graph (hk : 2 ≤ k) [Nontrivial G] [Nontrivial H] (h : allGraph k G H) :
    ∀r,graphGroupHistogram (G:=G) k r = graphGroupHistogram (G:=H) k r := by
  classical
  let a : Fin k → GadgetVertex G := fun _ => .inl 1
  obtain ⟨b,_,hs⟩ := exists_stable_of_forall_exists (initialA:=graphInitial (gadgetAdj (G:=G)) k)
    (initialB:=graphInitial (gadgetAdj (G:=H)) k) a (fun _=>True) (by
      intro r
      have hm : color (graphInitial (gadgetAdj (G:=G)) k) r a ∈ histogram (graphInitial (gadgetAdj (G:=G)) k) r :=
        Multiset.mem_map.mpr ⟨a,Finset.mem_univ _,rfl⟩
      rw [h r] at hm
      obtain ⟨b,_,hb⟩ := Multiset.mem_map.mp hm
      exact ⟨b,trivial,hb.symm⟩)
  obtain ⟨e,he⟩ := hs.complete_tuples k (Function.Embedding.refl _)
  have eqAll (t : Fin k → GadgetVertex G) : SameGraph t (e t) := by
    obtain ⟨v,w,hh,coords,_⟩ := he t
    have hv : v=t := funext fun i => (coords i).1
    have hw : w=e t := funext fun i => (coords i).2
    simpa only [hv,hw] using hh
  have tags (t : Fin k → GadgetVertex G) : (∀i, IsGroup (t i)) ↔ ∀i, IsGroup (e t i) := by
    refine forall_congr' fun i => ?_
    let zero : Fin k := ⟨0,by omega⟩
    let one : Fin k := ⟨1,by omega⟩
    by_cases hz : i=zero
    · exact (eqAll t).isGroup_iff i one (by subst i; apply Fin.ne_of_val_ne; exact Nat.zero_ne_one)
    · exact (eqAll t).isGroup_iff i zero hz
  let f := (coded G k).trans ((e.subtypeEquiv tags).trans (coded H k).symm)
  have hf (x : Fin k→G) : Sum.inl ∘ f x = e (Sum.inl ∘ x) := by
    apply funext; intro i
    exact wrap_unwrap _ ((tags (Sum.inl ∘ x)).mp (fun _ => trivial) i)
  intro r
  unfold graphGroupHistogram
  calc
    _ = Finset.univ.val.map ((fun v : Fin k→GadgetVertex H => color (graphInitial gadgetAdj k) r v) ∘ (fun x : Fin k→G => Sum.inl ∘ f x)) := by
      apply Multiset.map_congr rfl
      intro x _
      simpa only [Function.comp_apply,hf] using eqAll (Sum.inl ∘ x) r
    _ = (Finset.univ.val.map f).map (fun x : Fin k→H => color (graphInitial gadgetAdj k) r (Sum.inl ∘ x)) := by rw [Multiset.map_map]; rfl
    _ = _ := by rw [Multiset.map_univ_val_equiv]

theorem two_le_iff (hk : 2≤k) : EquivalentIII k G H ↔ allGraph k G H := by
  constructor
  · intro h
    have hr : ∀r,graphGroupHistogram (G:=G) k r=graphGroupHistogram (G:=H) k r := by
      simpa [EquivalentIII,show k≠1 by omega] using h
    obtain ⟨b,hb⟩ := GraphToGroup.exists_stable_group_tuple hr
    exact hb.equivalent
  · intro h
    have hc := card_eq (by omega : k≠0) h
    by_cases hN : Nontrivial G
    · letI := hN
      letI : Nontrivial H := Fintype.one_lt_card_iff_nontrivial.mp (by rw [←hc];exact Fintype.one_lt_card)
      simpa [EquivalentIII,show k≠1 by omega] using restrict_graph hk h
    · letI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hN
      letI : Subsingleton H := Fintype.card_le_one_iff_subsingleton.mp (by rw [←hc];exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance)
      letI : Unique G := ⟨⟨1⟩,fun _=>Subsingleton.elim _ _⟩
      letI : Unique H := ⟨⟨1⟩,fun _=>Subsingleton.elim _ _⟩
      exact groupEquivalent_of_isomorphic (MulEquiv.ofUnique : G≃*H) .three k

theorem full_one_iff : allGraph 1 G H ↔ Fintype.card G=Fintype.card H := by
  refine ⟨card_eq (by decide),fun hc => ?_⟩
  let f : G≃H := Fintype.equivOfCardEq hc
  let e : GadgetVertex G≃GadgetVertex H := Equiv.sumCongr f (Equiv.prodCongr f (Equiv.prodCongr f (Equiv.refl _)))
  apply equivalent_of_initial_equiv e
  intro a
  apply Prod.ext <;> funext i j <;> have h : i=j := Subsingleton.elim _ _ <;>
    subst j <;> simp [graphInitial,gadgetAdj_irrefl]
end GroupWL.SimpleGadgetSemantics


namespace GroupWL.SimpleGadgetSemantics
open Refinement
theorem all_positive_iff {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H] {k : ℕ}
    (hk : 0 < k) : EquivalentIII k G H ↔ allGraph k G H := by
  by_cases h : k = 1
  · subst k
    exact UnaryOnly.unary_iff_card.trans full_one_iff.symm
  · exact two_le_iff (by omega)
end GroupWL.SimpleGadgetSemantics

namespace GroupWL.MachinePrograms.GraphWLCore
open NatArrayLanguage IndexedRefinement
set_option maxRecDepth 8192
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
variable {n m k : ℕ}
def fullWL : List (Atom Reg Arr) := [
  .copy (wl .n) (dimensions 10),.copy (wl .width) (dimensions 11),
  .copyArray (array .targets) (.inl (.inr (.inl (.inl (.inr 2))))),
  .copyArray (array .fanouts) (.inl (.inr (.inl (.inr (.inr 2))))),
  .copyArray (array .leftSelection) (.inl (.inr (.inr (.inr ())))),
  .copyArray (array .rightSelection) (.inl (.inr (.inr (.inl ()))))]

def fullSetup : Code := .seq (atoms prepareDimensions)
  (.seq (TupleDimensions.program.map Sum.inr Sum.inr)
    (.seq (atoms prepareTables)
      (.seq ((GraphMatrixPrograms.build.map Sum.inl Sum.inl).map Sum.inl Sum.inl)
        (.seq ((GroupTupleArrays.generate.map Sum.inr Sum.inr).map Sum.inl Sum.inl)
          (atoms fullWL)))))

def fullDecide : Code := .seq fullSetup (IndexedWL.decide.map wl array)

theorem fullSetup_runs (f : Fin n→Fin n→Bool) (g : Fin m→Fin m→Bool)
    (S : State) (B : ℕ) (input : Input (k:=k) f g B S)
    (matrixRoom : GraphMatrixPrograms.Room n m k B)
    (room : IndexedWL.Room (n^k+m^k) k (max n m) B) :
    ∃t≤400*(B+1)^4,∃T,Runs (storageBound Reg Arr B) fullSetup S t T ∧ T.Bounded B ∧
      IndexedWL.Input (IndexedTuples.data n m k matrixRoom.left_positive)
        (GraphMatrixPrograms.initialRelation f g) B (core T) ∧
      (core T).array .leftSelection=(IndexedTuples.leftSelection n m k).map Fin.val ∧
      (core T).array .rightSelection=(IndexedTuples.rightSelection n m k).map Fin.val := by
  have Nroom : n^k+m^k≤B := (Nat.le_mul_self _).trans matrixRoom.matrix
  have kroom : k≤B := room.arity
  obtain ⟨start,hA⟩ := atoms_runs input.bounded prepareDimensions
    (by simp [prepareDimensions,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let A := applyAtoms prepareDimensions S
  have an : A.right.scalar 0=n := by
    simpa [A,applyAtoms,prepareDimensions,Atom.apply,Store.right,Store.setScalar,dimensions,wl] using input.left_order
  have am : A.right.scalar 1=m := by
    simpa [A,applyAtoms,prepareDimensions,Atom.apply,Store.right,Store.setScalar,dimensions,wl] using input.right_order
  have ak : A.right.scalar 2=k := by
    simpa [A,applyAtoms,prepareDimensions,Atom.apply,Store.right,Store.setScalar,dimensions,wl] using input.arity
  obtain ⟨t,ht,U,dims,hU,un,um,uk,ul,ur,ut,uw⟩ := TupleDimensions.program_runs A.right B n m k hA.right
    matrixRoom.left_positive matrixRoom.right_positive an am ak Nroom
  let C := A.left.join U
  have dims' := dims.right_bounded hA
  have hC : C.Bounded B := hA.left.join hU
  obtain ⟨stage,hD⟩ := atoms_runs hC prepareTables
    (by simp [prepareTables,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let D := applyAtoms prepareTables C
  have din : GraphMatrixPrograms.Input (k:=k) f g B D.left.left := by
    refine ⟨hD.left.left,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [D,C,A,applyAtoms,prepareTables,prepareDimensions,Atom.apply,Store.left,Store.setScalar,dimensions,wl,target,selection] using input.left_order
    · simpa [D,C,A,applyAtoms,prepareTables,prepareDimensions,Atom.apply,Store.left,Store.setScalar,dimensions,wl,target,selection] using input.right_order
    · simpa [D,C,A,applyAtoms,prepareTables,prepareDimensions,Atom.apply,Store.left,Store.setScalar,dimensions,wl,target,selection] using input.arity
    · simp [D,C,applyAtoms,prepareTables,Atom.apply,Store.left,Store.setScalar,dimensions,wl,target,selection,Sum.inr,ul]
    · simp [D,C,applyAtoms,prepareTables,Atom.apply,Store.left,Store.setScalar,dimensions,wl,target,selection,Sum.inr,ut]
    · exact input.left_table
    · exact input.right_table
  have dataInputs : D.left.right.scalar (GroupTupleArrays.target (.inl 0))=n ∧
      D.left.right.scalar (GroupTupleArrays.target (.inr 0))=m ∧
      D.left.right.scalar (GroupTupleArrays.target (.inl 11))=k ∧
      D.left.right.scalar (GroupTupleArrays.target (.inl 12))=max n m ∧
      D.left.right.scalar (GroupTupleArrays.selection (.inl 0))=n^k ∧
      D.left.right.scalar (GroupTupleArrays.selection (.inr ()))=m^k := by
    simp [D,C,applyAtoms,prepareTables,Atom.apply,Store.left,Store.right,Store.setScalar,dimensions,wl,target,selection,
      GroupTupleArrays.target,GroupTupleArrays.selection,un,um,uk,ul,ur,uw]
  obtain ⟨u,hu',V,matrix,vctx,matrixV⟩ := GraphMatrixPrograms.build_runs f g D.left.left matrixRoom din
  have hu : u≤210*(B+1)^4 := by
    have h := hu'.trans (GraphMatrixPrograms.build_cost_le matrixRoom)
    have power : (B+1)^2≤(B+1)^4 := pow_le_pow_right' (by omega) (by omega)
    nlinarith
  have hV := vctx.bounded
  have arityV := vctx.arity_eq
  let E := (V.join D.left.right).join D.right
  have matrix' := (matrix.left_bounded hD.left).left_bounded hD
  have hE : E.Bounded B := (hV.join hD.left.right).join hD.right
  obtain ⟨v,hv,W,arrays,hW,targets,fanouts,lefts,rights⟩ := GroupTupleArrays.generate_runs n m k
    matrixRoom.left_positive matrixRoom.right_positive E.left.right B hE.left.right
    dataInputs.1 dataInputs.2.1 dataInputs.2.2.1 dataInputs.2.2.2.1
    dataInputs.2.2.2.2.1 dataInputs.2.2.2.2.2 Nroom room.pair room.target
  let F := (E.left.left.join W).join E.right
  have arrays' := (arrays.right_bounded hE.left).left_bounded hE
  have hF : F.Bounded B := (hE.left.left.join hW).join hE.right
  obtain ⟨finish,hT⟩ := atoms_runs hF fullWL
    (by simp [fullWL,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let T := applyAtoms fullWL F
  have dimensionsFrame : F.right=U := by
    apply Store.ext <;> intro r <;>
      simp [F,E,D,C,applyAtoms,prepareTables,Atom.apply,Store.right,Store.setScalar,dimensions,wl,target,selection]
  have ready : IndexedWL.Input (IndexedTuples.data n m k matrixRoom.left_positive)
      (GraphMatrixPrograms.initialRelation f g) B (core T) := by
    refine ⟨hT.left.left.right,?_,?_,?_,?_,?_,?_⟩
    · change T.scalar (wl .n)=n^k+m^k
      simp [T,applyAtoms,fullWL,Atom.apply,Store.setScalar,Store.setArray,wl,dimensions]
      exact congrArg (fun Q : Store TupleDimensions.Reg TupleDimensions.Arr=>Q.scalar 10) dimensionsFrame |>.trans ut
    · simpa [T,F,E,core,applyAtoms,fullWL,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,wl,array,dimensions,Sum.inr] using arityV
    · change T.scalar (wl .width)=max n m
      simp [T,applyAtoms,fullWL,Atom.apply,Store.setScalar,Store.setArray,wl,dimensions]
      exact congrArg (fun Q : Store TupleDimensions.Reg TupleDimensions.Arr=>Q.scalar 11) dimensionsFrame |>.trans uw
    · simpa [T,F,E,core,applyAtoms,fullWL,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,wl,array,dimensions,Sum.inr] using matrixV
    · simpa [T,F,core,applyAtoms,fullWL,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,wl,array,dimensions] using fanouts
    · simpa [T,F,core,applyAtoms,fullWL,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,wl,array,dimensions] using targets
  have selectL : (core T).array .leftSelection=(IndexedTuples.leftSelection n m k).map Fin.val := by
    simpa [T,F,E,core,applyAtoms,fullWL,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,wl,array,dimensions] using lefts
  have selectR : (core T).array .rightSelection=(IndexedTuples.rightSelection n m k).map Fin.val := by
    simpa [T,F,E,core,applyAtoms,fullWL,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,wl,array,dimensions] using rights
  refine ⟨3+(t+(8+(u+(v+6)))),?_,T,.seq start (.seq dims' (.seq stage (.seq matrix' (.seq arrays' finish)))),hT,ready,selectL,selectR⟩
  have power : (B+1)^2≤(B+1)^4 := pow_le_pow_right' (by omega) (by omega)
  have linear : B+1≤(B+1)^4 := by simpa only [pow_one] using pow_le_pow_right' (by omega : 1≤B+1) (by omega : 1≤4)
  nlinarith

theorem fullDecide_runs (f : Fin n→Fin n→Bool) (g : Fin m→Fin m→Bool)
    (S : State) (B : ℕ) (input : Input (k:=k) f g B S)
    (matrixRoom : GraphMatrixPrograms.Room n m k B)
    (room : IndexedWL.Room (n^k+m^k) k (max n m) B)
 :
    ∃t≤1000*(B+1)^7,∃T,Runs (storageBound Reg Arr B) fullDecide S t T ∧ T.Bounded B ∧
      (T.scalar (wl .result)≠0 ↔ ∀r,
        (IndexedTuples.leftSelection n m k : Multiset _).map (CompressedRefinement.labels (IndexedTuples.data n m k matrixRoom.left_positive).edges
          (GraphMatrixPrograms.pointSignature f g) r)=
        (IndexedTuples.rightSelection n m k : Multiset _).map (CompressedRefinement.labels (IndexedTuples.data n m k matrixRoom.left_positive).edges
          (GraphMatrixPrograms.pointSignature f g) r)) := by
  obtain ⟨t,ht,U,first,hU,ready,lefts,rights⟩ := fullSetup_runs f g S B input matrixRoom room
  let D := IndexedTuples.data n m k matrixRoom.left_positive
  have prepared : IndexedWL.Input D (CompressedRefinement.table D.edges (GraphMatrixPrograms.initialEq f g) 0) B (core U) := ready
  let left := IndexedTuples.leftSelection n m k
  let right := IndexedTuples.rightSelection n m k
  have lengthL : left.length ≤ B := by
    simpa [left] using ((Nat.le_add_right (n^k) (m^k)).trans ((Nat.le_mul_self _).trans matrixRoom.matrix))
  have lengthR : right.length ≤ B := by
    simpa [right] using ((Nat.le_add_left (m^k) (n^k)).trans ((Nat.le_mul_self _).trans matrixRoom.matrix))
  obtain ⟨u,hu,V,last,hV,correct⟩ := IndexedWL.decide_runs_correct D (GraphMatrixPrograms.pointSignature f g)
    (GraphMatrixPrograms.initialEq f g) (GraphMatrixPrograms.initialEq_correct f g) (core U) room prepared left right
    lefts rights lengthL lengthR
  let T := ((U.left.left.left.join V).join U.left.right).join U.right
  have run := ((last.right_bounded hU.left.left).left_bounded hU.left).left_bounded hU
  have run' : Runs (storageBound Reg Arr B) (IndexedWL.decide.map wl array) U u T := by
    simpa only [NatArrayLanguage.Program.map_map,Function.comp_def,wl,array] using run
  have hT : T.Bounded B := ((hU.left.left.left.join hV).join hU.left.right).join hU.right
  have budget := hu.trans (IndexedWL.decisionCost_le_common_bound room lengthL lengthR)
  have power : (B+1)^4≤(B+1)^7 := pow_le_pow_right' (by omega) (by omega)
  exact ⟨t+u,by nlinarith,T,.seq first run',hT,correct⟩

end GroupWL.MachinePrograms.GraphWLCore

namespace GroupWL.MachinePrograms.SimpleGadget
open NatArrayLanguage Refinement CompressedRefinement
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
abbrev Reg := GadgetPairTables.Reg ⊕ GraphWLCore.Reg
abbrev Arr := GadgetPairTables.Arr ⊕ GraphWLCore.Arr
abbrev State := Store Reg Arr
def copyTables : List (Atom Reg Arr) := [
  .copy (.inr (GraphWLCore.wl .leftCount)) (.inl (.inl (.inr 5))),
  .copy (.inr (GraphWLCore.wl .rightCount)) (.inl (.inr (.inr 5))),
  .copyArray (.inr (GraphWLCore.array .fanouts)) (.inl (.inl (.inr ()))),
  .copyArray (.inr (GraphWLCore.array .targets)) (.inl (.inr (.inr ())))]
def decide : NatArrayLanguage.Program Reg Arr := .seq (GadgetPairTables.generate.map Sum.inl Sum.inl)
    (.seq (atoms copyTables) (GraphWLCore.fullDecide.map Sum.inr Sum.inr))
section
variable {G H : Type} [Fintype G] [Fintype H] {n m k : ℕ}
theorem selectionL (e : G≃Fin n) (e' : H≃Fin m) :
    (IndexedTuples.leftSelection n m k : Multiset _) =
      (FiniteWL.leftTuples (A:=G) (B:=H) (k:=k)).map (FiniteWL.numericEnumeration e e') := by
  let code : (Fin k→G)≃Fin (n^k) := (Equiv.piCongrRight (fun _ : Fin k=>e)).trans finFunctionFinEquiv
  have he := Multiset.map_univ_val_equiv code
  unfold IndexedTuples.leftSelection
  rw [←Fin.univ_val_map,←he,Multiset.map_map,FiniteWL.leftTuples,Multiset.map_map]
  apply Multiset.map_congr rfl
  intro a ha
  rfl

theorem selectionR (e : G≃Fin n) (e' : H≃Fin m) :
    (IndexedTuples.rightSelection n m k : Multiset _) =
      (FiniteWL.rightTuples (A:=G) (B:=H) (k:=k)).map (FiniteWL.numericEnumeration e e') := by
  let code : (Fin k→H)≃Fin (m^k) := (Equiv.piCongrRight (fun _ : Fin k=>e')).trans finFunctionFinEquiv
  have he := Multiset.map_univ_val_equiv code
  unfold IndexedTuples.rightSelection
  rw [←Fin.univ_val_map,←he,Multiset.map_map,FiniteWL.rightTuples,Multiset.map_map]
  apply Multiset.map_congr rfl
  intro a ha
  rfl

end
variable {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H]
  [DecidableEq G] [DecidableEq H] {n m k : ℕ}
theorem semantic (e : G≃Fin n) (e' : H≃Fin m) :
    (∀r,(IndexedTuples.leftSelection (IndexedGadget.size n) (IndexedGadget.size m) k : Multiset _).map
      (labels (IndexedTuples.data (IndexedGadget.size n) (IndexedGadget.size m) k
        (by have := (e 1).isLt;unfold IndexedGadget.size;omega)).edges
        (GraphMatrixPrograms.pointSignature (IndexedGadget.numericAdj (GroupInitial.encodedMul e))
          (IndexedGadget.numericAdj (GroupInitial.encodedMul e'))) r)=
      (IndexedTuples.rightSelection (IndexedGadget.size n) (IndexedGadget.size m) k : Multiset _).map
      (labels (IndexedTuples.data (IndexedGadget.size n) (IndexedGadget.size m) k
        (by have := (e 1).isLt;unfold IndexedGadget.size;omega)).edges
        (GraphMatrixPrograms.pointSignature (IndexedGadget.numericAdj (GroupInitial.encodedMul e))
          (IndexedGadget.numericAdj (GroupInitial.encodedMul e'))) r)) ↔
      Equivalent (graphInitial (gadgetAdj (G := G)) k) (graphInitial (gadgetAdj (G := H)) k) := by
  classical
  rw [selectionL (IndexedGadget.groupEnumeration e) (IndexedGadget.groupEnumeration e'),
    selectionR (IndexedGadget.groupEnumeration e) (IndexedGadget.groupEnumeration e')]
  change (∀r, ((FiniteWL.leftTuples (A := GadgetVertex G) (B := GadgetVertex H) (k := k)).map (IndexedGadget.tupleEnumeration e e')).map _ = ((FiniteWL.rightTuples (A := GadgetVertex G) (B := GadgetVertex H) (k := k)).map (IndexedGadget.tupleEnumeration e e')).map _) ↔ _
  rw [histogram_equivalence_transport (k:=k) (IndexedGadget.tupleEnumeration e e') FiniteWL.edges _
    (IndexedGadget.edges_tupleEnumeration e e') (FiniteWL.initial FiniteWL.atomicGraph FiniteWL.atomicGraph) _
    (GraphMatrixPrograms.pointSignature_gadget e e') FiniteWL.leftTuples FiniteWL.rightTuples]
  have hG : (FiniteWL.atomicGraph : (Fin k→GadgetVertex G)→_)=graphInitial (gadgetAdj (G:=G)) k :=
    funext FiniteWL.atomicGraph_eq
  have hH : (FiniteWL.atomicGraph : (Fin k→GadgetVertex H)→_)=graphInitial (gadgetAdj (G:=H)) k :=
    funext FiniteWL.atomicGraph_eq
  simp only [FiniteWL.leftTuples,FiniteWL.rightTuples, Multiset.map_map, Function.comp_def,
    FiniteWL.labels_left,FiniteWL.labels_right,hG,hH,Equivalent,histogram]

theorem pair_runs (e : G≃Fin n) (e' : H≃Fin m) (S : State) (B : ℕ)
    (hS : S.Bounded B) (hleft : S.left.left.scalar (.inl 0)=n)
    (hright : S.left.right.scalar (.inl 0)=m) (hk : S.right.scalar (GraphWLCore.wl .arity)=k)
    (lword : S.left.left.array (.inl ())=GroupInitial.tableWord (GroupInitial.encodedMul e))
    (rword : S.left.right.array (.inl ())=GroupInitial.tableWord (GroupInitial.encodedMul e'))
    (lroom : (IndexedGadget.size n)^2≤B) (rroom : (IndexedGadget.size m)^2≤B)
    (matrix : GraphMatrixPrograms.Room (IndexedGadget.size n) (IndexedGadget.size m) k B)
    (room : IndexedWL.Room ((IndexedGadget.size n)^k+(IndexedGadget.size m)^k) k
      (max (IndexedGadget.size n) (IndexedGadget.size m)) B) :
    ∃t≤1500*(B+1)^7,∃T,Runs (storageBound Reg Arr B) decide S t T ∧ T.Bounded B ∧
    (T.right.scalar (GraphWLCore.wl .result)≠0 ↔
      Equivalent (graphInitial (gadgetAdj (G := G)) k) (graphInitial (gadgetAdj (G := H)) k)) := by
  obtain ⟨t,ht,U,first,hU,lc,rc,lAdj,rAdj⟩ := GadgetPairTables.generate_runs
    (GroupInitial.encodedMul e) (GroupInitial.encodedMul e')
    (by have := (e 1).isLt;omega) (by have := (e' 1).isLt;omega) S.left B hS.left
    hleft hright lword rword lroom rroom
  let V := U.join S.right
  have hV : V.Bounded B := hU.join hS.right
  obtain ⟨mid,hA⟩ := atoms_runs hV copyTables (by simp [copyTables,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let A := applyAtoms copyTables V
  have input : GraphWLCore.Input (k:=k) (IndexedGadget.numericAdj (GroupInitial.encodedMul e))
      (IndexedGadget.numericAdj (GroupInitial.encodedMul e')) B A.right := by
    refine ⟨hA.right,?_,?_,?_,?_,?_⟩
    · simpa [A,V,copyTables,applyAtoms,Atom.apply,Store.right,Store.left,Store.setScalar,Store.setArray,GraphWLCore.wl] using lc.size_eq
    · simpa [A,V,copyTables,applyAtoms,Atom.apply,Store.right,Store.left,Store.setScalar,Store.setArray,GraphWLCore.wl] using rc.size_eq
    · simpa [A,V,copyTables,applyAtoms,Atom.apply,Store.right,Store.left,Store.setScalar,Store.setArray,GraphWLCore.wl] using hk
    · simpa [A,V,copyTables,applyAtoms,Atom.apply,Store.right,Store.left,Store.setScalar,Store.setArray,GraphWLCore.array] using lAdj
    · simpa [A,V,copyTables,applyAtoms,Atom.apply,Store.right,Store.left,Store.setScalar,Store.setArray,GraphWLCore.array] using rAdj
  obtain ⟨u,hu,W,last,hW,result⟩ := GraphWLCore.fullDecide_runs _ _ A.right B input matrix room
  refine ⟨t+(4+u),?_,A.left.join W,.seq (first.left_bounded hS) (.seq mid (last.right_bounded hA)),
    hA.left.join hW,result.trans (semantic e e')⟩
  have hp : B+1 ≤(B+1)^7 := by
    simpa only [pow_one] using pow_le_pow_right' (by omega : 1≤B+1) (by decide : 1≤7)
  omega
end GroupWL.MachinePrograms.SimpleGadget
namespace GroupWL.MachinePrograms.SimpleGadget
open WLExponentialBudgets
theorem order_le {N n p : ℕ} (hp : 2≤p) (hn : n≤p^N) :
    IndexedGadget.size n ≤ p^(2*N+3) := by
  calc
    IndexedGadget.size n ≤ 5*n^2 := by unfold IndexedGadget.size; nlinarith [Nat.le_mul_self n]
    _ ≤ p^3*(p^N)^2 := Nat.mul_le_mul ((by decide : 5≤2^3).trans (Nat.pow_le_pow_left hp 3)) (Nat.pow_le_pow_left hn 2)
    _ = _ := by rw [show 2*N+3=N*2+3 by omega,pow_add,pow_mul]; ring

theorem exponentialRoom {N n m k p : ℕ} (hp : 2≤p) (ln : 0<n) (rn : 0<m)
    (lbound : n≤p^N) (rbound : m≤p^N) (kbound : k≤N+10) :
    let L := IndexedGadget.size n
    let R := IndexedGadget.size m
    let B := budget p (2*N+3)
    L^2≤B ∧ R^2≤B ∧ GraphMatrixPrograms.Room L R k B ∧ IndexedWL.Room (L^k+R^k) k (max L R) B := by
  obtain ⟨L,R,kc,one,M,_,T,P,A,W,V⟩ := room p (2*N+3) _ _ k (order_le hp lbound) (order_le hp rbound) (by omega)
  exact ⟨by simpa only [pow_two] using L,by simpa only [pow_two] using R,
    ⟨by unfold IndexedGadget.size; omega,by unfold IndexedGadget.size; omega,L,R,kc,one,by simpa only [pow_two] using M⟩,
    ⟨by simpa only [pow_two] using M,T,P,A,W,one,V⟩⟩

theorem exponentialCost (N p K d : ℕ) :
    K*(budget p (2*N+3)+1)^d ≤ 2^(((K+d*(coefficient p+1))*256)*(N+1)^4) := by
  refine (polynomial_bound p (2*N+3) K d).trans ?_
  apply pow_le_pow_right' (by decide)
  have h : (2*N+3+1)^4 ≤ (4*(N+1))^4 := Nat.pow_le_pow_left (by omega) 4
  have hh := Nat.mul_le_mul_left (K+d*(coefficient p+1)) h
  convert hh using 1
  ring
end GroupWL.MachinePrograms.SimpleGadget


namespace GroupWL.MachinePrograms.SimpleGadget
open NatArrayLanguage Refinement
variable {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H]
  [DecidableEq G] [DecidableEq H] {n m k : ℕ}
theorem pair_runs_III (e : G≃Fin n) (e' : H≃Fin m) (S : State) (B : ℕ)
    (positive : 0 < k) (hS : S.Bounded B) (hleft : S.left.left.scalar (.inl 0)=n)
    (hright : S.left.right.scalar (.inl 0)=m) (hk : S.right.scalar (GraphWLCore.wl .arity)=k)
    (lword : S.left.left.array (.inl ())=GroupInitial.tableWord (GroupInitial.encodedMul e))
    (rword : S.left.right.array (.inl ())=GroupInitial.tableWord (GroupInitial.encodedMul e'))
    (lroom : (IndexedGadget.size n)^2≤B) (rroom : (IndexedGadget.size m)^2≤B)
    (matrix : GraphMatrixPrograms.Room (IndexedGadget.size n) (IndexedGadget.size m) k B)
    (room : IndexedWL.Room ((IndexedGadget.size n)^k+(IndexedGadget.size m)^k) k
      (max (IndexedGadget.size n) (IndexedGadget.size m)) B) :
    ∃t≤1500*(B+1)^7,∃T,Runs (storageBound Reg Arr B) decide S t T ∧ T.Bounded B ∧
    (T.right.scalar (GraphWLCore.wl .result)≠0 ↔
      EquivalentIII k G H) := by
  obtain ⟨t,ht,T,run,mem,result⟩ := pair_runs e e' S B hS hleft hright hk lword rword lroom rroom matrix room
  exact ⟨t,ht,T,run,mem,result.trans (SimpleGadgetSemantics.all_positive_iff positive).symm⟩
end GroupWL.MachinePrograms.SimpleGadget
