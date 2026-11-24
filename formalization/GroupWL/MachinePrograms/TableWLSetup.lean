import GroupWL.MachinePrograms.TableWL
import GroupWL.MachinePrograms.WordMatrixAssembly

/-! Correctness of the complete two-table preparation phase. -/
namespace GroupWL.MachinePrograms.TableWL
open NatArrayLanguage IndexedRefinement
set_option maxRecDepth 8192
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

variable {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
variable {n m k : ℕ}

def relation (word : Bool) (e : G≃Fin n) (e' : H≃Fin m)
    (f : Fin n→Fin n→Fin n) (g : Fin m→Fin m→Fin m) : Finset (Fin (n^k+m^k)×Fin (n^k+m^k)) :=
  if word then WordMatrixPrograms.initialRelation e e' else InitialMatrixPrograms.initialRelation f g

def initialEq (word : Bool) (e : G≃Fin n) (e' : H≃Fin m)
    (f : Fin n→Fin n→Fin n) (g : Fin m→Fin m→Fin m) : Fin (n^k+m^k)→Fin (n^k+m^k)→Bool :=
  if word then WordMatrixSemantics.initialEq e e' else InitialMatrixPrograms.initialEq f g

theorem relation_zero (word : Bool) (e : G≃Fin n) (e' : H≃Fin m)
    (f : Fin n→Fin n→Fin n) (g : Fin m→Fin m→Fin m)
    (edges : Fin (n^k+m^k)→Multiset (Fin k→Fin (n^k+m^k))) :
    relation word e e' f g=CompressedRefinement.table edges (initialEq word e e' f g) 0 := by
  cases word <;> rfl

theorem matrix_runs (word : Bool) (e : G≃Fin n) (e' : H≃Fin m)
    (f : Fin n→Fin n→Fin n) (g : Fin m→Fin m→Fin m)
    (hf : ∀x y,e.symm (f x y)=e.symm x*e.symm y)
    (hg : ∀x y,e'.symm (g x y)=e'.symm x*e'.symm y)
    (leftZero : (e 1).val=0) (rightZero : (e' 1).val=0)
    (S : WordMatrixPrograms.State) (B : ℕ) (bounded : S.Bounded B)
    (input : InitialMatrixPrograms.Input (k:=k) f g B S.left)
    (room : InitialMatrixPrograms.Room n m k B) (productRoom : (max n m)^4≤B) :
    ∃t≤210*(B+1)^4,∃T,Runs (storageBound WordMatrixPrograms.Reg WordMatrixPrograms.Arr B)
      (matrixProgram word) S t T ∧ T.Bounded B ∧ T.scalar (WordMatrixPrograms.wl .arity)=k ∧
      T.array (WordMatrixPrograms.array .matrix)=matrixWord (relation (k:=k) word e e' f g) := by
  cases word
  · obtain ⟨t,ht,U,run,ctx,out⟩ := InitialMatrixPrograms.build_runs f g S.left room input
    have bound := ht.trans (InitialMatrixPrograms.build_cost_le room)
    have power : (B+1)^2≤(B+1)^4 := pow_le_pow_right' (by omega) (by omega)
    exact ⟨t,by nlinarith,U.join S.right,run.left_bounded bounded,ctx.bounded.join bounded.right,ctx.arity_eq,out⟩
  · obtain ⟨t,ht,T,run,hT,ctx,out⟩ := WordMatrixPrograms.build_runs e e' f g hf hg leftZero rightZero
      S B bounded input.left_eq input.right_eq input.arity_eq input.cutoff_eq input.total_eq
      input.left_table input.right_table productRoom room.matrix
    exact ⟨t,ht,T,run,hT,ctx.arity_eq,out⟩

abbrev core (S : State) : Store IndexedWL.Reg IndexedWL.Arr := S.left.left.left.right

structure Input {n m k : ℕ} (f : Fin n→Fin n→Fin n) (g : Fin m→Fin m→Fin m) (B : ℕ) (S : State) : Prop where
  bounded : S.Bounded B
  left_order : S.scalar (wl .leftCount)=n
  right_order : S.scalar (wl .rightCount)=m
  arity : S.scalar (wl .arity)=k
  left_table : S.array (array .fanouts)=GroupInitial.tableWord f
  right_table : S.array (array .targets)=GroupInitial.tableWord g

theorem setup_runs (word : Bool) (e : G≃Fin n) (e' : H≃Fin m)
    (f : Fin n→Fin n→Fin n) (g : Fin m→Fin m→Fin m)
    (hf : ∀x y,e.symm (f x y)=e.symm x*e.symm y)
    (hg : ∀x y,e'.symm (g x y)=e'.symm x*e'.symm y)
    (leftZero : (e 1).val=0) (rightZero : (e' 1).val=0)
    (S : State) (B : ℕ) (input : Input (k:=k) f g B S)
    (matrixRoom : InitialMatrixPrograms.Room n m k B) (productRoom : (max n m)^4≤B)
    (room : IndexedWL.Room (n^k+m^k) k (max n m) B) :
    ∃t≤400*(B+1)^4,∃T,Runs (storageBound Reg Arr B) (setup word) S t T ∧ T.Bounded B ∧
      IndexedWL.Input (IndexedTuples.data n m k matrixRoom.left_positive)
        (relation word e e' f g) B (core T) ∧
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
  have din : InitialMatrixPrograms.Input (k:=k) f g B D.left.left.left := by
    refine ⟨hD.left.left.left,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [D,C,A,applyAtoms,prepareTables,prepareDimensions,Atom.apply,Store.left,Store.setScalar,dimensions,wl,target,selection] using input.left_order
    · simpa [D,C,A,applyAtoms,prepareTables,prepareDimensions,Atom.apply,Store.left,Store.setScalar,dimensions,wl,target,selection] using input.right_order
    · simpa [D,C,A,applyAtoms,prepareTables,prepareDimensions,Atom.apply,Store.left,Store.setScalar,dimensions,wl,target,selection] using input.arity
    · simp [D,C,applyAtoms,prepareTables,Atom.apply,Store.left,Store.setScalar,dimensions,wl,target,selection,WordMatrixPrograms.wl,ul]
    · simp [D,C,applyAtoms,prepareTables,Atom.apply,Store.left,Store.setScalar,dimensions,wl,target,selection,WordMatrixPrograms.wl,ut]
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
  obtain ⟨u,hu,V,matrix,hV,arityV,matrixV⟩ := matrix_runs word e e' f g hf hg leftZero rightZero
    D.left.left B hD.left.left din matrixRoom productRoom
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
  obtain ⟨finish,hT⟩ := atoms_runs hF prepareWL
    (by simp [prepareWL,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let T := applyAtoms prepareWL F
  have dimensionsFrame : F.right=U := by
    apply Store.ext <;> intro r <;>
      simp [F,E,D,C,applyAtoms,prepareTables,Atom.apply,Store.right,Store.setScalar,dimensions,wl,target,selection]
  have ready : IndexedWL.Input (IndexedTuples.data n m k matrixRoom.left_positive)
      (relation word e e' f g) B (core T) := by
    refine ⟨hT.left.left.left.right,?_,?_,?_,?_,?_,?_⟩
    · change T.scalar (wl .n)=n^k+m^k
      simp [T,applyAtoms,prepareWL,Atom.apply,Store.setScalar,Store.setArray,wl,dimensions]
      exact congrArg (fun Q : Store TupleDimensions.Reg TupleDimensions.Arr=>Q.scalar 10) dimensionsFrame |>.trans ut
    · simpa [T,F,E,core,applyAtoms,prepareWL,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,wl,array,dimensions,WordMatrixPrograms.wl] using arityV
    · change T.scalar (wl .width)=max n m
      simp [T,applyAtoms,prepareWL,Atom.apply,Store.setScalar,Store.setArray,wl,dimensions]
      exact congrArg (fun Q : Store TupleDimensions.Reg TupleDimensions.Arr=>Q.scalar 11) dimensionsFrame |>.trans uw
    · simpa [T,F,E,core,applyAtoms,prepareWL,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,wl,array,dimensions,WordMatrixPrograms.array] using matrixV
    · simpa [T,F,core,applyAtoms,prepareWL,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,wl,array,dimensions] using fanouts
    · simpa [T,F,core,applyAtoms,prepareWL,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,wl,array,dimensions] using targets
  have selectL : (core T).array .leftSelection=(IndexedTuples.leftSelection n m k).map Fin.val := by
    simpa [T,F,core,applyAtoms,prepareWL,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,wl,array,dimensions] using lefts
  have selectR : (core T).array .rightSelection=(IndexedTuples.rightSelection n m k).map Fin.val := by
    simpa [T,F,core,applyAtoms,prepareWL,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,wl,array,dimensions] using rights
  refine ⟨3+(t+(8+(u+(v+6)))),?_,T,.seq start (.seq dims' (.seq stage (.seq matrix' (.seq arrays' finish)))),hT,ready,selectL,selectR⟩
  have power : (B+1)^2≤(B+1)^4 := pow_le_pow_right' (by omega) (by omega)
  have linear : B+1≤(B+1)^4 := by simpa only [pow_one] using pow_le_pow_right' (by omega : 1≤B+1) (by omega : 1≤4)
  nlinarith

end GroupWL.MachinePrograms.TableWL
