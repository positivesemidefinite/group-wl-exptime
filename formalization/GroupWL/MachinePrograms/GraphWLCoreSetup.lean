import GroupWL.MachinePrograms.GraphWLCore

namespace GroupWL.MachinePrograms.GraphWLCore
open NatArrayLanguage IndexedRefinement
set_option maxRecDepth 8192
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
variable {n m k : ℕ}

abbrev core (S : State) : Store IndexedWL.Reg IndexedWL.Arr := S.left.left.right

structure Input {n m k : ℕ} (f : Fin n→Fin n→Bool) (g : Fin m→Fin m→Bool) (B : ℕ) (S : State) : Prop where
  bounded : S.Bounded B
  left_order : S.scalar (wl .leftCount)=n
  right_order : S.scalar (wl .rightCount)=m
  arity : S.scalar (wl .arity)=k
  left_table : S.array (array .fanouts)=GraphInitial.tableWord f
  right_table : S.array (array .targets)=GraphInitial.tableWord g

theorem setup_runs (f : Fin n→Fin n→Bool) (g : Fin m→Fin m→Bool)
    (S : State) (B : ℕ) (input : Input (k:=k) f g B S)
    (matrixRoom : GraphMatrixPrograms.Room n m k B)
    (room : IndexedWL.Room (n^k+m^k) k (max n m) B) :
    ∃t≤400*(B+1)^4,∃T,Runs (storageBound Reg Arr B) setup S t T ∧ T.Bounded B ∧
      IndexedWL.Input (IndexedTuples.data n m k matrixRoom.left_positive)
        (GraphMatrixPrograms.initialRelation f g) B (core T) ∧
      (core T).array .leftSelection=(core S).array .leftSelection ∧
      (core T).array .rightSelection=(core S).array .rightSelection := by
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
  have selectionV (a : IndexedWL.Arr) (ha : a=.leftSelection ∨ a=.rightSelection) :
      V.array (.inr a)=S.array (array a) := by
    rw [matrix.array_eq_of_not_mem (.inr a) (by rcases ha with rfl|rfl <;> decide)]
    rfl
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
      (GraphMatrixPrograms.initialRelation f g) B (core T) := by
    refine ⟨hT.left.left.right,?_,?_,?_,?_,?_,?_⟩
    · change T.scalar (wl .n)=n^k+m^k
      simp [T,applyAtoms,prepareWL,Atom.apply,Store.setScalar,Store.setArray,wl,dimensions]
      exact congrArg (fun Q : Store TupleDimensions.Reg TupleDimensions.Arr=>Q.scalar 10) dimensionsFrame |>.trans ut
    · simpa [T,F,E,core,applyAtoms,prepareWL,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,wl,array,dimensions,Sum.inr] using arityV
    · change T.scalar (wl .width)=max n m
      simp [T,applyAtoms,prepareWL,Atom.apply,Store.setScalar,Store.setArray,wl,dimensions]
      exact congrArg (fun Q : Store TupleDimensions.Reg TupleDimensions.Arr=>Q.scalar 11) dimensionsFrame |>.trans uw
    · simpa [T,F,E,core,applyAtoms,prepareWL,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,wl,array,dimensions,Sum.inr] using matrixV
    · simpa [T,F,core,applyAtoms,prepareWL,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,wl,array,dimensions] using fanouts
    · simpa [T,F,core,applyAtoms,prepareWL,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,wl,array,dimensions] using targets
  have selectL : (core T).array .leftSelection=(core S).array .leftSelection := by
    simpa [T,F,E,core,applyAtoms,prepareWL,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,wl,array,dimensions] using selectionV .leftSelection (Or.inl rfl)
  have selectR : (core T).array .rightSelection=(core S).array .rightSelection := by
    simpa [T,F,E,core,applyAtoms,prepareWL,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,wl,array,dimensions] using selectionV .rightSelection (Or.inr rfl)
  refine ⟨3+(t+(8+(u+(v+4)))),?_,T,.seq start (.seq dims' (.seq stage (.seq matrix' (.seq arrays' finish)))),hT,ready,selectL,selectR⟩
  have power : (B+1)^2≤(B+1)^4 := pow_le_pow_right' (by omega) (by omega)
  have linear : B+1≤(B+1)^4 := by simpa only [pow_one] using pow_le_pow_right' (by omega : 1≤B+1) (by omega : 1≤4)
  nlinarith

end GroupWL.MachinePrograms.GraphWLCore
