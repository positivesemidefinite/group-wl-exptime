import GroupWL.MachinePrograms.SeededSaturation
import GroupWL.MachinePrograms.PairedKernelScan
import GroupWL.MachinePrograms.ProductGroupOperation

/-! Concrete subgroup saturation followed by the two-kernel comparison. -/
namespace GroupWL.MachinePrograms.PairedClosureCheck
open NatArrayLanguage FiniteSetArrays
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

abbrev Reg := SeededSaturation.Reg ⊕ PairedKernelScan.Reg
abbrev Arr := SeededSaturation.Arr ⊕ PairedKernelScan.Arr
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr

def program : Code := .seq (SeededSaturation.saturate.map Sum.inl Sum.inl)
  (.seq (.atom (.copyArray (.inr ()) (.inl (.inr .current)))) (PairedKernelScan.scan.map Sum.inr Sum.inr))

variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
variable {n m k : ℕ}

theorem program_runs (e : G≃Fin n) (e' : H≃Fin m)
    (f : Fin n→Fin n→Fin n) (g : Fin m→Fin m→Fin m)
    (hf : ∀x y,e.symm (f x y)=e.symm x*e.symm y)
    (hg : ∀x y,e'.symm (g x y)=e'.symm x*e'.symm y)
    (a : Fin k→G) (b : Fin k→H) (S : State) (M : ℕ) (bounded : S.Bounded M)
    (seedOrder : S.scalar (.inl (.inl .order))=n*m)
    (identity : S.scalar (.inl (.inl .identity))=(finProdFinEquiv (e 1,e' 1)).val)
    (generators : S.array (.inl (.inl .generators))=
      List.ofFn (fun i : Fin k=>(finProdFinEquiv (e (a i),e' (b i))).val))
    (closureOrder : S.scalar (.inl (.inr .order))=n*m)
    (table : S.array (.inl (.inr .table))=GroupInitial.tableWord (ProductGroupTable.productOp f g))
    (scanOrder : S.scalar (.inr 0)=n*m) (rightOrder : S.scalar (.inr 1)=m)
    (leftOne : S.scalar (.inr 2)=(e 1).val) (rightOne : S.scalar (.inr 3)=(e' 1).val)
    (room : (n*m)*(n*m)≤M) :
    ∃t≤10*(n*m)^3+19*(n*m)+5*k+20,∃T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.scalar (.inr 7)≤1 ∧ (T.scalar (.inr 7)=1 ↔ FiniteWordTypes.sameWordType a b=true) := by
  let gs : List (Fin (n*m)) := List.ofFn (fun i : Fin k=>finProdFinEquiv (e (a i),e' (b i)))
  let identityIndex : Fin (n*m) := finProdFinEquiv (e 1,e' 1)
  let op := ProductGroupTable.productOp f g
  have hgens : S.left.array (.inl .generators)=gs.map Fin.val := by
    simpa [gs,List.map_ofFn] using generators
  have hread : ∀i : Fin ((n*m)*(n*m)),(S.left.array (.inr .table))[i.val]?.getD 0=
      (op (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2).val := by
    intro i
    change (S.array (.inl (.inr .table)))[i.val]?.getD 0=_
    rw [table]
    simp [GroupInitial.tableWord,i.isLt,op]
  obtain ⟨t,ht,U,close,hU,mask⟩ := SeededSaturation.saturate_runs S.left (n*m) M identityIndex gs op
    bounded.left seedOrder identity hgens closureOrder (by simp [Store.left,table]) hread room
  let V := U.join S.right
  have hV : V.Bounded M := hU.join bounded.right
  let copy : Atom Reg Arr := .copyArray (.inr ()) (.inl (.inr .current))
  let W := copy.apply V
  have copyRun := atom_runs hV copy trivial trivial
  have hW : W.Bounded M := copy.apply_bounded hV trivial
  have wmask : W.right.array ()=word (GroupSaturation.closureSet op (insert identityIndex gs.toFinset) (n*m)) := by
    simpa [W,copy,Atom.apply,Store.right,V] using mask
  have he : ∀x y,PairedKernelScan.pairEnumeration e e' (op x y)=
      PairedKernelScan.pairEnumeration e e' x*PairedKernelScan.pairEnumeration e e' y := by
    intro x y
    apply Prod.ext
    · simpa [PairedKernelScan.pairEnumeration,op,ProductGroupTable.productOp] using
        hf (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm y).1
    · simpa [PairedKernelScan.pairEnumeration,op,ProductGroupTable.productOp] using
        hg (finProdFinEquiv.symm x).2 (finProdFinEquiv.symm y).2
  have seedImage : (insert identityIndex gs.toFinset).image (PairedKernelScan.pairEnumeration e e')=
      insert 1 (Finset.univ.image (fun i=>(a i,b i))) := by
    have hgs : gs.toFinset=Finset.univ.image (fun i : Fin k=>finProdFinEquiv (e (a i),e' (b i))) := by
      ext x
      simp [gs]
    have pair (x : G) (y : H) : PairedKernelScan.pairEnumeration e e' (finProdFinEquiv (e x,e' y))=(x,y) := by
      unfold PairedKernelScan.pairEnumeration
      rw [Equiv.trans_apply,Equiv.symm_apply_apply]
      simp
    rw [hgs,Finset.image_insert,Finset.image_image]
    simp only [identityIndex,Function.comp_def,pair]
    rfl
  have hmask : ∀j : Fin (n*m),IndexedRefinement.read (W.right.array ()) j.val=1 ↔
      PairedKernelScan.pairEnumeration e e' j∈FiniteWordTypes.explore a b (Fintype.card (G×H)) := by
    intro j
    rw [wmask]
    change (word (GroupSaturation.closureSet op (insert identityIndex gs.toFinset) (n*m)))[j.val]?.getD 0=1 ↔ _
    rw [read_word]
    simpa using GroupSaturation.mask_closure_mem op (insert identityIndex gs.toFinset)
      (PairedKernelScan.pairEnumeration e e') he a b seedImage j
  obtain ⟨u,hu,X,scan,hX,xvalid,result⟩ := PairedKernelScan.scan_paired_runs e e' a b W.right M hW.right
    scanOrder rightOrder leftOne rightOne (by simp [wmask]) hmask
  refine ⟨t+(1+u),?_,W.left.join X,.seq (close.left_bounded bounded)
    (.seq copyRun (scan.right_bounded hW)),hW.left.join hX,xvalid,result⟩
  have hgslen : gs.length=k := List.length_ofFn
  rw [hgslen] at ht
  omega

end GroupWL.MachinePrograms.PairedClosureCheck
