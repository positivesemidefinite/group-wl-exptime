import GroupWL.MachinePrograms.GroupImageExpansion
import GroupWL.MachinePrograms.ProductGroupTable

/-! Initialize and run the complete group-image expansion from two ordinary
multiplication tables and two tuple arrays. -/
namespace GroupWL.MachinePrograms.GroupImageClient
open NatArrayLanguage
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

abbrev Reg := ProductGroupTable.Reg ⊕ GroupImageExpansion.Reg
abbrev Arr := ProductGroupTable.Arr ⊕ GroupImageExpansion.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr
instance : DecidableEq Reg := inferInstance
instance : DecidableEq Arr := inferInstance
instance : Fintype Reg := inferInstance
instance : Fintype Arr := inferInstance

def r (x : PairedImageExpansion.Reg) : Reg := .inr (.inr x)
def ar (x : PairedImageExpansion.Arr) : Arr := .inr (.inr x)
def identityReg : Reg := r (PairedImageExpansion.seedReg .identity)
def identityReg' : Reg := r (PairedImageExpansion.imageReg .identity)
def leftTuple : Arr := .inr (.inl .left)
def rightTuple : Arr := .inr (.inl .right)
def imageArray : Arr := .inr GroupImageExpansion.imageArray

def prepare : List (Atom Reg Arr) := [
  .copy (.inr (.inl .cols)) (.inl 1),
  .binary .mul (r (PairedImageExpansion.seedReg .order)) (.inl 0) (.inl 1),
  .binary .mul identityReg identityReg (.inl 1),
  .binary .add identityReg identityReg identityReg',
  .copy (r (PairedImageExpansion.closureReg .order)) (r (PairedImageExpansion.seedReg .order)),
  .copyArray (ar (PairedImageExpansion.closureArray .table)) (.inl 2),
  .copy (r (PairedImageExpansion.imageReg .rows)) (.inl 0),
  .copy (r (PairedImageExpansion.imageReg .cols)) (.inl 1)]

def expand : Code := sequence [ProductGroupTable.generate.map Sum.inl Sum.inl,
  atoms prepare,GroupImageExpansion.expand.map Sum.inr Sum.inr]

theorem expand_runs {n m k : ℕ} (S : State) (M : ℕ)
    (op : Fin n→Fin n→Fin n) (op' : Fin m→Fin m→Fin m)
    (identity : Fin n) (identity' : Fin m) (a : Fin k→Fin n) (b : Fin k→Fin m)
    (hb : S.Bounded M) (hn : S.scalar (.inl 0)=n) (hm : S.scalar (.inl 1)=m)
    (hi : S.scalar identityReg=identity.val) (hi' : S.scalar identityReg'=identity'.val)
    (hs : S.array (.inl 0)=GroupInitial.tableWord op) (ht : S.array (.inl 1)=GroupInitial.tableWord op')
    (ha : S.array leftTuple=GroupInitial.tupleWord a) (hb' : S.array rightTuple=GroupInitial.tupleWord b)
    (hroom : (n*m)*(n*m)≤M) :
    ∃t≤10*(n*m)^3+15*((n*m)*(n*m))+8*(n*m)+13*k+n*(9*m+13)+44,∃T,
      Runs (storageBound Reg Arr M) expand S t T ∧ T.Bounded M ∧
      T.array imageArray=GroupInitial.tupleWord (NumericGroupImages.expand op op' identity identity' a b) := by
  have hpos : 0<n*m := Nat.mul_pos (Nat.zero_lt_of_lt identity.isLt) (Nat.zero_lt_of_lt identity'.isLt)
  have hN : n*m≤M := by nlinarith
  obtain ⟨t,htime,U,product,hU,ho⟩ := ProductGroupTable.generate_runs op op' S.left M hb.left hn hm hs ht hpos hroom
  let V := U.join S.right
  have hV : V.Bounded M := hU.join hb.right
  have hnV : V.scalar (.inl 0)=n := (product.scalar_eq_of_not_mem 0 (by decide)).trans hn
  have hmV : V.scalar (.inl 1)=m := (product.scalar_eq_of_not_mem 1 (by decide)).trans hm
  have hiV : V.scalar identityReg=identity.val := hi
  have hiV' : V.scalar identityReg'=identity'.val := hi'
  have hmul : identity.val*m≤M := by nlinarith [identity.isLt]
  have hadd : identity.val*m+identity'.val≤M := by nlinarith [identity.isLt,identity'.isLt]
  have hv : ValidAtoms M prepare V := by
    simp [prepare,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Store.setArray,r,ar,identityReg,identityReg',
      PairedImageExpansion.seedReg,PairedImageExpansion.closureReg,PairedImageExpansion.imageReg,
      PairedImageExpansion.closureArray] at hiV hiV' ⊢
    simp [hnV,hmV,hiV,hiV',hN,hmul,hadd]
  obtain ⟨prep,hW⟩ := atoms_runs hV prepare hv
  let W := applyAtoms prepare V
  dsimp only [identityReg,r,PairedImageExpansion.seedReg] at hiV
  dsimp only [identityReg',r,PairedImageExpansion.imageReg] at hiV'
  have hready : GroupImageExpansion.Ready identity identity'
      (GroupInitial.tableWord (ProductGroupTable.productOp op op')) W.right := by
    constructor <;> simp [W,applyAtoms,prepare,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,
      r,ar,identityReg,identityReg',Store.right,PairedImageExpansion.seedReg,
      PairedImageExpansion.closureReg,PairedImageExpansion.closureArray,PairedImageExpansion.imageReg]
    all_goals first
      | exact hmV
      | exact hnV
      | exact hiV'
      | exact ho
      | simpa [finProdFinEquiv,Nat.add_comm,Nat.mul_comm,hnV,hmV,hiV,hiV']
  have hleft : W.right.array (.inl .left)=GroupInitial.tupleWord a := by
    simpa [W,applyAtoms,prepare,Atom.apply,Store.setScalar,Store.setArray,Store.right,V,
      r,ar,PairedImageExpansion.closureArray,leftTuple] using ha
  have hright : W.right.array (.inl .right)=GroupInitial.tupleWord b := by
    simpa [W,applyAtoms,prepare,Atom.apply,Store.setScalar,Store.setArray,Store.right,V,
      r,ar,PairedImageExpansion.closureArray,rightTuple] using hb'
  obtain ⟨u,hu,X,images,hX,hout⟩ := GroupImageExpansion.expand_runs W.right M identity identity' op op' a b
    (GroupInitial.tableWord (ProductGroupTable.productOp op op')) hW.right hready hleft hright
    (by simp) (by intro i; simp [GroupInitial.tableWord]) hroom
  have expanded := images.right_bounded hW
  refine ⟨t+(8+(u+0)),by omega,W.left.join X,
    .seq (product.left_bounded hb) (.seq prep (.seq expanded (.skip expanded.end_bound))),hW.left.join hX,?_⟩
  exact hout

end GroupWL.MachinePrograms.GroupImageClient
