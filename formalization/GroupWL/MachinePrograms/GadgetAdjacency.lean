import GroupWL.IndexedGadget
import GroupWL.MachinePrograms.NatArrayBoolean

/-! Evaluate a multiplication-graph edge using only numeric primitives. -/
namespace GroupWL.MachinePrograms.GadgetAdjacency
open NatArrayLanguage
abbrev Reg := Fin 24
abbrev Arr := Unit
abbrev Code := Program Reg Arr
set_option maxRecDepth 4096

def prepare : List (Atom Reg Arr) := [
  .const 3 0,.const 4 1,.const 5 4,.const 6 3,
  .binary .lt 7 1 0,.binary .lt 8 2 0,
  .binary .sub 9 1 0,.binary .sub 10 2 0,
  .divmod 11 12 9 5,.divmod 13 14 10 5,
  .divmod 15 16 11 0,.divmod 17 18 13 0,
  .read 19 () 11,.read 20 () 13,
  .binary .add 21 12 4,.binary .add 22 14 4]

def attachment (v g h j prod : Reg) : BooleanTest Reg :=
  .any (.all (.equal j 3) (.equal v g))
    (.any (.all (.equal j 4) (.equal v h)) (.all (.equal j 6) (.equal v prod)))

def formula : BooleanTest Reg :=
  .any (.all (.equal 7 4) (.all (.equal 8 3) (attachment 1 17 18 14 20)))
    (.any (.all (.equal 7 3) (.all (.equal 8 4) (attachment 2 15 16 12 19)))
      (.all (.equal 7 3) (.all (.equal 8 3)
        (.all (.equal 11 13) (.any (.equal 21 14) (.equal 22 12))))))

def evaluate : Code := .seq (atoms prepare) (formula.compile 23)

theorem evaluate_runs (n : ℕ) (hnpos : 0<n) (x y : Fin (IndexedGadget.size n))
    (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B) (hn : S.scalar 0=n)
    (hx : S.scalar 1=x.val) (hy : S.scalar 2=y.val) (hlen : (S.array ()).length=n*n) (h4 : 4≤B) :
    ∃ t≤200,∃ T,Runs (storageBound Reg Arr B) evaluate S t T ∧ T.Bounded B ∧
      T.scalar 23=IndexedRefinement.boolNat (IndexedGadget.test n (S.array ()) x.val y.val) := by
  have hxB : x.val≤B := by simpa [hx] using hS.1 1
  have hyB : y.val≤B := by simpa [hy] using hS.1 2
  have hpairx := IndexedGadget.pairIndex_lt hnpos x
  have hpairy := IndexedGadget.pairIndex_lt hnpos y
  have htagx : (x.val-n)%4+1≤B := by have := Nat.mod_lt (x.val-n) (by decide : 0<4);omega
  have htagy : (y.val-n)%4+1≤B := by have := Nat.mod_lt (y.val-n) (by decide : 0<4);omega
  have valid : ValidAtoms B prepare S := by
    simp [prepare,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,
      hn,hx,hy,hlen,hnpos,IndexedGadget.pairIndex] at hpairx hpairy ⊢
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    constructor
    · split_ifs <;>omega
    constructor
    · split_ifs <;>omega
    exact ⟨by omega,by omega,hpairx,hpairy,htagx,htagy⟩
  obtain ⟨init,hU⟩ := atoms_runs hS prepare valid
  let U := applyAtoms prepare S
  obtain ⟨t,ht,T,run,hT,hresult⟩ := BooleanTest.compile_runs formula 23 U B hU (by omega) (by decide)
  have he : formula.eval U=IndexedGadget.test n (S.array ()) x.val y.val := by
    by_cases hxx : x.val<n <;> by_cases hyy : y.val<n <;>
      simp [formula,attachment,BooleanTest.eval,U,applyAtoms,prepare,Atom.apply,BinaryOp.eval,
        Store.setScalar,hn,hx,hy,IndexedGadget.test,IndexedGadget.attachment,IndexedGadget.pairIndex,
        IndexedGadget.tag,IndexedRefinement.read,hxx,hyy]
  refine ⟨16+t,?_,T,Runs.seq init run,hT,?_⟩
  · have : 2*formula.size≤184 := by decide
    omega
  · simpa [he] using hresult
end GroupWL.MachinePrograms.GadgetAdjacency
