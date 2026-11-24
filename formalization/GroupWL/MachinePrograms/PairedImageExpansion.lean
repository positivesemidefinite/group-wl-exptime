import GroupWL.MachinePrograms.SeededSaturation
import GroupWL.MachinePrograms.GeneratorImageSemantics

/-! Concrete composition of tuple seeds, paired closure and row-wise image
expansion. The table and seed arrays are materialized inputs. -/
namespace GroupWL.MachinePrograms.PairedImageExpansion
open NatArrayLanguage FiniteSetArrays
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

abbrev Reg := SeededSaturation.Reg ⊕ GeneratorImages.Reg
abbrev Arr := SeededSaturation.Arr ⊕ GeneratorImages.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def expand : Code := sequence [
  SeededSaturation.saturate.map Sum.inl Sum.inl,
  .atom (.copyArray (.inr (.inl .input)) (.inl (.inr .current))),
  GeneratorImages.expand.map Sum.inr Sum.inr]

def imageArray : Arr := .inr (.inr .images)
def seedReg (r : GeneratorMask.Reg) : Reg := .inl (.inl r)
def seedArray (a : GeneratorMask.Arr) : Arr := .inl (.inl a)
def closureReg (r : GroupSaturation.Reg) : Reg := .inl (.inr r)
def closureArray (a : GroupSaturation.Arr) : Arr := .inl (.inr a)
def imageReg (r : GeneratorImages.Control) : Reg := .inr (.inr r)

theorem expand_runs (S : State) (rows cols M : ℕ) (e : Fin (rows*cols))
    (gs : List (Fin (rows*cols))) (identity : Fin cols)
    (op : Fin (rows*cols) → Fin (rows*cols) → Fin (rows*cols))
    (hb : S.Bounded M) (hn : S.scalar (seedReg .order)=rows*cols)
    (he : S.scalar (seedReg .identity)=e.val) (hgs : S.array (seedArray .generators)=gs.map Fin.val)
    (hn' : S.scalar (closureReg .order)=rows*cols)
    (htable : (S.array (closureArray .table)).length=(rows*cols)*(rows*cols))
    (hread : ∀i : Fin ((rows*cols)*(rows*cols)),(S.array (closureArray .table))[i.val]?.getD 0=
      (op (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2).val)
    (hrows : S.scalar (imageReg .rows)=rows) (hcols : S.scalar (imageReg .cols)=cols)
    (hidentity : S.scalar (imageReg .identity)=identity.val)
    (hroom : (rows*cols)*(rows*cols)≤M) :
    ∃t≤10*(rows*cols)^3+8*(rows*cols)+5*gs.length+rows*(9*cols+13)+20,∃T,
      Runs (storageBound Reg Arr M) expand S t T ∧ T.Bounded M ∧
      T.array imageArray=List.ofFn (fun x : Fin rows => GeneratorImages.rowImage
        (word (GroupSaturation.closureSet op (insert e gs.toFinset) (rows*cols))) cols identity.val x.val) := by
  obtain ⟨t,ht,U,close,hU,ho⟩ := SeededSaturation.saturate_runs S.left (rows*cols) M e gs op
    hb.left hn he hgs hn' htable hread hroom
  let V := U.join S.right
  have hV : V.Bounded M := hU.join hb.right
  let W := (Atom.copyArray (Sum.inr (Sum.inl FirstNonzero.Arr.input))
    (Sum.inl (Sum.inr GroupSaturation.Arr.current))).apply V
  have hW : W.Bounded M := Atom.apply_bounded hV _ trivial
  have copy := atom_runs hV (.copyArray (.inr (.inl .input)) (.inl (.inr .current))) trivial trivial
  have hcurrent : W.right.array (.inl .input)=word (GroupSaturation.closureSet op (insert e gs.toFinset) (rows*cols)) := by
    simpa [W,Atom.apply,Store.right,V] using ho
  have hpos : 0<rows*cols := by have := e.isLt; omega
  have hM : 1≤M := by nlinarith
  have hsize : rows*cols≤M := by nlinarith
  obtain ⟨u,hu,X,images,hX,hout⟩ := GeneratorImages.expand_runs W.right M rows cols identity.val hW.right
    (by simpa [W,Atom.apply,Store.right,V,imageReg] using hrows)
    (by simpa [W,Atom.apply,Store.right,V,imageReg] using hcols)
    (by simpa [W,Atom.apply,Store.right,V,imageReg] using hidentity) identity.isLt
    (by simp [hcurrent]) hsize hM
  have expanded := images.right_bounded hW
  refine ⟨t+(1+(u+0)),by omega,W.left.join X,
    .seq (close.left_bounded hb) (.seq copy (.seq expanded (.skip expanded.end_bound))),hW.left.join hX,?_⟩
  simpa [imageArray,hcurrent] using hout

theorem image_values {cols : ℕ} (identity : Fin cols) (xs : List ℕ) (rows : ℕ) :
    ∀v∈List.ofFn (fun x : Fin rows => GeneratorImages.rowImage xs cols identity.val x.val),v<cols := by
  intro v hv
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
  exact FirstNonzero.hit_getD_lt xs _ cols identity.val identity.isLt

end GroupWL.MachinePrograms.PairedImageExpansion
