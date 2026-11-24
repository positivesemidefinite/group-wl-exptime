import GroupWL.MachinePrograms.PairedGenerators
import GroupWL.MachinePrograms.PairedImageExpansion
import GroupWL.NumericGroupImages

/-! Assemble paired seed indices, saturate the paired multiplication table,
and materialize the complete function proposed by the generator images. -/
namespace GroupWL.MachinePrograms.GroupImageExpansion
open NatArrayLanguage
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

abbrev Reg := PairedGenerators.Reg ⊕ PairedImageExpansion.Reg
abbrev Arr := PairedGenerators.Arr ⊕ PairedImageExpansion.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def imageArray : Arr := .inr PairedImageExpansion.imageArray

def expand : Code := sequence [
  PairedGenerators.build.map Sum.inl Sum.inl,
  .atom (.copyArray (.inr (PairedImageExpansion.seedArray .generators)) (.inl .output)),
  PairedImageExpansion.expand.map Sum.inr Sum.inr]

open PairedImageExpansion in
structure Ready {n m : ℕ} (identity : Fin n) (identity' : Fin m) (table : List ℕ) (S : State) : Prop where
  pairCols : S.scalar (.inl .cols)=m
  seedOrder : S.scalar (.inr (seedReg .order))=n*m
  seedIdentity : S.scalar (.inr (seedReg .identity))=(finProdFinEquiv (identity,identity')).val
  closureOrder : S.scalar (.inr (closureReg .order))=n*m
  table_eq : S.array (.inr (closureArray .table))=table
  imageRows : S.scalar (.inr (imageReg .rows))=n
  imageCols : S.scalar (.inr (imageReg .cols))=m
  imageIdentity : S.scalar (.inr (imageReg .identity))=identity'.val

open PairedImageExpansion in
theorem expand_runs {n m k : ℕ} (S : State) (M : ℕ)
    (identity : Fin n) (identity' : Fin m)
    (op : Fin n→Fin n→Fin n) (op' : Fin m→Fin m→Fin m)
    (a : Fin k→Fin n) (b : Fin k→Fin m) (table : List ℕ)
    (hb : S.Bounded M) (hready : Ready identity identity' table S)
    (ha : S.array (.inl .left)=List.ofFn (fun i => (a i).val))
    (hb' : S.array (.inl .right)=List.ofFn (fun i => (b i).val))
    (hlen : table.length=(n*m)*(n*m))
    (hread : ∀i : Fin ((n*m)*(n*m)),table[i.val]?.getD 0=
      (ProductGroupTable.productOp op op' (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2).val)
    (hroom : (n*m)*(n*m)≤M) :
    ∃t≤10*(n*m)^3+8*(n*m)+13*k+n*(9*m+13)+28,∃T,
      Runs (storageBound Reg Arr M) expand S t T ∧ T.Bounded M ∧
      T.array imageArray=List.ofFn (fun x : Fin n => (NumericGroupImages.expand op op' identity identity' a b x).val) := by
  have hpos : 0<n*m := Nat.mul_pos (Nat.zero_lt_of_lt identity.isLt) (Nat.zero_lt_of_lt identity'.isLt)
  have hM : 1≤M := by nlinarith
  have hsize : n*m≤M := by nlinarith
  obtain ⟨t,ht,U,pair,hU,ho⟩ := PairedGenerators.build_runs a b S.left M hb.left hready.pairCols ha hb' hsize hM
  let V := U.join S.right
  have hV : V.Bounded M := hU.join hb.right
  let W := (Atom.copyArray (Sum.inr (seedArray .generators)) (Sum.inl PairedGenerators.Arr.output)).apply V
  have hW : W.Bounded M := Atom.apply_bounded hV _ trivial
  have copy := atom_runs hV (.copyArray (.inr (seedArray .generators)) (.inl .output)) trivial trivial
  have hgs : W.right.array (seedArray .generators)=
      (List.ofFn (fun i => finProdFinEquiv (a i,b i))).map Fin.val := by
    simpa [W,Atom.apply,Store.right,V,List.map_ofFn] using ho
  have htab : W.right.array (closureArray .table)=table := by
    simpa [W,Atom.apply,Store.right,V,seedArray,closureArray] using hready.table_eq
  obtain ⟨u,hu,X,images,hX,hout⟩ := PairedImageExpansion.expand_runs W.right n m M
    (finProdFinEquiv (identity,identity')) (List.ofFn (fun i => finProdFinEquiv (a i,b i))) identity'
    (ProductGroupTable.productOp op op') hW.right
    (by simpa [W,Atom.apply,Store.right,V] using hready.seedOrder)
    (by simpa [W,Atom.apply,Store.right,V] using hready.seedIdentity) hgs
    (by simpa [W,Atom.apply,Store.right,V] using hready.closureOrder)
    (by simpa [htab] using hlen)
    (by simpa [htab] using hread)
    (by simpa [W,Atom.apply,Store.right,V] using hready.imageRows)
    (by simpa [W,Atom.apply,Store.right,V] using hready.imageCols)
    (by simpa [W,Atom.apply,Store.right,V] using hready.imageIdentity) hroom
  have expanded := images.right_bounded hW
  refine ⟨t+(1+(u+0)),by simp only [List.length_ofFn] at hu; omega,W.left.join X,
    .seq (pair.left_bounded hb) (.seq copy (.seq expanded (.skip expanded.end_bound))),hW.left.join hX,?_⟩
  have hset : (List.ofFn (fun i => finProdFinEquiv (a i,b i))).toFinset=
      Finset.univ.image (fun i => finProdFinEquiv (a i,b i)) := by ext x; simp
  simpa [imageArray,NumericGroupImages.expand,NumericGroupImages.mask,NumericGroupImages.seeds,hset] using hout

open PairedImageExpansion in
theorem ready_frame {n m : ℕ} {identity : Fin n} {identity' : Fin m} {table : List ℕ}
    {B S T t} (h : Runs B expand S t T) (hs : Ready identity identity' table S) :
    Ready identity identity' table T := by
  exact ⟨(h.scalar_eq_of_not_mem _ (by decide)).trans hs.pairCols,
    (h.scalar_eq_of_not_mem _ (by decide)).trans hs.seedOrder,
    (h.scalar_eq_of_not_mem _ (by decide)).trans hs.seedIdentity,
    (h.scalar_eq_of_not_mem _ (by decide)).trans hs.closureOrder,
    (h.array_eq_of_not_mem _ (by decide)).trans hs.table_eq,
    (h.scalar_eq_of_not_mem _ (by decide)).trans hs.imageRows,
    (h.scalar_eq_of_not_mem _ (by decide)).trans hs.imageCols,
    (h.scalar_eq_of_not_mem _ (by decide)).trans hs.imageIdentity⟩

theorem left_frame {B S T t} (h : Runs B expand S t T) :
    T.array (.inl .left)=S.array (.inl .left) := h.array_eq_of_not_mem _ (by decide)

theorem right_frame {B S T t} (h : Runs B expand S t T) :
    T.array (.inl .right)=S.array (.inl .right) := h.array_eq_of_not_mem _ (by decide)

end GroupWL.MachinePrograms.GroupImageExpansion
