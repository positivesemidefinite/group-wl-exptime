import GroupWL.MachinePrograms.ArrayMaterialization
import GroupWL.MachinePrograms.NatArrayFrames

/-! Gather the local relation matrix in numeric neighbor order. The input
coefficient table has two padded coordinates per block/readout pair. -/
namespace GroupWL.MachinePrograms.SourceRelationMatrix
open NatArrayLanguage
set_option maxHeartbeats 1200000

inductive Reg where
  | total | position | remaining | one | zero | degree | readouts | readout | two
  | coordinate | neighbor | block | address | result
  deriving DecidableEq, Fintype
inductive Arr where | coefficients | neighbors | output deriving DecidableEq, Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def registers : Fin 5 ↪ Reg := ⟨![.total,.position,.remaining,.one,.zero],by decide⟩

def cellAtoms : List (Atom Reg Arr) := [
  .divmod .coordinate .neighbor .position .degree,
  .read .block .neighbors .neighbor,
  .binary .mul .address .block .readouts,
  .binary .add .address .address .readout,
  .binary .mul .address .address .two,
  .binary .add .address .address .coordinate,
  .read .result .coefficients .address]

def program : Code := materialize registers .output .result (atoms cellAtoms)

def entry (coefficients neighbors : List ℕ) (r j g i : ℕ) : ℕ :=
  coefficients[((neighbors[i%g]?.getD 0)*r+j)*2+i/g]?.getD 0

def Ready (coefficients neighbors : List ℕ) (r j d g : ℕ) (S : State) : Prop :=
  S.array .coefficients=coefficients ∧ S.array .neighbors=neighbors ∧
  S.scalar .readouts=r ∧ S.scalar .readout=j ∧ S.scalar .degree=g ∧
  S.scalar .two=2 ∧ S.scalar .total=d*g

theorem cell_runs (coefficients neighbors : List ℕ) (b r j d g M : ℕ)
    (hj : j<r) (hd : d≤2) (hcoeff : b*r*2≤coefficients.length)
    (hcount : g≤neighbors.length) (hblocks : ∀ i<g, neighbors[i]?.getD 0<b)
    (S : State) (ready : Ready coefficients neighbors r j d g S) (bounded : S.Bounded M)
    (hi : S.scalar .position<d*g) :
    ∃ t ≤ 7, ∃ T, Runs (storageBound Reg Arr M) (atoms cellAtoms) S t T ∧
      T.Bounded M ∧ Ready coefficients neighbors r j d g T ∧
      T.scalar .result=entry coefficients neighbors r j g (S.scalar .position) ∧
      T.array .output=S.array .output ∧
      ∀ i : Fin 4, T.scalar (registers i.castSucc)=S.scalar (registers i.castSucc) := by
  rcases ready with ⟨hc,hn,hr,hj',hg,htwo,htotal⟩
  have hgpos : 0<g := by nlinarith
  have hk : S.scalar .position/g<d := (Nat.div_lt_iff_lt_mul hgpos).2 hi
  have hnidx : S.scalar .position%g<neighbors.length := (Nat.mod_lt _ hgpos).trans_le hcount
  have hblock := hblocks (S.scalar .position%g) (Nat.mod_lt _ hgpos)
  have haddr : ((neighbors[S.scalar .position%g]?.getD 0)*r+j)*2+S.scalar .position/g <
      coefficients.length := by
    apply lt_of_lt_of_le _ hcoeff
    have hpair : (neighbors[S.scalar .position%g]?.getD 0)*r+j < b*r := by
      calc _ < (neighbors[S.scalar .position%g]?.getD 0+1)*r := by nlinarith
           _ ≤ b*r := Nat.mul_le_mul_right _ (by omega)
    omega
  have hlenM : coefficients.length≤M := hc ▸ bounded.2.1 Arr.coefficients
  have hfinal : ((neighbors[S.scalar .position%g]?.getD 0)*r+j)*2+S.scalar .position/g≤M :=
    (Nat.le_of_lt haddr).trans hlenM
  have htwice : ((neighbors[S.scalar .position%g]?.getD 0)*r+j)*2≤M :=
    (Nat.le_add_right _ _).trans hfinal
  have hadd : (neighbors[S.scalar .position%g]?.getD 0)*r+j≤M :=
    (Nat.le_mul_of_pos_right _ (by decide : 0<2)).trans htwice
  have hmul : (neighbors[S.scalar .position%g]?.getD 0)*r≤M :=
    (Nat.le_add_right _ _).trans hadd
  have valid : ValidAtoms M cellAtoms S := by
    simp [cellAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,hc,hn,hr,hj',hg,htwo,hgpos,hnidx]
    simpa only [List.getElem?_eq_getElem hnidx,Option.getD_some] using
      And.intro hmul (And.intro hadd (And.intro htwice (And.intro hfinal haddr)))
  obtain ⟨run,hT⟩ := atoms_runs bounded cellAtoms valid
  refine ⟨7,le_rfl,applyAtoms cellAtoms S,run,hT,?_,?_,?_,?_⟩
  · simp [Ready,cellAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,hc,hn,hr,hj',hg,htwo,htotal]
  · simp [entry,cellAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,hc,hn,hr,hj',hg,htwo]
  · rfl
  · intro i
    fin_cases i <;> simp [registers,cellAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar]

theorem program_runs (coefficients neighbors : List ℕ) (b r j d g M : ℕ)
    (hj : j<r) (hd : d≤2) (hcoeff : b*r*2≤coefficients.length)
    (hcount : g≤neighbors.length) (hblocks : ∀ i<g, neighbors[i]?.getD 0<b)
    (S : State) (ready : Ready coefficients neighbors r j d g S) (bounded : S.Bounded M) (hM : 1≤M) :
    ∃ t ≤ d*g*11+6, ∃ T, Runs (storageBound Reg Arr M) program S t T ∧
      T.Bounded M ∧ Ready coefficients neighbors r j d g T ∧
      T.array .output=List.ofFn (fun i : Fin (d*g) => entry coefficients neighbors r j g i.val) := by
  apply materialize_runs registers .output .result (atoms cellAtoms)
    (Ready coefficients neighbors r j d g) (entry coefficients neighbors r j g) M (d*g) 7 hM
  · intro T hT i v
    fin_cases i <;> simpa [Ready,registers,Store.setScalar] using hT
  · intro T hT xs
    simpa [Ready,Store.setArray] using hT
  · exact fun T hT hb hi => cell_runs coefficients neighbors b r j d g M hj hd hcoeff hcount hblocks T hT hb hi
  · exact bounded
  · exact ready
  · exact ready.2.2.2.2.2.2

end GroupWL.MachinePrograms.SourceRelationMatrix
