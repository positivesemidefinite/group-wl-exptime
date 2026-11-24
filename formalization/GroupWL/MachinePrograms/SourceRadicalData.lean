import GroupWL.MachinePrograms.SourceRadicalClient
import GroupWL.MachinePrograms.MatrixScatterCorrectness

namespace GroupWL.MachinePrograms.SourceRadicalClient

def data (p : ℕ) (scope coefficients : List ℕ) (b r j d : ℕ) : KernelProgram.Data :=
  KernelProgram.executeRows (relation scope coefficients b r j d) p
    (SourceNeighbors.selected scope r j b).length d
    (KernelProgram.initial (SourceNeighbors.selected scope r j b).length)

theorem executeRows_valid (A : List ℕ) (p n m : ℕ) (D : KernelProgram.Data)
    (hp : 0<p) (hD : D.Valid p n) : (KernelProgram.executeRows A p n m D).Valid p n := by
  induction m generalizing D with
  | zero => exact hD
  | succ m ih => exact ih _ (KernelProgram.eliminate_valid p n _ D hp hD)

theorem data_valid (p : ℕ) (scope coefficients : List ℕ) (b r j d : ℕ) (hp : 1<p) :
    (data p scope coefficients b r j d).Valid p (SourceNeighbors.selected scope r j b).length :=
  executeRows_valid _ p _ d _ (by omega) (KernelProgram.initial_valid p _ hp)

end GroupWL.MachinePrograms.SourceRadicalClient

namespace GroupWL.MachinePrograms.MatrixScatter

theorem scatter_congr_neighbors (ns ns' values initial : List ℕ) (width stride offset n : ℕ)
    (h : ∀ i<n, ns[i/width]?.getD 0=ns'[i/width]?.getD 0) :
    scatter ns values initial width stride offset n=scatter ns' values initial width stride offset n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [scatter,scatter,ih (fun i hi => h i (by omega))]
    congr 1
    exact congrArg (fun x => x*stride+n%width+offset) (h n (by omega))

end GroupWL.MachinePrograms.MatrixScatter
