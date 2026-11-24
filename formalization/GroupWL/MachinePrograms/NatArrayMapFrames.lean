import GroupWL.MachinePrograms.NatArrayComponents
import GroupWL.MachinePrograms.NatArrayFrames

/-! Compute mapped-program effects without unfolding the mapped algorithm. -/
namespace GroupWL.MachinePrograms.NatArrayLanguage
variable {R A R' A' : Type*}
variable [DecidableEq R] [DecidableEq A] [DecidableEq R'] [DecidableEq A']

theorem Atom.scalarWrites_map (p : Atom R A) (r : R→R') (a : A→A') :
    (p.map r a).scalarWrites=p.scalarWrites.image r := by
  cases p <;> simp [Atom.map,Atom.scalarWrites]

theorem Atom.arrayWrites_map (p : Atom R A) (r : R→R') (a : A→A') :
    (p.map r a).arrayWrites=p.arrayWrites.image a := by
  cases p <;> simp [Atom.map,Atom.arrayWrites]

theorem Program.scalarWrites_map (p : Program R A) (r : R→R') (a : A→A') :
    (p.map r a).scalarWrites=p.scalarWrites.image r := by
  induction p with
  | skip => simp [Program.map,Program.scalarWrites]
  | atom p => exact p.scalarWrites_map r a
  | seq p q ihp ihq => simp [Program.map,Program.scalarWrites,ihp,ihq,Finset.image_union]
  | branch x p q ihp ihq => simp [Program.map,Program.scalarWrites,ihp,ihq,Finset.image_union]
  | «while» x p ih => simpa only [Program.map,Program.scalarWrites] using ih

theorem Program.arrayWrites_map (p : Program R A) (r : R→R') (a : A→A') :
    (p.map r a).arrayWrites=p.arrayWrites.image a := by
  induction p with
  | skip => simp [Program.map,Program.arrayWrites]
  | atom p => exact p.arrayWrites_map r a
  | seq p q ihp ihq => simp [Program.map,Program.arrayWrites,ihp,ihq,Finset.image_union]
  | branch x p q ihp ihq => simp [Program.map,Program.arrayWrites,ihp,ihq,Finset.image_union]
  | «while» x p ih => simpa only [Program.map,Program.arrayWrites] using ih

end GroupWL.MachinePrograms.NatArrayLanguage
