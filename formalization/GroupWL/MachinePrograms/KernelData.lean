import GroupWL.MachinePrograms.KernelClients

namespace GroupWL.MachinePrograms.KernelProgram
open NatArrayLanguage

structure Data.Valid (p n : ℕ) (D : Data) : Prop where
  width : D.width≤n
  liftLength : D.lift.length=n*D.width
  lowerLength : D.lowerTranspose.length=n*D.width
  liftValues : ∀x∈D.lift,x<p
  lowerValues : ∀x∈D.lowerTranspose,x<p

@[simp] theorem matrixProduct_length (A B : List ℕ) (r k c p : ℕ) :
    (matrixProduct A B r k c p).length=r*c := by simp [matrixProduct]

theorem matrixProduct_values (A B : List ℕ) (r k c p : ℕ) (positive : 0<p) :
    ∀x∈matrixProduct A B r k c p,x<p := by
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  exact Nat.mod_lt _ positive

@[simp] theorem equation_length (A : List ℕ) (n i p : ℕ) (D : Data) :
    (equation A n i p D).length=D.width := by simp [equation]

theorem equation_values (A : List ℕ) (n i p : ℕ) (D : Data) (positive : 0<p) :
    ∀x∈equation A n i p D,x<p := matrixProduct_values _ _ _ _ _ _ positive

theorem diagonalPrefix_values (n i : ℕ) : ∀x∈IdentityMatrix.diagonalPrefix n i,x≤1 := by
  induction i with
  | zero => intro x hx; have := List.mem_replicate.mp hx; omega
  | succ i ih =>
      intro x hx
      rcases List.mem_or_eq_of_mem_set hx with h | h
      · exact ih x h
      · omega

theorem initial_valid (p n : ℕ) (positive : 1<p) : (initial n).Valid p n := by
  refine ⟨le_rfl,IdentityMatrix.diagonalPrefix_length n n,
    IdentityMatrix.diagonalPrefix_length n n,?_,?_⟩ <;>
    intro x hx <;> have := diagonalPrefix_values n n x hx <;> omega

theorem eliminate_valid (p n : ℕ) (h : List ℕ) (D : Data) (positive : 0<p)
    (valid : D.Valid p n) : (eliminate p n h D).Valid p n := by
  unfold eliminate
  split
  · exact valid
  · exact ⟨(Nat.sub_le _ _).trans valid.width,matrixProduct_length _ _ _ _ _ _,
      matrixProduct_length _ _ _ _ _ _,matrixProduct_values _ _ _ _ _ _ positive,
      matrixProduct_values _ _ _ _ _ _ positive⟩

theorem pivotLift_values (xs : List ℕ) (w j neg p : ℕ) (positive : 1<p) :
    ∀x∈List.ofFn (fun i : Fin (w*(w-1)) => PivotMatrix.liftValue xs (w-1) j neg p i),x<p := by
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  unfold PivotMatrix.liftValue PivotMatrix.lowerValue
  split_ifs
  · exact Nat.mod_lt _ (by omega)
  · exact positive
  · omega

theorem pivotLower_values (w j p : ℕ) (positive : 1<p) :
    ∀x∈List.ofFn (fun i : Fin (w*(w-1)) => PivotMatrix.lowerValue (w-1) j i),x<p := by
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  unfold PivotMatrix.lowerValue
  split_ifs <;> omega

structure Represents (p n remaining : ℕ) (A : List ℕ) (D : Data) (S : State) : Prop where
  ambient : S.scalar (wr .ambient)=n
  width : S.scalar (wr .width)=D.width
  remaining : S.scalar (wr .remaining)=remaining
  modulus : S.scalar (wr .modulus)=p
  one : S.scalar (wr .one)=1
  input : S.array (wa .input)=A
  lift : S.array (wa .lift)=D.lift
  lower : S.array (wa .lowerTranspose)=D.lowerTranspose

theorem Represents.of_left_eq {p n i : ℕ} {A : List ℕ} {D : Data} {S T : State}
    (h : Represents p n i A D S) (eq : T.left=S.left) : Represents p n i A D T := by
  have hs (r : WorkReg) : T.scalar (wr r)=S.scalar (wr r) := congrArg (fun U => U.scalar r) eq
  have ha (a : WorkArr) : T.array (wa a)=S.array (wa a) := congrArg (fun U => U.array a) eq
  exact ⟨(hs _).trans h.ambient,(hs _).trans h.width,(hs _).trans h.remaining,
    (hs _).trans h.modulus,(hs _).trans h.one,(ha _).trans h.input,(ha _).trans h.lift,(ha _).trans h.lower⟩

end GroupWL.MachinePrograms.KernelProgram
