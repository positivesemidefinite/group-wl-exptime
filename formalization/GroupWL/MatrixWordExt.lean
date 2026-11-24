import GroupWL.MatrixEncoding

namespace GroupWL.MatrixEncoding
open CachedElimination
variable {p m n : ℕ} [NeZero p]

theorem ofFn_eq_word (A : MatrixData (F:=ZMod p) m n) (f : ℕ → ℕ)
    (h : ∀ i : Fin m, ∀ j : Fin n, f (i.val*n+j.val)=A[i][j].val) :
    List.ofFn (fun z : Fin (m*n) => f z.val)=word A := by
  unfold word
  apply congrArg List.ofFn
  funext z
  have hz : z.val=(finProdFinEquiv.symm z).1.val*n+(finProdFinEquiv.symm z).2.val := by
    change z.val=z.val/n*n+z.val%n
    simpa only [Nat.add_comm,Nat.mul_comm] using (Nat.mod_add_div z.val n).symm
  exact (congrArg f hz).trans (h (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2)

end GroupWL.MatrixEncoding
