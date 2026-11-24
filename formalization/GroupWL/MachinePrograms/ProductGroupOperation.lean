import GroupWL.MachinePrograms.GroupInitial

namespace GroupWL.MachinePrograms.ProductGroupTable

def productOp {n m : ℕ} (f : Fin n → Fin n → Fin n) (g : Fin m → Fin m → Fin m)
    (x y : Fin (n*m)) : Fin (n*m) :=
  finProdFinEquiv (f (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm y).1,
    g (finProdFinEquiv.symm x).2 (finProdFinEquiv.symm y).2)

@[simp] theorem productOp_pair {n m : ℕ} (f : Fin n → Fin n → Fin n) (g : Fin m → Fin m → Fin m)
    (a c : Fin n) (b d : Fin m) :
    productOp f g (finProdFinEquiv (a,b)) (finProdFinEquiv (c,d))=finProdFinEquiv (f a c,g b d) := by
  simp [productOp]

end GroupWL.MachinePrograms.ProductGroupTable
