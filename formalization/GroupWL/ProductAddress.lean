import GroupWL.BinaryAddress

/-! # Two coordinate blocks of a product address -/
namespace GroupWL.ProductAddress

open AddressedCircuit BinaryAddress

def left {r s : ℕ} (a : Address (r + s)) : Address r := fun i => a (i.castAdd s)
def right {r s : ℕ} (a : Address (r + s)) : Address s := fun i => a (Fin.natAdd r i)
def join {r s : ℕ} (a : Address r) (b : Address s) : Address (r + s) := Fin.addCases a b

@[simp] theorem left_join {r s : ℕ} (a : Address r) (b : Address s) : left (join a b) = a := by
  funext i; simp [left, join]

@[simp] theorem right_join {r s : ℕ} (a : Address r) (b : Address s) : right (join a b) = b := by
  funext i; simp [right, join]

@[simp] theorem join_left_right {r s : ℕ} (a : Address (r + s)) : join (left a) (right a) = a := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [left, right, join]

def equiv (r s : ℕ) : Address (r + s) ≃ Address r × Address s where
  toFun a := (left a, right a)
  invFun a := join a.1 a.2
  left_inv := join_left_right
  right_inv a := by simp

theorem ext {r s : ℕ} {a b : Address (r + s)}
    (hl : left a = left b) (hr : right a = right b) : a = b :=
  (equiv r s).injective (Prod.ext hl hr)

def domain {r s : ℕ} (D : ProductDomain r) (E : ProductDomain s) : ProductDomain (r + s) where
  coordinate := Fin.addCases D.coordinate E.coordinate
  nonempty i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using D.nonempty j
    · simpa using E.nonempty j

@[simp] theorem contains_domain {r s : ℕ} (D : ProductDomain r) (E : ProductDomain s)
    (a : Address (r + s)) : (domain D E).Contains a ↔ D.Contains (left a) ∧ E.Contains (right a) := by
  constructor
  · intro h
    constructor
    · intro i; simpa [domain, left] using h (i.castAdd s)
    · intro i; simpa [domain, right] using h (Fin.natAdd r i)
  · rintro ⟨hD, hE⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [domain, left] using hD j
    · simpa [domain, right] using hE j

def map {r s : ℕ} (f : AddressMap r) (g : AddressMap s) : AddressMap (r + s) := Fin.addCases f g

@[simp] theorem left_apply {r s : ℕ} (f : AddressMap r) (g : AddressMap s)
    (a : Address (r + s)) : left ((map f g).apply a) = f.apply (left a) := by
  funext i; simp [map, left, AddressMap.apply]

@[simp] theorem right_apply {r s : ℕ} (f : AddressMap r) (g : AddressMap s)
    (a : Address (r + s)) : right ((map f g).apply a) = g.apply (right a) := by
  funext i; simp [map, right, AddressMap.apply]

@[simp] theorem identity_apply {r : ℕ} (a : Address r) :
    (AddressMap.identity r).apply a = a := rfl

end GroupWL.ProductAddress
