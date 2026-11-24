import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Pi
import Mathlib.Tactic

/-!
# Finite descriptions of addressed monotone circuits

The description lists gate types and product-domain wiring schemas. It does
not list the exponentially many addressed gates. Truth is the least closure
under the seed, scalar (OR), and two-input AND rules.
-/
namespace GroupWL.AddressedCircuit

abbrev Address (r : ℕ) := Fin r → Bool

structure ProductDomain (r : ℕ) where
  coordinate : Fin r → Finset Bool
  nonempty : ∀ i, (coordinate i).Nonempty

namespace ProductDomain

def Contains {r : ℕ} (D : ProductDomain r) (a : Address r) : Prop :=
  ∀ i, a i ∈ D.coordinate i

def full (r : ℕ) : ProductDomain r := ⟨fun _ => Finset.univ, by simp⟩

def singleton {r : ℕ} (a : Address r) : ProductDomain r :=
  ⟨fun i => {a i}, by simp⟩

@[simp] theorem contains_full {r : ℕ} (a : Address r) : (full r).Contains a := by
  simp [Contains, full]

@[simp] theorem contains_singleton {r : ℕ} (a b : Address r) :
    (singleton a).Contains b ↔ b = a := by
  simp [Contains, singleton, funext_iff]

theorem exists_address {r : ℕ} (D : ProductDomain r) : ∃ a, D.Contains a := by
  choose a ha using D.nonempty
  exact ⟨a, ha⟩

end ProductDomain

abbrev AddressMap (r : ℕ) := Fin r → Equiv.Perm Bool

def AddressMap.apply {r : ℕ} (f : AddressMap r) (a : Address r) : Address r :=
  fun i => f i (a i)

def AddressMap.equiv {r : ℕ} (f : AddressMap r) : Equiv.Perm (Address r) where
  toFun := f.apply
  invFun a i := (f i).symm (a i)
  left_inv a := by funext i; exact (f i).symm_apply_apply (a i)
  right_inv a := by funext i; exact (f i).apply_symm_apply (a i)

theorem AddressMap.injective {r : ℕ} (f : AddressMap r) :
    Function.Injective f.apply := f.equiv.injective

def AddressMap.identity (r : ℕ) : AddressMap r := fun _ => Equiv.refl Bool

inductive GateKind where
  | scalar
  | andGate
  deriving DecidableEq, Fintype

structure Schema (T : Type*) (r : ℕ) where
  source : T
  target : T
  port : Bool
  domain : ProductDomain r
  permutation : AddressMap r

structure Request (T : Type*) (r : ℕ) where
  gate : T
  domain : ProductDomain r

structure Circuit (T : Type*) (r : ℕ) where
  kind : T → GateKind
  edges : ℕ
  schema : Fin edges → Schema T r
  seedCount : ℕ
  seed : Fin seedCount → Request T r
  testCount : ℕ
  test : Fin testCount → Request T r
  seed_scalar : ∀ q, kind (seed q).gate = .scalar
  test_scalar : ∀ q, kind (test q).gate = .scalar

namespace Circuit

variable {T : Type*} {r : ℕ} (C : Circuit T r)

abbrev Node (_C : Circuit T r) := T × Address r

def Wire (u v : C.Node) (b : Bool) : Prop :=
  ∃ e : Fin C.edges, ∃ a : Address r,
    (C.schema e).domain.Contains a ∧
    u = ((C.schema e).source, a) ∧
    v = ((C.schema e).target, (C.schema e).permutation.apply a) ∧
    (C.schema e).port = b

def Seed (v : C.Node) : Prop :=
  ∃ q : Fin C.seedCount, v.1 = (C.seed q).gate ∧ (C.seed q).domain.Contains v.2

def Test (v : C.Node) : Prop :=
  ∃ q : Fin C.testCount, v.1 = (C.test q).gate ∧ (C.test q).domain.Contains v.2

inductive True : C.Node → Prop
  | seed {v} (h : C.Seed v) : True v
  | scalar {u v} {b} (hkind : C.kind v.1 = .scalar)
      (hwire : C.Wire u v b) (hu : True u) : True v
  | andGate {u₀ u₁ v} (hkind : C.kind v.1 = .andGate)
      (hw₀ : C.Wire u₀ v false) (hw₁ : C.Wire u₁ v true)
      (hu₀ : True u₀) (hu₁ : True u₁) : True v

def Accepts : Prop := ∃ v, C.Test v ∧ C.True v

/-- A finite description is acyclic when some natural-number rank increases
along every expanded wire. The rank function itself is proof data only. -/
def Acyclic : Prop := ∃ rank : C.Node → ℕ,
  ∀ u v b, C.Wire u v b → rank u < rank v

theorem true_least (P : C.Node → Prop)
    (hs : ∀ v, C.Seed v → P v)
    (hor : ∀ u v b, C.kind v.1 = .scalar → C.Wire u v b → P u → P v)
    (hand : ∀ u₀ u₁ v, C.kind v.1 = .andGate → C.Wire u₀ v false →
      C.Wire u₁ v true → P u₀ → P u₁ → P v) :
    ∀ v, C.True v → P v := by
  intro v hv
  induction hv with
  | seed h => exact hs _ h
  | scalar hk hw _ ih => exact hor _ _ _ hk hw ih
  | andGate hk hw₀ hw₁ _ _ ih₀ ih₁ => exact hand _ _ _ hk hw₀ hw₁ ih₀ ih₁

theorem true_scalar_iff {v : C.Node} (hk : C.kind v.1 = .scalar) :
    C.True v ↔ C.Seed v ∨ ∃ u b, C.Wire u v b ∧ C.True u := by
  constructor
  · intro h
    cases h with
    | seed hs => exact Or.inl hs
    | scalar _ hw hu => exact Or.inr ⟨_, _, hw, hu⟩
    | andGate ha _ _ _ _ => simp_all
  · rintro (hs | ⟨u, b, hw, hu⟩)
    · exact .seed hs
    · exact .scalar hk hw hu

theorem true_and_iff {v : C.Node} (hk : C.kind v.1 = .andGate) :
    C.True v ↔ ∃ u₀ u₁, C.Wire u₀ v false ∧ C.Wire u₁ v true ∧
      C.True u₀ ∧ C.True u₁ := by
  constructor
  · intro h
    cases h with
    | seed hs =>
        obtain ⟨q, hq, _⟩ := hs
        have := C.seed_scalar q
        rw [← hq, hk] at this
        contradiction
    | scalar hs _ _ => simp_all
    | andGate _ hw₀ hw₁ hu₀ hu₁ => exact ⟨_, _, hw₀, hw₁, hu₀, hu₁⟩
  · rintro ⟨u₀, u₁, hw₀, hw₁, hu₀, hu₁⟩
    exact .andGate hk hw₀ hw₁ hu₀ hu₁

end Circuit
end GroupWL.AddressedCircuit
