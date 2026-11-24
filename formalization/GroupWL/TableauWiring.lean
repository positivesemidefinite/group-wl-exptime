import GroupWL.ProductAddress
import GroupWL.CellularTableau

/-! # Explicit polynomial-size wiring schemas for the cellular tableau

Time uses only nonwrapping carry cases. Space uses cyclic carry/borrow cases.
The schema list has exactly `|Alphabet|^3 * (2*d^2+3*d+2)` entries.
-/
namespace GroupWL.TableauWiring

open AddressedCircuit BinaryAddress CellularTableau

abbrev SpatialCase (d : ℕ) := Fin d × Option (Fin d)
abbrev Case (d : ℕ) := SpatialCase d ⊕ (Fin d ⊕ (SpatialCase d ⊕ Bool))
abbrev Index (Alphabet : Type*) (d : ℕ) := (Alphabet × Alphabet × Alphabet) × Case d

def schema {Alphabet : Type*} {d : ℕ} (rule : Alphabet → Alphabet → Alphabet → Alphabet) :
    Index Alphabet d → Schema (Gate Alphabet) (d + d)
  | ((a, b, c), .inl (h, p)) =>
    { source := .scalar a, target := .pair a b c, port := false
      domain := ProductAddress.domain (carryDomain h) (successorDomain p)
      permutation := ProductAddress.map (prefixFlip h) (stepMap p) }
  | ((a, b, c), .inr (.inl h)) =>
    { source := .scalar b, target := .pair a b c, port := true
      domain := ProductAddress.domain (carryDomain h) (ProductDomain.full d)
      permutation := ProductAddress.map (prefixFlip h) (AddressMap.identity d) }
  | ((a, b, c), .inr (.inr (.inl (h, p)))) =>
    { source := .scalar c, target := .triple a b c, port := true
      domain := ProductAddress.domain (carryDomain h) (predecessorDomain p)
      permutation := ProductAddress.map (prefixFlip h) (stepMap p) }
  | ((a, b, c), .inr (.inr (.inr false))) =>
    { source := .pair a b c, target := .triple a b c, port := false
      domain := ProductDomain.full (d + d), permutation := AddressMap.identity (d + d) }
  | ((a, b, c), .inr (.inr (.inr true))) =>
    { source := .triple a b c, target := .scalar (rule a b c), port := false
      domain := ProductDomain.full (d + d), permutation := AddressMap.identity (d + d) }

theorem case_count (d : ℕ) : Fintype.card (Case d) = 2 * d ^ 2 + 3 * d + 2 := by
  simp only [Case, SpatialCase, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_option, Fintype.card_bool]
  ring

theorem schema_count (Alphabet : Type*) [Fintype Alphabet] (d : ℕ) :
    Fintype.card (Index Alphabet d) = Fintype.card Alphabet ^ 3 * (2 * d ^ 2 + 3 * d + 2) := by
  simp only [Index, Fintype.card_prod, case_count]
  ring

def time {d : ℕ} (a : Address (d + d)) : ℕ := value (ProductAddress.left a)
def space {d : ℕ} (a : Address (d + d)) : ZMod (2 ^ d) := value (ProductAddress.right a)

@[simp] theorem time_lt {d : ℕ} (a : Address (d + d)) : time a < 2 ^ d := value_lt _

theorem successor_space {d : ℕ} (p : Option (Fin d)) (a : Address d)
    (ha : (successorDomain p).Contains a) :
    (value ((stepMap p).apply a) : ZMod (2 ^ d)) = (value a : ZMod (2 ^ d)) + 1 := by
  rw [successor_value p a ha]
  simp

theorem predecessor_space {d : ℕ} (p : Option (Fin d)) (a : Address d)
    (ha : (predecessorDomain p).Contains a) :
    (value ((stepMap p).apply a) : ZMod (2 ^ d)) = (value a : ZMod (2 ^ d)) - 1 := by
  have hn : 0 < 2 ^ d := pow_pos (by omega) d
  rw [predecessor_value p a ha]
  simp only [ZMod.natCast_mod]
  rw [Nat.cast_sub (by omega)]
  simp

/-- The expanded five edge types, including ports and noncyclic time. -/
inductive Edge {Alphabet : Type*} (rule : Alphabet → Alphabet → Alphabet → Alphabet) (d : ℕ) :
    (Gate Alphabet × ℕ × ZMod (2 ^ d)) → (Gate Alphabet × ℕ × ZMod (2 ^ d)) → Bool → Prop
  | left (a b c : Alphabet) (t : ℕ) (x : ZMod (2 ^ d)) :
      Edge rule d (.scalar a, t, x) (.pair a b c, t + 1, x + 1) false
  | center (a b c : Alphabet) (t : ℕ) (x : ZMod (2 ^ d)) :
      Edge rule d (.scalar b, t, x) (.pair a b c, t + 1, x) true
  | right (a b c : Alphabet) (t : ℕ) (x : ZMod (2 ^ d)) :
      Edge rule d (.scalar c, t, x) (.triple a b c, t + 1, x - 1) true
  | pair (a b c : Alphabet) (t : ℕ) (x : ZMod (2 ^ d)) :
      Edge rule d (.pair a b c, t, x) (.triple a b c, t, x) false
  | output (a b c : Alphabet) (t : ℕ) (x : ZMod (2 ^ d)) :
      Edge rule d (.triple a b c, t, x) (.scalar (rule a b c), t, x) false

/-- Every single listed schema realizes exactly its intended temporal/spatial
edge. In particular no temporal wrap edge is introduced. -/
theorem schema_sound {Alphabet : Type*} {d : ℕ}
    (rule : Alphabet → Alphabet → Alphabet → Alphabet)
    (e : Index Alphabet d) (a : Address (d + d)) (ha : (schema rule e).domain.Contains a) :
    Edge rule d ((schema rule e).source, time a, space a)
      ((schema rule e).target, time ((schema rule e).permutation.apply a),
        space ((schema rule e).permutation.apply a)) (schema rule e).port := by
  rcases e with ⟨⟨x, y, z⟩, e⟩
  rcases e with ⟨h, p⟩ | h | ⟨h, p⟩ | k
  · have hh := (ProductAddress.contains_domain _ _ a).mp ha
    have ht := carry_value h _ ((contains_carryDomain _ _).mp hh.1)
    have hp := successor_space p _ hh.2
    change Edge rule d (.scalar x, time a, space a)
      (.pair x y z, value (ProductAddress.left _), (value (ProductAddress.right _) : ZMod (2 ^ d))) false
    simp only [schema]
    rw [ProductAddress.left_apply, ProductAddress.right_apply, ht, hp]
    exact .left x y z (time a) (space a)
  · have hh := (ProductAddress.contains_domain _ _ a).mp ha
    have ht := carry_value h _ ((contains_carryDomain _ _).mp hh.1)
    change Edge rule d (.scalar y, time a, space a)
      (.pair x y z, value (ProductAddress.left _), (value (ProductAddress.right _) : ZMod (2 ^ d))) true
    simp only [schema]
    rw [ProductAddress.left_apply, ProductAddress.right_apply, ht, ProductAddress.identity_apply]
    exact .center x y z (time a) (space a)
  · have hh := (ProductAddress.contains_domain _ _ a).mp ha
    have ht := carry_value h _ ((contains_carryDomain _ _).mp hh.1)
    have hp := predecessor_space p _ hh.2
    change Edge rule d (.scalar z, time a, space a)
      (.triple x y z, value (ProductAddress.left _), (value (ProductAddress.right _) : ZMod (2 ^ d))) true
    simp only [schema]
    rw [ProductAddress.left_apply, ProductAddress.right_apply, ht, hp]
    exact .right x y z (time a) (space a)
  · cases k
    · exact .pair x y z (time a) (space a)
    · exact .output x y z (time a) (space a)

theorem address_ext {d : ℕ} {a b : Address (d + d)}
    (ht : time a = time b) (hx : space a = space b) : a = b := by
  apply ProductAddress.ext
  · exact value_injective d ht
  · apply value_injective d
    have hv := congrArg ZMod.val hx
    simpa only [space, ZMod.val_natCast, Nat.mod_eq_of_lt (value_lt _)] using hv

theorem carry_for_time {d : ℕ} (a b : Address (d + d)) (ht : time b = time a + 1) :
    ∃ h : Fin d, (carryDomain h).Contains (ProductAddress.left a) := by
  apply Exists.imp (fun h hh => (contains_carryDomain h _).mpr hh)
    (carry_exists (ProductAddress.left a) ?_)
  intro ha
  have hta : time a = 2 ^ d - 1 := by simp only [time, ha, value_all_true]
  have htb := time_lt b
  have hn : 0 < 2 ^ d := pow_pos (by omega) d
  omega

theorem left_realized {Alphabet : Type*} {d : ℕ}
    (rule : Alphabet → Alphabet → Alphabet → Alphabet) (x y z : Alphabet)
    (a b : Address (d + d)) (ht : time b = time a + 1) (hx : space b = space a + 1) :
    ∃ e : Index Alphabet d, (schema rule e).source = .scalar x ∧
      (schema rule e).target = .pair x y z ∧ (schema rule e).port = false ∧
      (schema rule e).domain.Contains a ∧ (schema rule e).permutation.apply a = b := by
  obtain ⟨h, hh⟩ := carry_for_time a b ht
  obtain ⟨p, hp⟩ := successor_cover (ProductAddress.right a)
  refine ⟨((x, y, z), .inl (h, p)), rfl, rfl, rfl,
    (ProductAddress.contains_domain _ _ a).mpr ⟨hh, hp⟩, ?_⟩
  apply address_ext
  · change value (ProductAddress.left ((ProductAddress.map (prefixFlip h) (stepMap p)).apply a)) = time b
    rw [ProductAddress.left_apply, carry_value h _ ((contains_carryDomain _ _).mp hh)]
    exact ht.symm
  · change (value (ProductAddress.right ((ProductAddress.map (prefixFlip h) (stepMap p)).apply a)) :
      ZMod (2 ^ d)) = space b
    rw [ProductAddress.right_apply, successor_space p _ hp]
    exact hx.symm

theorem center_realized {Alphabet : Type*} {d : ℕ}
    (rule : Alphabet → Alphabet → Alphabet → Alphabet) (x y z : Alphabet)
    (a b : Address (d + d)) (ht : time b = time a + 1) (hx : space b = space a) :
    ∃ e : Index Alphabet d, (schema rule e).source = .scalar y ∧
      (schema rule e).target = .pair x y z ∧ (schema rule e).port = true ∧
      (schema rule e).domain.Contains a ∧ (schema rule e).permutation.apply a = b := by
  obtain ⟨h, hh⟩ := carry_for_time a b ht
  refine ⟨((x, y, z), .inr (.inl h)), rfl, rfl, rfl,
    (ProductAddress.contains_domain _ _ a).mpr ⟨hh, ProductDomain.contains_full _⟩, ?_⟩
  apply address_ext
  · change value (ProductAddress.left ((ProductAddress.map (prefixFlip h) (AddressMap.identity d)).apply a)) = time b
    rw [ProductAddress.left_apply, carry_value h _ ((contains_carryDomain _ _).mp hh)]
    exact ht.symm
  · change (value (ProductAddress.right ((ProductAddress.map (prefixFlip h) (AddressMap.identity d)).apply a)) :
      ZMod (2 ^ d)) = space b
    rw [ProductAddress.right_apply, ProductAddress.identity_apply]
    exact hx.symm

theorem right_realized {Alphabet : Type*} {d : ℕ}
    (rule : Alphabet → Alphabet → Alphabet → Alphabet) (x y z : Alphabet)
    (a b : Address (d + d)) (ht : time b = time a + 1) (hx : space b = space a - 1) :
    ∃ e : Index Alphabet d, (schema rule e).source = .scalar z ∧
      (schema rule e).target = .triple x y z ∧ (schema rule e).port = true ∧
      (schema rule e).domain.Contains a ∧ (schema rule e).permutation.apply a = b := by
  obtain ⟨h, hh⟩ := carry_for_time a b ht
  obtain ⟨p, hp⟩ := predecessor_cover (ProductAddress.right a)
  refine ⟨((x, y, z), .inr (.inr (.inl (h, p)))), rfl, rfl, rfl,
    (ProductAddress.contains_domain _ _ a).mpr ⟨hh, hp⟩, ?_⟩
  apply address_ext
  · change value (ProductAddress.left ((ProductAddress.map (prefixFlip h) (stepMap p)).apply a)) = time b
    rw [ProductAddress.left_apply, carry_value h _ ((contains_carryDomain _ _).mp hh)]
    exact ht.symm
  · change (value (ProductAddress.right ((ProductAddress.map (prefixFlip h) (stepMap p)).apply a)) :
      ZMod (2 ^ d)) = space b
    rw [ProductAddress.right_apply, predecessor_space p _ hp]
    exact hx.symm

end GroupWL.TableauWiring
