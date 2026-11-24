import GroupWL.AddressedCircuit

/-! # Rectangular binary carry and borrow schemas

Addresses are little-endian. Each carry/borrow case fixes only a prefix of
bits and uses a coordinatewise permutation, so it is a permitted product
domain wiring schema rather than an exponentially enumerated relation.
-/
namespace GroupWL.BinaryAddress

open AddressedCircuit

/-- Little-endian numeric value of a Boolean address. -/
def value : {r : ℕ} → Address r → ℕ
  | 0, _ => 0
  | r + 1, a => (if a 0 then 1 else 0) + 2 * value (fun i : Fin r => a i.succ)

@[simp] theorem value_zero : value (fun _ : Fin 0 => false) = 0 := rfl

@[simp] theorem value_succ {r : ℕ} (a : Address (r + 1)) :
    value a = (if a 0 then 1 else 0) + 2 * value (fun i : Fin r => a i.succ) := rfl

def CarryAt {r : ℕ} (h : Fin r) (a : Address r) : Prop :=
  (∀ i, i < h → a i = true) ∧ a h = false

def BorrowAt {r : ℕ} (h : Fin r) (a : Address r) : Prop :=
  (∀ i, i < h → a i = false) ∧ a h = true

/-- A prefix of ones followed by the first zero; higher bits are free. -/
def carryDomain {r : ℕ} (h : Fin r) : ProductDomain r where
  coordinate i := if i < h then {true} else if i = h then {false} else Finset.univ
  nonempty i := by split_ifs <;> simp

/-- A prefix of zeros followed by the first one; higher bits are free. -/
def borrowDomain {r : ℕ} (h : Fin r) : ProductDomain r where
  coordinate i := if i < h then {false} else if i = h then {true} else Finset.univ
  nonempty i := by split_ifs <;> simp

@[simp] theorem contains_carryDomain {r : ℕ} (h : Fin r) (a : Address r) :
    (carryDomain h).Contains a ↔ CarryAt h a := by
  constructor
  · intro ha
    refine ⟨fun i hi => ?_, ?_⟩
    · have := ha i
      simpa [carryDomain, hi] using this
    · have := ha h
      simpa [carryDomain] using this
  · rintro ⟨ha, hh⟩ i
    by_cases hi : i < h
    · simp [carryDomain, hi, ha i hi]
    · by_cases he : i = h
      · subst i; simp [carryDomain, hh]
      · simp [carryDomain, hi, he]

@[simp] theorem contains_borrowDomain {r : ℕ} (h : Fin r) (a : Address r) :
    (borrowDomain h).Contains a ↔ BorrowAt h a := by
  constructor
  · intro ha
    refine ⟨fun i hi => ?_, ?_⟩
    · have := ha i
      simpa [borrowDomain, hi] using this
    · have := ha h
      simpa [borrowDomain] using this
  · rintro ⟨ha, hh⟩ i
    by_cases hi : i < h
    · simp [borrowDomain, hi, ha i hi]
    · by_cases he : i = h
      · subst i; simp [borrowDomain, hh]
      · simp [borrowDomain, hi, he]

def notEquiv : Equiv.Perm Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl

/-- The same prefix-flip permutation implements both carry and borrow. -/
def prefixFlip {r : ℕ} (h : Fin r) : AddressMap r :=
  fun i => if i ≤ h then notEquiv else Equiv.refl Bool

@[simp] theorem prefixFlip_apply {r : ℕ} (h : Fin r) (a : Address r) (i : Fin r) :
    (prefixFlip h).apply a i = if i ≤ h then !a i else a i := by
  simp only [prefixFlip, AddressMap.apply]
  split_ifs <;> rfl

theorem value_lt {r : ℕ} (a : Address r) : value a < 2 ^ r := by
  induction r with
  | zero => simp [value]
  | succ r ih =>
    have ht := ih (fun i : Fin r => a i.succ)
    rw [value_succ, pow_succ]
    cases ha : a 0 <;> simp [ha] <;> omega

@[simp] theorem value_all_false (r : ℕ) : value (fun _ : Fin r => false) = 0 := by
  induction r with
  | zero => rfl
  | succ r ih => simp [value, ih]

@[simp] theorem value_all_true (r : ℕ) : value (fun _ : Fin r => true) = 2 ^ r - 1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [value_succ, Bool.true_eq, if_true, ih, pow_succ]
    have : 0 < 2 ^ r := pow_pos (by omega) r
    omega

theorem carry_value {r : ℕ} (h : Fin r) (a : Address r) (ha : CarryAt h a) :
    value ((prefixFlip h).apply a) = value a + 1 := by
  induction r with
  | zero => exact Fin.elim0 h
  | succ r ih =>
    revert ha
    refine Fin.cases ?_ (fun k => ?_) h
    · intro ha
      have hzero := ha.2
      have htail : (fun i : Fin r => (prefixFlip (0 : Fin (r + 1))).apply a i.succ) =
          (fun i : Fin r => a i.succ) := by
        funext i
        simp
      rw [value_succ, value_succ, htail]
      simp [hzero]
      omega
    · intro ha
      have hz : a 0 = true := ha.1 0 (by simp)
      have ht : CarryAt k (fun i : Fin r => a i.succ) :=
        ⟨fun i hi => ha.1 i.succ (by simpa using hi), ha.2⟩
      have htval := ih k (fun i : Fin r => a i.succ) ht
      have htail : (fun i : Fin r => (prefixFlip k.succ).apply a i.succ) =
          (prefixFlip k).apply (fun i : Fin r => a i.succ) := by
        funext i
        simp
      rw [value_succ, value_succ, htail, htval]
      simp [hz]
      omega

theorem prefixFlip_involutive {r : ℕ} (h : Fin r) :
    Function.Involutive (prefixFlip h).apply := by
  intro a
  funext i
  simp only [prefixFlip_apply]
  split_ifs <;> simp

theorem carry_to_borrow {r : ℕ} (h : Fin r) (a : Address r) (ha : CarryAt h a) :
    BorrowAt h ((prefixFlip h).apply a) := by
  constructor
  · intro i hi
    simp [prefixFlip_apply, le_of_lt hi, ha.1 i hi]
  · simp [prefixFlip_apply, ha.2]

theorem borrow_to_carry {r : ℕ} (h : Fin r) (a : Address r) (ha : BorrowAt h a) :
    CarryAt h ((prefixFlip h).apply a) := by
  constructor
  · intro i hi
    simp [prefixFlip_apply, le_of_lt hi, ha.1 i hi]
  · simp [prefixFlip_apply, ha.2]

theorem borrow_value {r : ℕ} (h : Fin r) (a : Address r) (ha : BorrowAt h a) :
    value ((prefixFlip h).apply a) + 1 = value a := by
  have hc := carry_value h ((prefixFlip h).apply a) (borrow_to_carry h a ha)
  rw [prefixFlip_involutive] at hc
  exact hc.symm

/-- Every address except the maximum has a unique carry case. -/
theorem carry_exists {r : ℕ} (a : Address r) (ha : a ≠ fun _ => true) :
    ∃ h, CarryAt h a := by
  classical
  let s := Finset.univ.filter (fun i => a i = false)
  have hs : s.Nonempty := by
    by_contra hn
    apply ha
    funext i
    have hi : a i ≠ false := by
      intro hf
      exact hn ⟨i, by simp [s, hf]⟩
    cases hv : a i <;> simp_all
  let h := s.min' hs
  refine ⟨h, ?_, ?_⟩
  · intro i hi
    cases hv : a i
    · have himem : i ∈ s := by simp [s, hv]
      have hle : h ≤ i := Finset.min'_le s i himem
      exact False.elim (not_lt_of_ge hle hi)
    · rfl
  · have hh : h ∈ s := Finset.min'_mem s hs
    exact (Finset.mem_filter.mp hh).2

theorem borrow_exists {r : ℕ} (a : Address r) (ha : a ≠ fun _ => false) :
    ∃ h, BorrowAt h a := by
  classical
  let s := Finset.univ.filter (fun i => a i = true)
  have hs : s.Nonempty := by
    by_contra hn
    apply ha
    funext i
    have hi : a i ≠ true := by
      intro hf
      exact hn ⟨i, by simp [s, hf]⟩
    cases hv : a i <;> simp_all
  let h := s.min' hs
  refine ⟨h, ?_, ?_⟩
  · intro i hi
    cases hv : a i
    · rfl
    · have himem : i ∈ s := by simp [s, hv]
      have hle : h ≤ i := Finset.min'_le s i himem
      exact False.elim (not_lt_of_ge hle hi)
  · have hh : h ∈ s := Finset.min'_mem s hs
    exact (Finset.mem_filter.mp hh).2

theorem carry_unique {r : ℕ} (a : Address r) {h k : Fin r}
    (hh : CarryAt h a) (hk : CarryAt k a) : h = k := by
  rcases lt_trichotomy h k with hlt | heq | hgt
  · have := hk.1 h hlt; simp [hh.2] at this
  · exact heq
  · have := hh.1 k hgt; simp [hk.2] at this

theorem borrow_unique {r : ℕ} (a : Address r) {h k : Fin r}
    (hh : BorrowAt h a) (hk : BorrowAt k a) : h = k := by
  rcases lt_trichotomy h k with hlt | heq | hgt
  · have := hk.1 h hlt; simp [hh.2] at this
  · exact heq
  · have := hh.1 k hgt; simp [hk.2] at this

/-- The extra cyclic schema flips the all-one or all-zero address. -/
def flipAll (r : ℕ) : AddressMap r := fun _ => notEquiv

@[simp] theorem flipAll_apply {r : ℕ} (a : Address r) (i : Fin r) :
    (flipAll r).apply a i = !a i := rfl

/-- Exactly r carry cases and one cyclic wrap case. -/
def successorDomain {r : ℕ} : Option (Fin r) → ProductDomain r
  | some h => carryDomain h
  | none => ProductDomain.singleton (fun _ => true)

def predecessorDomain {r : ℕ} : Option (Fin r) → ProductDomain r
  | some h => borrowDomain h
  | none => ProductDomain.singleton (fun _ => false)

def stepMap {r : ℕ} : Option (Fin r) → AddressMap r
  | some h => prefixFlip h
  | none => flipAll r

@[simp] theorem schema_count (r : ℕ) : Fintype.card (Option (Fin r)) = r + 1 := by simp

theorem successor_cover {r : ℕ} (a : Address r) : ∃ c, (successorDomain c).Contains a := by
  classical
  by_cases ha : a = fun _ => true
  · exact ⟨none, (ProductDomain.contains_singleton _ _).mpr ha⟩
  · obtain ⟨h, hh⟩ := carry_exists a ha
    exact ⟨some h, (contains_carryDomain h a).mpr hh⟩

theorem predecessor_cover {r : ℕ} (a : Address r) : ∃ c, (predecessorDomain c).Contains a := by
  classical
  by_cases ha : a = fun _ => false
  · exact ⟨none, (ProductDomain.contains_singleton _ _).mpr ha⟩
  · obtain ⟨h, hh⟩ := borrow_exists a ha
    exact ⟨some h, (contains_borrowDomain h a).mpr hh⟩

/-- Every successor schema has the exact cyclic arithmetic semantics. -/
theorem successor_value {r : ℕ} (c : Option (Fin r)) (a : Address r)
    (ha : (successorDomain c).Contains a) :
    value ((stepMap c).apply a) = (value a + 1) % 2 ^ r := by
  cases c with
  | none =>
    have he : a = fun _ => true := (ProductDomain.contains_singleton _ _).mp ha
    subst a
    have hf : (flipAll r).apply (fun _ => true) = fun _ => false := by funext i; rfl
    change value ((flipAll r).apply (fun _ => true)) = _
    rw [hf, value_all_false, value_all_true]
    have hp : 0 < 2 ^ r := pow_pos (by omega) r
    have he : 2 ^ r - 1 + 1 = 2 ^ r := by omega
    rw [he, Nat.mod_self]
  | some h =>
    have hc := carry_value h a ((contains_carryDomain h a).mp ha)
    change value ((prefixFlip h).apply a) = _
    rw [hc]
    exact (Nat.mod_eq_of_lt (by rw [← hc]; exact value_lt _)).symm

/-- Every predecessor schema has the exact cyclic arithmetic semantics. -/
theorem predecessor_value {r : ℕ} (c : Option (Fin r)) (a : Address r)
    (ha : (predecessorDomain c).Contains a) :
    value ((stepMap c).apply a) = (value a + 2 ^ r - 1) % 2 ^ r := by
  cases c with
  | none =>
    have he : a = fun _ => false := (ProductDomain.contains_singleton _ _).mp ha
    subst a
    have hf : (flipAll r).apply (fun _ => false) = fun _ => true := by funext i; rfl
    change value ((flipAll r).apply (fun _ => false)) = _
    rw [hf, value_all_true, value_all_false, zero_add]
    exact (Nat.mod_eq_of_lt (by have := pow_pos (show 0 < 2 by omega) r; omega)).symm
  | some h =>
    have hc := borrow_value h a ((contains_borrowDomain h a).mp ha)
    change value ((prefixFlip h).apply a) = _
    rw [← hc]
    have he : value ((prefixFlip h).apply a) + 1 + 2 ^ r - 1 =
        value ((prefixFlip h).apply a) + 2 ^ r := by
      rw [Nat.add_right_comm _ 1, Nat.add_sub_cancel]
    rw [he, Nat.add_mod_right]
    exact (Nat.mod_eq_of_lt (value_lt _)).symm

/-- Numeric values distinguish all Boolean addresses. -/
theorem value_injective (r : ℕ) : Function.Injective (value (r := r)) := by
  induction r with
  | zero =>
    intro a b hab
    funext i
    exact Fin.elim0 i
  | succ r ih =>
    intro a b hab
    have hbits : a 0 = b 0 := by
      cases ha : a 0 <;> cases hb : b 0 <;> simp_all [value_succ] <;> omega
    have htail : value (fun i : Fin r => a i.succ) = value (fun i : Fin r => b i.succ) := by
      rw [value_succ, value_succ, hbits] at hab
      omega
    have heq := ih htail
    funext i
    exact Fin.cases hbits (fun j => congrFun heq j) i

def valueFin {r : ℕ} (a : Address r) : Fin (2 ^ r) := ⟨value a, value_lt a⟩

/-- Executable conversion of an integer to its low r binary digits. -/
def ofNat : (r : ℕ) → ℕ → Address r
  | 0, _ => Fin.elim0
  | r + 1, n => Fin.cases (decide (n % 2 = 1)) (ofNat r (n / 2))

theorem value_ofNat (r n : ℕ) (hn : n < 2 ^ r) : value (ofNat r n) = n := by
  induction r generalizing n with
  | zero =>
    have : n = 0 := by simpa using hn
    subst n
    rfl
  | succ r ih =>
    have ht : n / 2 < 2 ^ r := by
      apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
      simpa [pow_succ] using hn
    change (if decide (n % 2 = 1) then 1 else 0) + 2 * value (ofNat r (n / 2)) = n
    rw [ih (n / 2) ht]
    have hm : n % 2 < 2 := Nat.mod_lt n (by omega)
    have hd := Nat.mod_add_div n 2
    by_cases he : n % 2 = 1
    · simp [he]
      omega
    · have he' : n % 2 = 0 := by omega
      simp [he]
      omega

theorem ofNat_value {r : ℕ} (a : Address r) : ofNat r (value a) = a :=
  value_injective r (value_ofNat r (value a) (value_lt a))

/-- Boolean addresses are exactly the positions of the cyclic power-of-two tape. -/
def valueEquiv (r : ℕ) : Address r ≃ Fin (2 ^ r) where
  toFun := valueFin
  invFun n := ofNat r n.val
  left_inv a := ofNat_value a
  right_inv n := Fin.ext (value_ofNat r n.val n.isLt)

@[simp] theorem valueEquiv_val {r : ℕ} (a : Address r) : (valueEquiv r a).val = value a := rfl

/-- The compact successor schema family denotes exactly numeric cyclic successor. -/
theorem successor_schema_iff {r : ℕ} (a b : Address r) :
    (∃ c, (successorDomain c).Contains a ∧ (stepMap c).apply a = b) ↔
      value b = (value a + 1) % 2 ^ r := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact successor_value c a hc
  · intro hab
    obtain ⟨c, hc⟩ := successor_cover a
    refine ⟨c, hc, value_injective r ?_⟩
    exact (successor_value c a hc).trans hab.symm

/-- The compact predecessor schema family denotes exactly numeric cyclic predecessor. -/
theorem predecessor_schema_iff {r : ℕ} (a b : Address r) :
    (∃ c, (predecessorDomain c).Contains a ∧ (stepMap c).apply a = b) ↔
      value b = (value a + 2 ^ r - 1) % 2 ^ r := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact predecessor_value c a hc
  · intro hab
    obtain ⟨c, hc⟩ := predecessor_cover a
    refine ⟨c, hc, value_injective r ?_⟩
    exact (predecessor_value c a hc).trans hab.symm

end GroupWL.BinaryAddress
