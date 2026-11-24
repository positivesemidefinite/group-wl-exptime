import GroupWL.BinaryAddress

/-! # Polynomial product-domain descriptions of binary suffix intervals -/
namespace GroupWL.BinaryIntervals
open AddressedCircuit BinaryAddress

/-- The highest differing bit determines numeric order, regardless of all
lower address bits. -/
theorem value_lt_of_highest_bit {r : ℕ} (h : Fin r) (a b : Address r)
    (ha : a h = false) (hb : b h = true) (he : ∀ i, h < i → a i = b i) :
    value a < value b := by
  induction r with
  | zero => exact Fin.elim0 h
  | succ r ih =>
    revert ha hb he
    refine Fin.cases ?_ (fun k => ?_) h
    · intro ha hb he
      have ht : (fun i : Fin r => a i.succ) = fun i : Fin r => b i.succ := by
        funext i
        exact he i.succ (by simp)
      rw [value_succ, value_succ, ha, hb, ht]
      simp
    · intro ha hb he
      have ht := ih k (fun i : Fin r => a i.succ) (fun i : Fin r => b i.succ) ha hb
        (fun i hi => he i.succ (by simpa using hi))
      rw [value_succ, value_succ]
      cases a 0 <;> cases b 0 <;> simp <;> omega

/-- Distinct finite addresses have a greatest coordinate at which they differ. -/
theorem highest_difference {r : ℕ} (a b : Address r) (hne : a ≠ b) :
    ∃ h : Fin r, a h ≠ b h ∧ ∀ i, h < i → a i = b i := by
  classical
  let s := Finset.univ.filter (fun i => a i ≠ b i)
  have hs : s.Nonempty := by
    by_contra hn
    apply hne
    funext i
    by_contra hi
    exact hn ⟨i, by simp [s, hi]⟩
  let h := s.max' hs
  refine ⟨h, (Finset.mem_filter.mp (Finset.max'_mem s hs)).2, ?_⟩
  intro i hi
  by_contra hne
  have himem : i ∈ s := by simp [s, hne]
  have hle : i ≤ h := Finset.le_max' s i himem
  exact not_lt_of_ge hle hi

/-- Strictly larger addresses have exactly the indicated zero-to-one highest
difference from their threshold address. -/
theorem exists_high_bit_of_lt {r : ℕ} (m a : Address r) (hlt : value m < value a) :
    ∃ h : Fin r, m h = false ∧ a h = true ∧ ∀ i, h < i → a i = m i := by
  have hne : m ≠ a := by intro h; subst a; exact (lt_irrefl _ hlt)
  obtain ⟨h, hh, he⟩ := highest_difference m a hne
  have hm : m h = false := by
    cases hm : m h
    · rfl
    · have ha : a h = false := by cases ha : a h <;> simp_all
      have hrev := value_lt_of_highest_bit h a m ha hm (fun i hi => (he i hi).symm)
      omega
  have ha : a h = true := by cases ha : a h <;> simp_all
  exact ⟨h, hm, ha, fun i hi => (he i hi).symm⟩

/-- Fix the higher threshold bits, switch one threshold zero to one, and
leave every lower bit free. This domain is always nonempty. -/
def aboveDomain {r : ℕ} (m : Address r) (h : Fin r) : ProductDomain r where
  coordinate i := if h < i then {m i} else if i = h then {true} else Finset.univ
  nonempty i := by split_ifs <;> simp

@[simp] theorem contains_aboveDomain {r : ℕ} (m a : Address r) (h : Fin r) :
    (aboveDomain m h).Contains a ↔ a h = true ∧ ∀ i, h < i → a i = m i := by
  constructor
  · intro ha
    refine ⟨?_, fun i hi => ?_⟩
    · have := ha h
      simpa [aboveDomain] using this
    · have := ha i
      simpa [aboveDomain, hi] using this
  · rintro ⟨hh, ha⟩ i
    by_cases hi : h < i
    · simp [aboveDomain, hi, ha i hi]
    · by_cases he : i = h
      · subst i; simp [aboveDomain, hh]
      · simp [aboveDomain, hi, he]

/-- One singleton threshold case plus one case for each zero bit. -/
abbrev Case {r : ℕ} (m : Address r) := Option {h : Fin r // m h = false}

def domain {r : ℕ} (m : Address r) : Case m → ProductDomain r
  | none => ProductDomain.singleton m
  | some h => aboveDomain m h.val

/-- The full blank suffix is represented by at most r+1 product domains. -/
theorem case_card_le {r : ℕ} (m : Address r) : Fintype.card (Case m) ≤ r + 1 := by
  simpa using Nat.add_le_add_right (Fintype.card_subtype_le (fun h : Fin r => m h = false)) 1

/-- Exact union semantics; no exponential list of blank addresses occurs. -/
theorem covered_iff {r : ℕ} (m a : Address r) :
    (∃ c : Case m, (domain m c).Contains a) ↔ value m ≤ value a := by
  constructor
  · rintro ⟨c, hc⟩
    cases c with
    | none =>
      have he := (ProductDomain.contains_singleton m a).mp hc
      subst a
      exact le_rfl
    | some h =>
      obtain ⟨ha, he⟩ := (contains_aboveDomain m a h.val).mp hc
      exact (value_lt_of_highest_bit h.val m a h.property ha (fun i hi => (he i hi).symm)).le
  · intro hle
    by_cases he : value m = value a
    · have he' : a = m := (value_injective r he).symm
      exact ⟨none, (ProductDomain.contains_singleton m a).mpr he'⟩
    · have hlt : value m < value a := by omega
      obtain ⟨h, hm, ha, hh⟩ := exists_high_bit_of_lt m a hlt
      exact ⟨some ⟨h, hm⟩, (contains_aboveDomain m a h).mpr ⟨ha, hh⟩⟩

/-- Numeric thresholds are converted by the executable binary algorithm. -/
theorem covered_iff_threshold (r m : ℕ) (hm : m < 2 ^ r) (a : Address r) :
    (∃ c : Case (ofNat r m), (domain (ofNat r m) c).Contains a) ↔ m ≤ value a := by
  rw [covered_iff, value_ofNat r m hm]

/-- An executable list of exactly r+1 domains. Redundant cases use the
threshold singleton, avoiding a data-dependent enumeration of zero bits. -/
def indexedDomain {r : ℕ} (m : Address r) : Option (Fin r) → ProductDomain r
  | none => ProductDomain.singleton m
  | some h => if m h = false then aboveDomain m h else ProductDomain.singleton m

theorem indexed_covered_iff {r : ℕ} (m a : Address r) :
    (∃ c : Option (Fin r), (indexedDomain m c).Contains a) ↔ value m ≤ value a := by
  rw [← covered_iff]
  constructor
  · rintro ⟨c,hc⟩
    cases c with
    | none => exact ⟨none,hc⟩
    | some h =>
      by_cases hm : m h = false
      · exact ⟨some ⟨h,hm⟩,by simpa [indexedDomain,hm,domain] using hc⟩
      · exact ⟨none,by simpa [indexedDomain,hm,domain] using hc⟩
  · rintro ⟨c,hc⟩
    cases c with
    | none => exact ⟨none,hc⟩
    | some h => exact ⟨some h.val,by simpa [indexedDomain,h.property,domain] using hc⟩

end GroupWL.BinaryIntervals
