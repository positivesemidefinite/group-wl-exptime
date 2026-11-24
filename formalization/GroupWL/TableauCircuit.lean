import GroupWL.TableauWiring
import GroupWL.FiniteCodes

/-! The compact addressed circuit realizes the complete finite cellular tableau. -/
namespace GroupWL.TableauCircuit

open AddressedCircuit BinaryAddress CellularTableau

structure ScalarRequest (Alphabet : Type*) (r : ℕ) where
  letter : Alphabet
  domain : ProductDomain r

def kind {Alphabet : Type*} : Gate Alphabet → GateKind
  | .scalar _ => .scalar
  | .pair _ _ _ | .triple _ _ _ => .andGate

def circuit {Alphabet : Type*} [FiniteCode Alphabet] {d s t : ℕ}
    (rule : Alphabet → Alphabet → Alphabet → Alphabet)
    (seeds : Fin s → ScalarRequest Alphabet (d + d))
    (tests : Fin t → ScalarRequest Alphabet (d + d)) : Circuit (Gate Alphabet) (d + d) where
  kind := kind
  edges := FiniteCode.size (TableauWiring.Index Alphabet d)
  schema e := TableauWiring.schema rule ((FiniteCode.equiv (α := TableauWiring.Index Alphabet d)).symm e)
  seedCount := s
  seed q := ⟨.scalar (seeds q).letter, (seeds q).domain⟩
  testCount := t
  test q := ⟨.scalar (tests q).letter, (tests q).domain⟩
  seed_scalar _ := rfl
  test_scalar _ := rfl

section
variable {Alphabet : Type*} [FiniteCode Alphabet] {d s t : ℕ}
variable (rule : Alphabet → Alphabet → Alphabet → Alphabet)
variable (seeds : Fin s → ScalarRequest Alphabet (d + d))
variable (tests : Fin t → ScalarRequest Alphabet (d + d))

private theorem wire_of_schema (i : TableauWiring.Index Alphabet d)
    (a : Address (d + d)) (h : (TableauWiring.schema rule i).domain.Contains a) :
    (circuit rule seeds tests).Wire ((TableauWiring.schema rule i).source, a)
      ((TableauWiring.schema rule i).target, (TableauWiring.schema rule i).permutation.apply a)
      (TableauWiring.schema rule i).port := by
  refine ⟨FiniteCode.equiv (α := TableauWiring.Index Alphabet d) i, a, ?_, ?_, ?_, ?_⟩
  · simpa only [circuit, Equiv.symm_apply_apply] using h
  all_goals simp only [circuit, Equiv.symm_apply_apply]

private theorem wire_of_realized {g h : Gate Alphabet} {a b : Address (d + d)} {port : Bool}
    (he : ∃ e : TableauWiring.Index Alphabet d,
      (TableauWiring.schema rule e).source = g ∧ (TableauWiring.schema rule e).target = h ∧
      (TableauWiring.schema rule e).port = port ∧
      (TableauWiring.schema rule e).domain.Contains a ∧
      (TableauWiring.schema rule e).permutation.apply a = b) :
    (circuit rule seeds tests).Wire (g,a) (h,b) port := by
  obtain ⟨e, hs, ht, hp, ha, hb⟩ := he
  have hw := wire_of_schema rule seeds tests e a ha
  simpa only [hs, ht, hp, hb] using hw

theorem wire_iff (u v : Gate Alphabet × Address (d + d)) (port : Bool) :
    (circuit rule seeds tests).Wire u v port ↔
      TableauWiring.Edge rule d
        (u.1, TableauWiring.time u.2, TableauWiring.space u.2)
        (v.1, TableauWiring.time v.2, TableauWiring.space v.2) port := by
  constructor
  · rintro ⟨e, a, ha, rfl, rfl, rfl⟩
    exact TableauWiring.schema_sound rule ((FiniteCode.equiv (α := TableauWiring.Index Alphabet d)).symm e) a ha
  · rcases u with ⟨g,a⟩
    rcases v with ⟨h,b⟩
    intro he
    change TableauWiring.Edge rule d (g,TableauWiring.time a,TableauWiring.space a)
      (h,TableauWiring.time b,TableauWiring.space b) port at he
    generalize hta : TableauWiring.time a = ta at he
    generalize htb : TableauWiring.time b = tb at he
    generalize hxa : TableauWiring.space a = xa at he
    generalize hxb : TableauWiring.space b = xb at he
    cases he with
    | left x y z time space =>
        exact wire_of_realized rule seeds tests
          (TableauWiring.left_realized rule x y z a b (by omega) (by rw [hxa,hxb]))
    | center x y z time space =>
        exact wire_of_realized rule seeds tests
          (TableauWiring.center_realized rule x y z a b (by omega) (by rw [hxa,hxb]))
    | right x y z time space =>
        exact wire_of_realized rule seeds tests
          (TableauWiring.right_realized rule x y z a b (by omega) (by rw [hxa,hxb]))
    | pair x y z time space =>
        have hab : a = b := TableauWiring.address_ext (hta.trans htb.symm) (hxa.trans hxb.symm)
        subst b
        exact wire_of_schema rule seeds tests ((x,y,z),.inr (.inr (.inr false))) a
          (ProductDomain.contains_full a)
    | output x y z time space =>
        have hab : a = b := TableauWiring.address_ext (hta.trans htb.symm) (hxa.trans hxb.symm)
        subst b
        exact wire_of_schema rule seeds tests ((x,y,z),.inr (.inr (.inr true))) a
          (ProductDomain.contains_full a)

def Meaning (seed : ZMod (2 ^ d) → Alphabet) : Gate Alphabet × Address (d + d) → Prop
  | (.scalar a, v) => a = cyclicRun rule seed (TableauWiring.time v) (TableauWiring.space v)
  | (.pair a b _, v) => ∃ n, TableauWiring.time v = n + 1 ∧
      a = cyclicRun rule seed n (TableauWiring.space v - 1) ∧
      b = cyclicRun rule seed n (TableauWiring.space v)
  | (.triple a b c, v) => ∃ n, TableauWiring.time v = n + 1 ∧
      a = cyclicRun rule seed n (TableauWiring.space v - 1) ∧
      b = cyclicRun rule seed n (TableauWiring.space v) ∧
      c = cyclicRun rule seed n (TableauWiring.space v + 1)

def SeedsExact (seed : ZMod (2 ^ d) → Alphabet) : Prop :=
  ∀ (letter : Alphabet) (a : Address (d + d)),
    (∃ q, letter = (seeds q).letter ∧ (seeds q).domain.Contains a) ↔
      TableauWiring.time a = 0 ∧ letter = seed (TableauWiring.space a)

omit [FiniteCode Alphabet] in
private theorem edge_scalar {g : Gate Alphabet} {a : Alphabet} {n m : ℕ}
    {x y : ZMod (2 ^ d)} {port : Bool}
    (h : TableauWiring.Edge rule d (g,n,x) (.scalar a,m,y) port) :
    ∃ b c e, g = .triple b c e ∧ a = rule b c e ∧ n = m ∧ x = y := by
  cases h with
  | output b c e n x => exact ⟨b,c,e,rfl,rfl,rfl,rfl⟩

omit [FiniteCode Alphabet] in
private theorem edge_pair_false {g : Gate Alphabet} {a b c : Alphabet} {n m : ℕ}
    {x y : ZMod (2 ^ d)}
    (h : TableauWiring.Edge rule d (g,n,x) (.pair a b c,m,y) false) :
    g = .scalar a ∧ m = n + 1 ∧ y = x + 1 := by
  cases h
  exact ⟨rfl,rfl,rfl⟩

omit [FiniteCode Alphabet] in
private theorem edge_pair_true {g : Gate Alphabet} {a b c : Alphabet} {n m : ℕ}
    {x y : ZMod (2 ^ d)}
    (h : TableauWiring.Edge rule d (g,n,x) (.pair a b c,m,y) true) :
    g = .scalar b ∧ m = n + 1 ∧ y = x := by
  cases h
  exact ⟨rfl,rfl,rfl⟩

omit [FiniteCode Alphabet] in
private theorem edge_triple_false {g : Gate Alphabet} {a b c : Alphabet} {n m : ℕ}
    {x y : ZMod (2 ^ d)}
    (h : TableauWiring.Edge rule d (g,n,x) (.triple a b c,m,y) false) :
    g = .pair a b c ∧ m = n ∧ y = x := by
  cases h
  exact ⟨rfl,rfl,rfl⟩

omit [FiniteCode Alphabet] in
private theorem edge_triple_true {g : Gate Alphabet} {a b c : Alphabet} {n m : ℕ}
    {x y : ZMod (2 ^ d)}
    (h : TableauWiring.Edge rule d (g,n,x) (.triple a b c,m,y) true) :
    g = .scalar c ∧ m = n + 1 ∧ y = x - 1 := by
  cases h
  exact ⟨rfl,rfl,rfl⟩

theorem sound (seed : ZMod (2 ^ d) → Alphabet) (hs : SeedsExact seeds seed)
    (v : Gate Alphabet × Address (d + d)) (hv : (circuit rule seeds tests).True v) :
    Meaning rule seed v := by
  apply (circuit rule seeds tests).true_least (Meaning rule seed) ?_ ?_ ?_ v hv
  · rintro ⟨g,a⟩ ⟨q,hq,ha⟩
    change g = .scalar (seeds q).letter at hq
    subst g
    have hx := (hs (seeds q).letter a).mp ⟨q,rfl,ha⟩
    change (seeds q).letter = cyclicRun rule seed (TableauWiring.time a) (TableauWiring.space a)
    rw [hx.1]
    exact hx.2
  · rintro ⟨g,a⟩ ⟨h,b⟩ port hk hw hu
    cases h with
    | pair x y z => contradiction
    | triple x y z => contradiction
    | scalar c =>
      obtain ⟨x,y,z,hg,rfl,ht,hx⟩ := edge_scalar rule ((wire_iff rule seeds tests _ _ _).mp hw)
      dsimp only at hg ht hx
      subst g
      obtain ⟨n,hn,hl,hc,hr⟩ := hu
      change rule x y z = cyclicRun rule seed (TableauWiring.time b) (TableauWiring.space b)
      rw [← ht,hn,← hx,hl,hc,hr]
      rfl
  · rintro ⟨g,a⟩ ⟨h,b⟩ ⟨j,c⟩ hk hw₀ hw₁ hu₀ hu₁
    have he₀ := (wire_iff rule seeds tests _ _ _).mp hw₀
    have he₁ := (wire_iff rule seeds tests _ _ _).mp hw₁
    cases j with
    | scalar x => contradiction
    | pair x y z =>
      obtain ⟨hg,ht₀,hx₀⟩ := edge_pair_false rule he₀
      obtain ⟨hh,ht₁,hx₁⟩ := edge_pair_true rule he₁
      dsimp only at hg hh ht₀ ht₁ hx₀ hx₁
      subst g; subst h
      simp only [Meaning] at hu₀ hu₁ ⊢
      have ht : TableauWiring.time a = TableauWiring.time b := by omega
      refine ⟨TableauWiring.time a,ht₀,?_,?_⟩
      · simpa only [hx₀,add_sub_cancel_right] using hu₀
      · simpa only [hx₁,ht] using hu₁
    | triple x y z =>
      obtain ⟨hg,ht₀,hx₀⟩ := edge_triple_false rule he₀
      obtain ⟨hh,ht₁,hx₁⟩ := edge_triple_true rule he₁
      dsimp only at hg hh ht₀ ht₁ hx₀ hx₁
      subst g; subst h
      simp only [Meaning] at hu₀ hu₁ ⊢
      obtain ⟨n,hn,hl,hc⟩ := hu₀
      have ht : n = TableauWiring.time b := by omega
      refine ⟨n,ht₀.trans hn,?_,?_,?_⟩
      · simpa only [hx₀] using hl
      · simpa only [hx₀] using hc
      · simpa only [hx₁,sub_add_cancel,ht] using hu₁

def address (d n : ℕ) (x : ZMod (2 ^ d)) : Address (d + d) :=
  ProductAddress.join (ofNat d n) (ofNat d x.val)

@[simp] theorem time_address (d n : ℕ) (x : ZMod (2 ^ d)) (hn : n < 2 ^ d) :
    TableauWiring.time (address d n x) = n := by
  simp [TableauWiring.time,address,value_ofNat d n hn]

@[simp] theorem space_address (d n : ℕ) (x : ZMod (2 ^ d)) :
    TableauWiring.space (address d n x) = x := by
  simp [TableauWiring.space,address,value_ofNat d x.val (ZMod.val_lt x)]

theorem address_time_space (a : Address (d + d)) :
    address d (TableauWiring.time a) (TableauWiring.space a) = a := by
  apply TableauWiring.address_ext
  · exact time_address _ _ _ (TableauWiring.time_lt a)
  · exact space_address _ _ _

theorem complete (seed : ZMod (2 ^ d) → Alphabet) (hs : SeedsExact seeds seed)
    (n : ℕ) (hn : n < 2 ^ d) (x : ZMod (2 ^ d)) :
    (circuit rule seeds tests).True (.scalar (cyclicRun rule seed n x),address d n x) := by
  induction n generalizing x with
  | zero =>
    apply Circuit.True.seed
    obtain ⟨q,hq,ha⟩ := (hs (seed x) (address d 0 x)).mpr
      ⟨time_address d 0 x hn, by rw [space_address]⟩
    exact ⟨q,congrArg Gate.scalar hq,ha⟩
  | succ n ih =>
    have hn' : n < 2 ^ d := by omega
    let a := cyclicRun rule seed n (x - 1)
    let b := cyclicRun rule seed n x
    let c := cyclicRun rule seed n (x + 1)
    have hl : (circuit rule seeds tests).True (.scalar a,address d n (x - 1)) := ih hn' _
    have hc : (circuit rule seeds tests).True (.scalar b,address d n x) := ih hn' _
    have hr : (circuit rule seeds tests).True (.scalar c,address d n (x + 1)) := ih hn' _
    have hp : (circuit rule seeds tests).True (.pair a b c,address d (n+1) x) := by
      refine .andGate rfl ?_ ?_ hl hc
      · apply (wire_iff rule seeds tests _ _ _).mpr
        simpa only [Prod.fst,Prod.snd,time_address d n _ hn',time_address d (n+1) _ hn,
          space_address,sub_add_cancel] using (TableauWiring.Edge.left (d := d) (rule := rule) a b c n (x-1))
      · apply (wire_iff rule seeds tests _ _ _).mpr
        simpa only [Prod.fst,Prod.snd,time_address d n _ hn',time_address d (n+1) _ hn,
          space_address] using (TableauWiring.Edge.center (d := d) (rule := rule) a b c n x)
    have ht : (circuit rule seeds tests).True (.triple a b c,address d (n+1) x) := by
      refine .andGate rfl ?_ ?_ hp hr
      · apply (wire_iff rule seeds tests _ _ _).mpr
        exact .pair a b c _ _
      · apply (wire_iff rule seeds tests _ _ _).mpr
        simpa only [Prod.fst,Prod.snd,time_address d n _ hn',time_address d (n+1) _ hn,
          space_address,add_sub_cancel_right] using (TableauWiring.Edge.right (d := d) (rule := rule) a b c n (x+1))
    refine .scalar (b := false) rfl ?_ ht
    apply (wire_iff rule seeds tests _ _ _).mpr
    exact .output a b c _ _

theorem scalar_iff (seed : ZMod (2 ^ d) → Alphabet) (hs : SeedsExact seeds seed)
    (letter : Alphabet) (a : Address (d + d)) :
    (circuit rule seeds tests).True (.scalar letter,a) ↔
      letter = cyclicRun rule seed (TableauWiring.time a) (TableauWiring.space a) := by
  constructor
  · exact sound rule seeds tests seed hs _
  · intro h
    subst letter
    simpa only [address_time_space] using
      complete rule seeds tests seed hs (TableauWiring.time a) (TableauWiring.time_lt a) (TableauWiring.space a)

def rank : Gate Alphabet × ℕ × ZMod (2 ^ d) → ℕ
  | (.scalar _,n,_) => 3*n+2
  | (.pair _ _ _,n,_) => 3*n
  | (.triple _ _ _,n,_) => 3*n+1

omit [FiniteCode Alphabet] in
theorem edge_rank {u v : Gate Alphabet × ℕ × ZMod (2 ^ d)} {port : Bool}
    (h : TableauWiring.Edge rule d u v port) : rank u < rank v := by
  cases h <;> simp only [rank] <;> omega

theorem acyclic : (circuit rule seeds tests).Acyclic := by
  refine ⟨fun v => rank (v.1,TableauWiring.time v.2,TableauWiring.space v.2),?_⟩
  intro u v b h
  exact edge_rank rule ((wire_iff rule seeds tests u v b).mp h)

theorem edges_eq [Fintype Alphabet] : (circuit rule seeds tests).edges =
    FiniteCode.size Alphabet ^ 3 * (2*d^2+3*d+2) := by
  change FiniteCode.size (TableauWiring.Index Alphabet d) = _
  rw [← FiniteCode.card_eq_size,TableauWiring.schema_count,FiniteCode.card_eq_size]

end
end GroupWL.TableauCircuit
