/-
Representations: semantic nets.

A semantic net is a finite set of labelled links between nodes. One label
is the hierarchy link (`isa`): a canary isa bird, a bird isa animal. Other
labels are properties (a bird `can` fly) or relations between concepts.
Nets may share structure and contain cycles, so walks up the hierarchy are
bounded by a step count.

* `level k n`: the nodes reached from `n` by exactly `k` hierarchy links.
* `valsAt k n l`: the values of property `l` stored at those nodes.
* `lookup n l`: property lookup with inheritance. Search moves up the
  hierarchy one level at a time and stops at the first level that stores
  the property, so a value stored nearer overrides one stored farther up
  (a penguin cannot fly, though birds can).
* `findVal single n l v`: verify one value of a property: climb until a
  level stores `v`. For a single-valued property (`single`), a different
  value found first is a contradiction and answers false; a many-valued
  property ("has wings", "has skin") accumulates up the hierarchy.
* `isaDist n m`: how many hierarchy links separate `n` from `m`.

Main results: a property stored at a node is found there (`lookup_local`);
otherwise it is inherited from the nearest level that stores it
(`lookup_inherits`); a value is found at the first level storing it
(`findVal_spec`), so a property stored once at a superordinate is
available to every subordinate that does not override it (cognitive
economy); and the distance found is the least level containing the target
(`isaDist_spec`).
-/

namespace Cog

/-- A semantic net: links `(from, label, to)`, and the label of the
hierarchy link. -/
structure SemNet (N L : Type) where
  links : List (N × L × N)
  isa : L

namespace SemNet

variable {N L : Type} [DecidableEq N] [DecidableEq L] (G : SemNet N L)

/-- The nodes `n` links to by label `l`. -/
def targets (n : N) (l : L) : List N :=
  (G.links.filter fun e => e.1 == n && e.2.1 == l).map fun e => e.2.2

/-- The nodes reached from `n` by exactly `k` hierarchy links. -/
def level : Nat → N → List N
  | 0, n => [n]
  | k + 1, n => (level k n).flatMap fun m => G.targets m G.isa

/-- The values of property `l` stored at level `k` above `n`. -/
def valsAt (k : Nat) (n : N) (l : L) : List N :=
  (G.level k n).flatMap fun m => G.targets m l

/-- Search for property `l` from level `k`, at most `fuel` further levels. -/
def search (n : N) (l : L) : Nat → Nat → Option (Nat × List N)
  | k, 0 => if G.valsAt k n l = [] then none else some (k, G.valsAt k n l)
  | k, f + 1 => if G.valsAt k n l = [] then search n l (k + 1) f else some (k, G.valsAt k n l)

/-- **Property lookup with inheritance**: the nearest level storing `l`,
within `fuel` levels, and the values stored there. -/
def lookup (fuel : Nat) (n : N) (l : L) : Option (Nat × List N) := G.search n l 0 fuel

/-- Search for value `v` of property `l` from level `k` up, at most `fuel`
further levels. For a single-valued property (`single`), another value
found first is a contradiction and ends the search, answering false. -/
def seek (single : Bool) (n : N) (l : L) (v : N) : Nat → Nat → Option (Bool × Nat)
  | k, f =>
    if v ∈ G.valsAt k n l then some (true, k)
    else if single && G.valsAt k n l != [] then some (false, k)
    else match f with
      | 0 => none
      | f + 1 => seek single n l v (k + 1) f

/-- **Verify a property value**: the level at which `v` is found (true), or,
for a single-valued property, at which a conflicting value is (false). -/
def findVal (single : Bool) (fuel : Nat) (n : N) (l : L) (v : N) : Option (Bool × Nat) :=
  G.seek single n l v 0 fuel

theorem seek_spec (single : Bool) (n : N) (l : L) (v : N) (k j fuel : Nat) (hj : k ≤ j)
    (hjf : j ≤ k + fuel)
    (hbelow : ∀ i, k ≤ i → i < j → v ∉ G.valsAt i n l ∧ (single = false ∨ G.valsAt i n l = []))
    (hat : v ∈ G.valsAt j n l) :
    G.seek single n l v k fuel = some (true, j) := by
  induction fuel generalizing k with
  | zero =>
    have : j = k := by omega
    subst this
    rw [seek]; simp [hat]
  | succ f ih =>
    by_cases hk : k = j
    · subst hk; rw [seek]; simp [hat]
    · obtain ⟨hv, hs⟩ := hbelow k (Nat.le_refl k) (by omega)
      rw [seek]
      have hs' : (single && G.valsAt k n l != []) = false := by
        rcases hs with h | h <;> simp [h]
      simp only [hv, hs', ite_false, Bool.false_eq_true]
      exact ih (k + 1) (by omega) (by omega) (fun i h1 h2 => hbelow i (by omega) h2)

/-- **A property value is found at the first level storing it**, when no
lower level stores it or, for a single-valued property, any other value. -/
theorem findVal_spec (single : Bool) (fuel : Nat) (n : N) (l : L) (v : N) (k : Nat)
    (hk : k ≤ fuel)
    (hbelow : ∀ i, i < k → v ∉ G.valsAt i n l ∧ (single = false ∨ G.valsAt i n l = []))
    (hat : v ∈ G.valsAt k n l) :
    G.findVal single fuel n l v = some (true, k) :=
  G.seek_spec single n l v 0 k fuel (Nat.zero_le _) (by omega) (fun i _ h2 => hbelow i h2) hat

/-- Search for `m` from level `k` up, at most `fuel` further levels. -/
def distFrom (n m : N) : Nat → Nat → Option Nat
  | k, 0 => if m ∈ G.level k n then some k else none
  | k, f + 1 => if m ∈ G.level k n then some k else distFrom n m (k + 1) f

/-- **Hierarchical distance**: the least number of hierarchy links from `n`
to `m`, within `fuel`. -/
def isaDist (fuel : Nat) (n m : N) : Option Nat := G.distFrom n m 0 fuel

theorem valsAt_zero (n : N) (l : L) : G.valsAt 0 n l = G.targets n l := by
  simp [valsAt, level]

theorem level_succ (k : Nat) (n m : N) :
    m ∈ G.level (k + 1) n ↔ ∃ p ∈ G.level k n, m ∈ G.targets p G.isa := by
  simp [level]

/-- Search from `k` finds the first level, from `k` on, that stores `l`. -/
theorem search_spec (n : N) (l : L) (k j fuel : Nat) (hj : k ≤ j) (hjf : j ≤ k + fuel)
    (hbelow : ∀ i, k ≤ i → i < j → G.valsAt i n l = []) (hat : G.valsAt j n l ≠ []) :
    G.search n l k fuel = some (j, G.valsAt j n l) := by
  induction fuel generalizing k with
  | zero =>
    have : j = k := by omega
    subst this
    simp [search, hat]
  | succ f ih =>
    by_cases hk : k = j
    · subst hk; simp [search, hat]
    · have hkv := hbelow k (Nat.le_refl k) (by omega)
      simp only [search, hkv, ite_true]
      exact ih (k + 1) (by omega) (by omega) (fun i h1 h2 => hbelow i (by omega) h2)

/-- **A property stored at a node is found there**, and overrides any value
stored higher up. -/
theorem lookup_local (fuel : Nat) (n : N) (l : L) (h : G.targets n l ≠ []) :
    G.lookup fuel n l = some (0, G.targets n l) := by
  rw [← valsAt_zero]
  exact G.search_spec n l 0 0 fuel (Nat.le_refl 0) (Nat.zero_le _) (fun i h1 h2 => by omega)
    (by rwa [valsAt_zero])

/-- **Inheritance**: if no level below `k` stores `l` and level `k` does,
lookup returns level `k`'s values. So a property stored once at a
superordinate is available to every subordinate that does not override it
(cognitive economy). -/
theorem lookup_inherits (fuel : Nat) (n : N) (l : L) (k : Nat) (hk : k ≤ fuel)
    (hbelow : ∀ i, i < k → G.valsAt i n l = []) (hat : G.valsAt k n l ≠ []) :
    G.lookup fuel n l = some (k, G.valsAt k n l) :=
  G.search_spec n l 0 k fuel (Nat.zero_le _) (by omega) (fun i _ h2 => hbelow i h2) hat

/-- A value stored at an ancestor is among the values found at its level. -/
theorem mem_valsAt (k : Nat) (n m v : N) (l : L) (hm : m ∈ G.level k n)
    (hv : v ∈ G.targets m l) : v ∈ G.valsAt k n l := by
  simp only [valsAt, List.mem_flatMap]
  exact ⟨m, hm, hv⟩

theorem distFrom_spec (n m : N) (k j fuel : Nat) (hj : k ≤ j) (hjf : j ≤ k + fuel)
    (hbelow : ∀ i, k ≤ i → i < j → m ∉ G.level i n) (hat : m ∈ G.level j n) :
    G.distFrom n m k fuel = some j := by
  induction fuel generalizing k with
  | zero =>
    have : j = k := by omega
    subst this
    simp [distFrom, hat]
  | succ f ih =>
    by_cases hk : k = j
    · subst hk; simp [distFrom, hat]
    · have hkv := hbelow k (Nat.le_refl k) (by omega)
      simp only [distFrom, hkv, ite_false]
      exact ih (k + 1) (by omega) (by omega) (fun i h1 h2 => hbelow i (by omega) h2)

/-- **Distance is the least level** containing the target. -/
theorem isaDist_spec (fuel : Nat) (n m : N) (k : Nat) (hk : k ≤ fuel)
    (hbelow : ∀ i, i < k → m ∉ G.level i n) (hat : m ∈ G.level k n) :
    G.isaDist fuel n m = some k :=
  G.distFrom_spec n m 0 k fuel (Nat.zero_le _) (by omega) (fun i _ h2 => hbelow i h2) hat

end SemNet

end Cog
