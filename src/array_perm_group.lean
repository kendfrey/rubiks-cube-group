import algebra.group
import data.equiv.basic
import array_group

open equiv

section perm_array

  parameters {n : ℕ} {α : Type*}

  @[simp] private lemma array.read_def {f : fin n → α} {i : fin n} : array.read { data := f } i = f i := rfl

  def perm_array (a : array n α) (p : perm (fin n)) : array n α := ⟨a.read ∘ p.inv_fun⟩

  lemma perm_array_def (a : array n α) (p : perm (fin n)) : perm_array a p = ⟨a.read ∘ p.inv_fun⟩ := rfl

  @[simp] lemma perm_array_array_one {p : perm (fin n)} [group α] : perm_array 1 p = 1 :=
  begin
    apply array.ext,
    intros i,
    refl,
  end

  @[simp] lemma perm_array_perm_one {a : array n α} : perm_array a 1 = a :=
  begin
    apply array.ext,
    intros i,
    refl,
  end

  @[simp] lemma perm_array_comp {a : array n α} {p₁ p₂ : perm (fin n)} : perm_array (perm_array a p₁) p₂ = perm_array a (p₂ * p₁) :=
  begin
    apply array.ext,
    simp [perm_array_def, perm.mul_def],
  end

end perm_array

section

parameters {n : ℕ} {α : Type*} [group α]

def array_perm (n : ℕ) (α : Type*) := array n α × perm (fin n)

@[reducible] private def ap := array_perm n α

variables (a b c : ap)

private def mul : ap := (perm_array a.fst b.snd * b.fst, b.snd * a.snd)
private def inv : ap := (perm_array a.fst⁻¹ a.snd⁻¹, a.snd⁻¹)

instance array_perm.has_mul : has_mul ap := ⟨mul⟩
instance array_perm.has_one : has_one ap := ⟨(mk_array n 1, 1)⟩
instance array_perm.has_inv : has_inv ap := ⟨inv⟩

@[simp] private lemma mul_def : a * b = (perm_array a.fst b.snd * b.fst, b.snd * a.snd) := rfl
@[simp] private lemma one_def : (1 : ap) = (mk_array n 1, 1) := rfl
@[simp] private lemma inv_def : a⁻¹ = (perm_array a.fst⁻¹ a.snd⁻¹, a.snd⁻¹) := rfl

private lemma mul_assoc : a * b * c = a * (b * c) :=
begin
  dsimp,
  congr' 1,
  apply array.ext,
  intros i,
  simp only [perm_array_def, function.comp, array.read_mul, array.read_def, mul_assoc],
  refl,
end

private lemma one_mul : 1 * a = a :=
begin
  dsimp,
  change (perm_array 1 a.snd * a.fst, a.snd * 1) = a,
  rw perm_array_array_one,
  simp,
end

private lemma mul_one : a * 1 = a :=
begin
  dsimp,
  rw perm_array_perm_one,
  change (a.fst * 1, 1 * a.snd) = a,
  simp,
end

private lemma mul_left_inv : a⁻¹ * a = 1 :=
begin
  dsimp,
  rw perm_array_comp,
  simp,
  refl,
end

instance array_perm_group : group ap :=
{
  mul := (*),
  mul_assoc := mul_assoc,
  one := 1,
  one_mul := one_mul,
  mul_one := mul_one,
  inv := has_inv.inv,
  mul_left_inv := mul_left_inv,
}

end