import data.fin

open fin nat

def fin' := fin

variables {n : ℕ} (a b c : fin' n.succ)

instance : has_one (fin' n.succ) := ⟨(0 : fin n.succ)⟩
instance : has_mul (fin' n.succ) := ⟨((+) : fin n.succ → fin n.succ → fin n.succ)⟩

include a
private def inv : fin' n.succ :=
begin
  cases a,
  cases a_val,
  {
    exact 1,
  },
  {
    exact (n - a_val : fin n.succ),
  },
end
omit a

instance : has_inv (fin' n.succ) := ⟨inv⟩

private lemma mul_assoc : a * b * c = a * (b * c) :=
begin
  apply eq_of_veq,
  simp [(*), fin.add_def, add_assoc],
end

private lemma one_mul : 1 * a = a :=
begin
  apply eq_of_veq,
  simp [has_one.one, (*), fin.add_def, mod_eq_of_lt a.is_lt],
end

private lemma mul_one : a * 1 = a :=
begin
  apply eq_of_veq,
  simp [has_one.one, (*), fin.add_def, mod_eq_of_lt a.is_lt],
end

private lemma mul_left_inv : a⁻¹ * a = 1 :=
begin
  apply eq_of_veq,
  cases a,
  cases a_val,
  {
    simp only [has_one.one, (*), has_inv.inv, inv, fin.add_def],
    simp,
  },
  {
    simp only [(*), has_inv.inv, inv, fin.add_def, fin.sub_def],
    rw [coe_val_of_lt, coe_val_of_lt]; try { simp [lt_of_succ_lt a_property], },
    have : (n - a_val + a_val.succ) = n.succ,
    {
      rw add_succ,
      congr,
      apply nat.sub_add_cancel,
      apply le_of_lt,
      apply lt_of_succ_lt_succ,
      apply a_property,
    },
    rw this,
    apply mod_self,
  },
end

private lemma mul_comm : a * b = b * a :=
begin
  apply eq_of_veq,
  simp [(*), fin.add_def, add_comm],
end

instance : comm_group (fin' n.succ) :=
{
  mul := (*),
  mul_assoc := mul_assoc,
  one := 0,
  one_mul := one_mul,
  mul_one := mul_one,
  inv := inv,
  mul_left_inv := mul_left_inv,
  mul_comm := mul_comm,
}