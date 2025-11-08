open Nat

theorem ambpc_eq_ambpamc(a b c:Nat):a*(b+c)=a*b+a*c:=by
induction c
case zero =>
  rw [Nat.add_zero]
  rw [Nat.mul_zero]
  rw [Nat.add_zero]
case succ c h=>
rw [← Nat.add_assoc]
repeat rw [Nat.mul_succ]
rw [← Nat.add_assoc]
rw [h]

theorem amb_mc_eq_am_bmc(a b c:Nat):a*b*c=a*(b*c):=by
induction c
case zero =>
  repeat rw [Nat.mul_zero]
case succ c h=>
  repeat rw [Nat.mul_succ]
  rw [ambpc_eq_ambpamc]
  rw [h]
