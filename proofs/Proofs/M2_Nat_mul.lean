import Proofs.M1_Nat_plus

open Nat

namespace Mul
--############################################################################################################################

/--
### 곱셈은 좌분배법칙을 만족한다.

`버터*(코미+티그)=버터*코미+버터*티그`
-/

theorem distributive (butter kommy tig : Nat)
    :butter*(kommy+tig)=butter*kommy+butter*tig:=by

induction tig--                             티그에 대해서 귀납법을 쓰자

case zero =>--                              티그가 0이라면
--                                          버터*(코미+0)=버터*코미+버터*0을 보이면 된다.
  rw [Nat.add_zero]--                       버터*(코미+0)=버터*코미이다.
  rw [Nat.mul_zero]--                       또한, 버터*0=0이다.
  rw [Nat.add_zero]--                       따라서 버터*(코미+0)=버터*코미=버터*코미+0=버터*코미+버터*0이다.

case succ tig hypothesis=>--                티그에서 성립할 때 티그의 다음수에서도 성립함을 보이자
--                                          버터*(코미+티그의 다음수)=버터*코미+버터*(티그의 다음수)임을 보이면 된다.
  rw [Nat.add_succ]--                       코미+티그의 다음수=(코미+티그)의 다음수이다.
  repeat rw [Nat.mul_succ]--                곱셈의 정의에 의해 버터*((코미+티그)의 다음수)=버터*(코미+티그)+버터이며
--                                          버터*티그의 다음수=버터*티그+버터이다.
  rw [← Plus.associative]--                 버터*코미+(버터*티그+버터)=버터*코미+버터*티그+버터이다.
  rw [hypothesis]--                         가정에 의해 버터*(코미+티그)+버터=버터*코미+버터*티그+버터이므로 성립한다.

--############################################################################################################################

/--
### 곱셈은 결합법칙을 만족한다.

`(버터*코미)*티그=버터*(코미*티그)`
-/

theorem associative (butter kommy tig : Nat)
    :butter*kommy*tig=butter*(kommy*tig):=by

induction tig--                             티그에 대해서 귀납법을 쓰자.

case zero =>--                              티그가 0이라면
  repeat rw [Nat.mul_zero]--                (버터*코미)*0=0=버터*0=버터*(코미*0)으로 성립한다.

case succ tig hypothesis=>--                티그에서 성립할때 티그의 다음수에서도 성립함을 보이자.
--                                          (버터*코미)*티그의 다음수=버터*(코미*티그의 다음수)를 보이면 된다.
  repeat rw [Nat.mul_succ]--                곱셈의 정의에 의해 (버터*코미)*티그의 다음수=(버터*코미)*티그+버터*코미이며
--                                          코미*티그의 다음수=코미*티그+코미이다.
  rw [distributive]--                       분배법칙에 의해 버터*(코미*티그+코미)=버터*(코미*티그)+버터*코미이다.
  rw [hypothesis]--                         가정에 의해 (버터*코미)*티그+버터*코미=버터*(코미*티그)+버터*코미므로 성립한다.

--############################################################################################################################

/--
### 0에 어떤 자연수를 곱하든지 0이다.

`0*버터=0`
-/

theorem zero_mul_butter_eq_zero (butter : Nat)
    :0*butter=0:=by

induction butter--                          버터에 대해서 귀납법을 쓰자.

case zero =>--                              버터=0이라면
  rw [Nat.mul_zero]--                       0*0=0이므로 성립한다.

case succ butter hypothesis =>--            버터에서 성립할 때 버터의 다음수에서도 성립함을 보이자.
  rw [Nat.mul_succ]--                       곱셈의 정의에 의해 0*(버터의 다음수)=0*버터+0이다.
  rw [hypothesis, Nat.add_zero]--           가정과 덧셈에 정의에 의해 0*버터+0=0+0=0이므로 성립한다.

--############################################################################################################################

/--
### 1은 곱셈의 좌항등원이다.

`1*버터=버터`
-/

theorem one_mul_butter_eq_butter (butter : Nat)
    :1*butter=butter:=by

induction butter--                          버터에 대해서 귀납법을 쓰자.

case zero =>--                              버터=0이라면
  rw [Nat.mul_zero]--                       1*0=0이므로 성립한다.

case succ butter hypothesis =>--            버터에서 성립할 때 버터의 다음수에서도 성립함을 보이자.
  rw [Nat.mul_succ]--                       곱셈의 정의에 의해 1*버터의 다음수=1*버터+1이다.
  rw [hypothesis]--                         가정에 의해 1*버터+1=버터+1=버터의 다음수므로 성립한다.

--############################################################################################################################

/--
### 곱셈은 우분배법칙을 만족한다.

`(버터+코미)*티그=버터*티그+코미*티그`
-/
theorem right_distributive (butter kommy tig : Nat)
    :(butter+kommy)*tig=butter*tig+kommy*tig:=by

induction tig--                             티그에 대해 귀납법을 쓰자.

case zero =>--                              티그=0이라면
  repeat rw [Nat.mul_zero]--                (버터+코미)*0=0=0+0=버터*0+코미*0므로 성립한다.

case succ tig hypothesis =>--               티그에서 성립할 때 티그의 다음수에서도 성립함을 보이자.
  repeat rw [Nat.mul_succ]--                우선 증명하고자 하는 문장을 곱셈의 정의를 적용하여 정리하면 다음과 같이 된다.
--                                              `(버터+코미)*티그+(버터+코미)=버터*티그+버터+(코미*티그+코미)`
  repeat rw [← Plus.associative]--          이것을 보이기 위해 우선 결합법칙을 이용하면
--                                          (버터+코미)*티그+버터+코미=버터*티그+버터+코미*티그+코미를 보이면 된다는 것을 알 수 있다.
  rw [hypothesis]--                         가정에 의해 (버터+코미)*티그+버터+코미=버터*티그+코미*티그+버터+코미
  --                                        한편 좌변은 결합 법칙에 의해 버터*티그+버터+코미*티그+코미=버터*티그+(버터+코미*티그)+코미이고
  rw [Plus.associative (butter*tig) butter (kommy*tig)]
  --                                        교환 법칙을 쓰면 버터*티그+(버터+코미*티그)+코미=버터*티그+(코미*티그+버터)+코미이므로
  rw [Plus.commutative butter (kommy*tig)]
  rw [← Plus.associative]--                 결국 결합법칙을 쓰면 버터*티그+코미*티그+버터+코미=버터*티그+코미*티그+버터+코미로 성립한다.

--############################################################################################################################

/--
### 곱셈은 교환 법칙을 만족한다.
`버터*코미=코미*버터`
-/

theorem commutative (butter kommy : Nat)
    :butter*kommy=kommy*butter:=by

induction kommy--                           코미에 대해서 귀납법을 쓰자.

case zero =>--                              코미=0이라면
  rw [Nat.mul_zero]--                       버터*0=0이고
  rw [zero_mul_butter_eq_zero]--            0*버터=0이라서 성립한다.

case succ kommy hypothesis =>--             코미에서 성립할 때 코미의 다음수에서도 성립함을 보이자.
  rw [right_distributive]--                 우분배법칙에 의해 코미의 다음수*버터=(코미+1)*버터=코미*버터+1*버터이다.
  rw [Nat.mul_succ]--                       곱셈의 정의에 의해 버터*코미의 다음수=버터*코미+버터이다.
  rw [one_mul_butter_eq_butter]--           1*버터=버터이므로 코미의 다음수*버터=코미*버터+버터이다.
  rw [hypothesis]--                         가정에 의해 버터*코미+버터=코미*버터+버터이므로 성립한다.

--############################################################################################################################

/--
### 두 수를 곱해서 0이면 둘 줄 하나는 0이다.

`버터*코미=0이라면 버터=0이거나 코미=0`
-/

theorem butter_mul_kommy_eq_zero_imp_butter_or_kommy_eq_zero (butter kommy : Nat)
    :butter*kommy=0→(butter=0∨kommy=0):=by

intro h--                                   버터*코미=0이라고 가정하자.
induction butter--                          그리고 버터에 대해 귀납법을 적용하자.

case zero=>--                               버터=0이라면
  apply Or.inl--                            버터=0이므로 자명히 버터=0이거나 코미=0이다.
  rfl
case succ butter hypothesis=>--             버터에서 성립할 때 버터의 다음수에서도 성립함을 보이자.
  apply Or.inr--                            버터의 다음수*코미=코미*버터의 다음수이고
  rw [commutative] at h--                   곱셈의 정의에 의해 코미*버터의 다음수=코미*버터+코미이다.
  rw [Nat.mul_succ] at h--                  코미*버터+코미=0이므로 코미*버터=0이고 코미=0이다.
  replace h2:=(Plus.butter_plus_kommy_eq_zero_imp_butter_eq_kommy_eq_zero (kommy*butter) kommy)
  replace h:kommy=0:=And.right (h2 h)--     따라서 코미=0이므로 버터=0이거나 코미=0이다.
  exact h

--############################################################################################################################

/--
### 곱셈은 0이 아닌 자연수에 한해서 소거법칙을 만족한다.
`티그가 0이 아니라면, 버터*티그=코미*티그라면 버터=코미`
-/

theorem cancellation (butter kommy tig : Nat)
    :(¬(tig=0)→((butter*tig=kommy*tig)→butter=kommy)):=by

intro h h2--                                조건 2개를 각각 가정하자.
induction butter generalizing kommy--       버터에 대해서 귀납법을 쓰자.

case zero=>--                               버터=0이라면
  rw [zero_mul_butter_eq_zero] at h2--      버터*0=0=코미*티그이다.
  rw [Eq.comm] at h2--                      따라서 코미=0이거나 티그=0이다.
  match (butter_mul_kommy_eq_zero_imp_butter_or_kommy_eq_zero kommy tig h2) with
  | Or.inl h3=>--                           만약 코미=0이라면
   rw [Eq.comm]--                           코미=버터=0이므로 성립한다.
   trivial
  | Or.inr _=>--                            만약 티그=0인 상황은
   contradiction--                          우리의 가정과 모순되므로 고려 대상이 아니다.

case succ butter hypothesis=>--             버터에서 성립할 때 버터의 다음수에서도 성립함을 보이자.
  rw [commutative] at h2--                  교환법칙에 의해 버터의 다음수*티그=티그*버터의 다음수이며
  rw [Nat.mul_succ] at h2--                 이는 곱셈의 정의에 의해 티그*버터+버터이다.
  induction kommy--                         코미에 대해서 한번 더 귀납법을 쓰자.
  case zero=>--                             코미=0인 상황은
    rw [zero_mul_butter_eq_zero] at h2--    0*티그=0이므로
--                                          가정에 의해 티그*버터+티그=0이 되고
--                                          따라서 티그=0이 된다.
    have tig_eq_zero:tig=0:=And.right (
      (Plus.butter_plus_kommy_eq_zero_imp_butter_eq_kommy_eq_zero (tig*butter) tig) h2
      )
    contradiction--                         이것은 가정과 모순 되므로 고려대상이 아니다.

  case succ rufo hi=>--                    자연수 루포가 존재하여 코미가 루포의 다음수라면
    rw [commutative (rufo+1) tig] at h2--  교환법칙에 의해 루포의 다음수*티그=티그*루포의 다음수이고
    rw [Nat.mul_succ] at h2--                  이는 곱셈의 정의에 의해 티그*루포+티그이다.
    rw [Plus.cancellation] at h2--         가정과 소거법칙을 사용하면 티그*버터=티그*루포가 된다.
    rw [commutative tig butter] at h2--    교환법칙을 사용하여 식을 정리하면 버터*티그=루포*티그가 된다.
    rw [commutative tig rufo] at h2--      가정에 의해서 버터=루포가 된다.
    have butter_eq_kommy:butter=rufo:=((hypothesis rufo) h2)
    rw [Nat.succ_inj]--                    루포의 다음수가 코미였음을 상기하면
    exact butter_eq_kommy--                버터의 다음수=코미가 되어 성립하게 된다.
end Mul
