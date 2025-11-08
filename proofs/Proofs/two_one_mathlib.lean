import Mathlib.Tactic
open Nat -- Nat=자연수.
section second_exercise -- 2번 문제
theorem zero_plus_butter_eq_butter(butter:Nat):0+butter=butter:=by
induction butter
case zero => -- 버터=0일때를 먼저 보이자.
  rw [Nat.add_zero]; -- 0+0=0이다. (덧셈의 정의에서)
  -- 0=0으로 만족한다.
case succ butter hypothesis => -- 버터에서 만족할때 버터의 다음수에서도 만족함을 보이자.
  rw [← Nat.add_assoc] -- 0+(버터+1)=(0+버터)+1이다. (결합법칙, 이전 편에 증명했다.)
  rw [hypothesis] -- 가정에 의해 0+버터=버터.
  -- 버터의 다음수=버터의 다음수로 만족한다.

theorem one_plus_butter_eq_butter_plus_one(butter:Nat):1+butter=butter+1:=by
induction butter
case zero => -- 버터=0일때를 먼저 보이자.
  rw [zero_plus_butter_eq_butter,Nat.add_zero] -- 1+0=0+1=1이다. (덧셈의 정의와 zero_plus_butter_eq_butter로 부터)
  -- 1=1로 성립한다.
case succ butter hypothesis => -- 버터에서 만족할때 버터의 다음수에서도 만족함을 보이자.
  rw [← Nat.add_assoc] -- 1+(버터+1)=(1+버터)+1이다. (RG?)
  rw [hypothesis] -- 가정에 의해 버터+1=1+버터.
  -- (버터+1)+1=(버터+1)+1로 성립한다.

theorem butter_plus_kommy_eq_kommy_plus_butter (butter kommy:Nat):butter+kommy=kommy+butter:=by
induction kommy -- 이번엔 코미에 대해 귀납법을 쓰자.
case zero => -- 코미=0일때를 먼저 보이자.
  rw [Nat.add_zero, zero_plus_butter_eq_butter] -- 버터+0=0+버터=버터이다. (덧셈의 정의와 zero_plus_butter_eq_butter에 의해서)
  -- 버터=버터로 성립.
case succ kommy hypothesis => -- 코미에서 만족할때 코미의 다음수에서도 만족함을 보이자.
  rw [Nat.add_assoc] -- (코미+1)+버터=코미+(1+버터)이다. (RG?)
  rw [one_plus_butter_eq_butter_plus_one] -- 1+버터=버터+1. (one_plus_butter_eq_butter_plus_one에 의해)
  repeat rw [Nat.add_succ]
  -- 버터+코미의 다음수=(버터+코미)의 다음수.
  -- 코미+버터의 다음수=(코미+버터)의 다음수 (덧셈의 정의에서).
  rw [hypothesis] -- 가정에 의해 버터+코미=코미+버터.
  -- 따라서 (코미+버터)의 다음수=(코미+버터)의 다음수.
end second_exercise


section third_exercise -- 3번 문제
theorem butter_plus_tig_eq_kommy_plus_tig_iff_butter_eq_kommy(butter kommy tig:Nat):(butter+tig=kommy+tig)↔(butter=kommy):=by
induction tig -- 티그에 대해서 귀납법을 쓰자.
case zero => -- 티그=0일때를 먼저 보이자.
  repeat rw [Nat.add_zero] -- 버터+0=버터, 코미+0=코미. (덧셈의 정의)
  -- 버터=코미 <-> 버터=코미로 성립한다.
case succ tig hypothesis => -- 타그에서 만족하면 티그의 다음수에서도 만족함을 보이자.
  apply Iff.intro -- -> 와 <-를 각각 따로 보이자.

  -- (->)
  repeat rw [← Nat.add_assoc]
  -- 버터+(티그+1)=(버터+티그)+1
  -- 코미+(티그+1)=(코미+티그)+1 (RG?)
  rw [Nat.succ_inj] -- 어떤 수 버터, 코미에 대해 버터의 다음수=코미의 다음수면 버터=코미 (자연수의 정의)
  rw [hypothesis] -- 가정에 의해 코미=버터
  intro h
  exact h

  -- (<-)
  repeat rw [← Nat.add_assoc]
  -- 버터+(티그+1)=(버터+티그)+1
  -- 코미+(티그+1)=(코미+티그)+1 (RG?)
  rw [Nat.succ_inj] -- 어떤 수 버터, 코미에 대해 버터의 다음수=코미의 다음수면 버터=코미 (자연수의 정의)
  rw [hypothesis] -- 가정에 의해 코미=버터
  intro h
  exact h
end third_exercise
