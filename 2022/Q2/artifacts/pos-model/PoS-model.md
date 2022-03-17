simplification 1: single token type
simplification 2: can I remove epoched?

```go
become_validator(validator_address, consensus_key)
{
  validators[validator_address].reward_address = staking_reward_address
  validators[validator_address].state = pending
  var e1 = set(validators[validator_address].consensus_key, consensus_key)
  var e2 = set(validators[validator_address].status, candidate)
  append(pipeline[cur_epoch+pipeline_length], [e1,e2])
}
```

```go
deactivate(validator_address)
{
  var e1 = set(validators[validator_address].status, inactive)
  append(pipeline[cur_epoch+pipeline_length], e1)
}
```

```go
reactivate(validator_address)
{
  validators[validator_address].state = pending
  var e1 = set(validators[validator_address].status, candidate)
  append(pipeline[cur_epoch+pipeline_length], e1)
}
```

```go
self_bond(validator_address, amount)
{
  balance[validator_address] -= amount
  balance[pos] += amount
  var e1 = add(bond[validator_address][validator_address].deltas[cur_epoch], amount)
  var e2 = add(validators[validator_address].total_deltas[cur_epoch+pipeline_length], amount)
  var e3 = fun(update_voting_power(validator_address))
  var e4 = fun(update_total_voting_power())
  var e5 = fun(update_validator_set))
  append(pipeline[cur_epoch+pipeline_length], [e1,e2,e3,e4,e5])
}
```

```go
compute_total(deltas)
{
  var sum = 0
  forall(delta in deltas){
    sum += delta.amount
  }
  return sum
}
```

```go
unbound(validator_address, amount)
{
  var total_bonded = compute_total(bond[validator_address][validator_address].deltas)
  if (total_bonded < amount) then panic
  var remain := amount
  foreach (bond in bonds[validator_address][validator_address].deltas)) while (remain > 0) do
    if amount > remain then
      var unbond_amount = remain
      bonds[validator_address][validator_address].deltas[bond.epoch].amount -= remain
    else
      var unbond_amount = next.amount
      bonds[validator_address][validator_address].deltas[bond.epoch].amount = 0
    unbonds[validator_address][validator_address].deltas[(bond.epoch,cur_epoch)] = unbond_amount
    remain -= unbond_amount
  var e1 = substract(validators[validator_address].total_deltas[token][cur_epoch+unbonding_length], amount)
  var e2 = fun(update_voting_power,validator_address)
  var e3 = fun(update_total_voting_power,[])
  var e4 = fun(update_validator_set,[])
  append(pipeline[cur_epoch+unbonding_length], [e1,e2,e3,e4])
}
```

```go
withdraw_unbonds(validator_address)
{
  var unbonds = unbonds[validator_address][validator_address].deltas)
  if (unbonds == []) then panic
  //could we have unbound.end < cur_epoch, when?
  foreach (unbond in unbounds s.t. unbound.end <= cur_epoch) do
    var amount_after_slashing = unbond.amount
    foreach (slash in slashes[validator_address] s.t. unbond.start <= slash.epoch && slash.epoch <= unbond.end)
      amount_after_slashing *= (10000 - slash.rate) / 10000)
    balance[validator_address] +=amount_after_slashing
    balance[pos] -= amount_after_slashing
    //removing unbonds and slashes?
}
```

```go
change_consensus_key(validator_address)
{
  var e1 = set(validators[validator_address].consensus_key, consensus_key)
  append(pipeline[cur_epoch+pipeline_length], e1)
}
```

```go
new_evidence(evidence){
  append(slash[evidence.validator_address], evidence)
  var max_epoch := max{epoch | validators[validator_address].total_deltas[epoch] != 0 && epoch <= evidence.epoch}
  var slashed_amount := validators[validator_address].total_deltas[max_epoch]*evidence.slash_rate
  e1 := substract(validators[validator_address].total_deltas[cur_epoch+pipeline_length], slashed_amount)
  append(pipeline[cur_epoch+pipeline_length], e1)
  e2 := fun(update_voting_power(validator_address))
  append(pipeline[cur_epoch+pipeline_length], e2)
  e3 := fun(update_total_voting_power())
  append(pipeline[cur_epoch+pipeline_length], e3)
  e4 := fun(update_validator_set))
  append(pipeline[cur_epoch+pipeline_length], e4)
}
```

```go
calculate_slash_rate()
{

}
```

```go
end_of_epoch()
{

}
```