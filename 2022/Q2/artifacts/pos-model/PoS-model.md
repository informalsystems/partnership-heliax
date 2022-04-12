## Assumptions/simplifications

- There is a single token type

## Data types

```go
type Addr
type Key
type Epoch uint
type VotingPower float

type Validator struct {
  consensus_key map<Epoch, Key>
  state map<Epoch, {inactive, pending, candidate}>
  total_deltas map<Epoch, amount:int>
  voting_power map<Epoch, VotingPower>
  reward_address Addr
}

type Bond struct {
  validator Addr //not used
  source Addr //not used
  deltas map<Epoch, int>
  }

type Unbond struct {
  validator Addr //not used
  source Addr //not used
  deltas map<(start:Epoch, end:Epoch), int>
}

type Slash struct {
  epoch Epoch
  validator Addr
  block_height int //not used
  rate float
  slash_type //not used
}

type WeightedValidator struct {
  validator Addr
  voting_power float
}

type ValidatorSet struct {
  active orderedset<WeightedValidator>
  inactive orderedset<WeightedValidator>
}
```

## Variables

```go
cur_epoch ← 0 in Epoch //current epoch

validators[] in Addr → Validator //map from address to validator
balances[] in Addr → int //map from address to integer
bonds[][] in (Addr X Addr) → Bond //map from address to map from address to bond
unbonds[][] in (Addr X Addr) → Unbond  //map from (address, address) to unbond
slashes[] in Addr → 2^Slash //map from address to list of slashes

validator_sets[] in Epoch → ValidatorSet //map from epoch to validator_set
total_voting_power[] in Epoch to VotingPower //map from epoch to voting_power
```

## Validator transactions

```go
tx_become_validator(validator_address, consensus_key, staking_reward_address)
{
  //VP:https://github.com/anoma/anoma/blob/master/proof_of_stake/src/validation.rs#L421
  //https://github.com/anoma/anoma/blob/master/proof_of_stake/src/validation.rs#L459
  //https://github.com/anoma/anoma/blob/master/proof_of_stake/src/validation.rs#L471
  //COMMENT: In the code they check not only at cur_epoch but at all epochs between cur_epoch and the offset. Double-check
  //COMMENT: I do not see in the code where they check that the consensus key is not an old one (this is in the docs).
  //COMMENT: todo: check there are no consensus_key changes schedule between cur_epoch and the offset. If this necessary though? should
  //not be enough with the state checks?
  //https://github.com/anoma/anoma/blob/master/proof_of_stake/src/validation.rs#L515
  var pre_state = read_epoched_field(validators[validator_address].state, cur_epoch)
  if (pre_state == ⊥ && validator_address != staking_reward_address) then
    //reward_address is not in the docs/spec validator struct
    validators[validator_address].reward_address = staking_reward_address
    //set status to pending inmediately
    validators[validator_address].state[cur_epoch] = pending
    //set status to candidate and consensus key at n + pipeline_length
    validators[validator_address].consensus_key[cur_epoch+pipeline_length] = consensus_key
    validators[validator_address].state[cur_epoch+pipeline_length] = candidate
}
```

```go
//COMMENT: races between become_validate or reactivate and deactivate. deactivate does not write anything inmediately. This is related to the validity predicates
tx_deactivate(validator_address)
{
  //VP:https://github.com/anoma/anoma/blob/master/proof_of_stake/src/validation.rs#L471
  //COMMENT: we cannot think of a scenario in which pre_state_offset is equal pending, but the VP seems
  //to be conern about it. Did we misunderstand the VP? This also applies to the tx_reactivate transaction
  var pre_state_offset = read_epoched_field(validators[validator_address].state, cur_epoch+pipeline_length)
  if (pre_state_offset in {pending, candidate}) then
    //set status to inactive at n + pipeline_length
    validators[validator_address].state[cur_epoch+pipeline_length] = inactive
}
```

```go
tx_reactivate(validator_address)
{
  //VP:https://github.com/anoma/anoma/blob/master/proof_of_stake/src/validation.rs#L459
  //https://github.com/anoma/anoma/blob/master/proof_of_stake/src/validation.rs#L471
  var pre_state = read_epoched_field(validators[validator_address].state, cur_epoch)
  var pre_state_offset = read_epoched_field(validators[validator_address].state, cur_epoch+pipeline_length)
  if (pre_state == inactive && pre_state_offset in {pending, inactive}) then
    //set status to pending inmediately
    validators[validator_address].state[cur_epoch] = pending
    //set status to candidate at n + pipeline_length
    validators[validator_address].state[cur_epoch+pipeline_length] = candidate
}
```

```go
tx_self_bond(validator_address, amount)
{
  bond(validator_address, validator_address, amount, pipeline_length)
}
```

```go
tx_unbond(validator_address, amount)
{
  unbond(validator_address, validator_address, amount)
```

```go
tx_withdraw_unbonds_validator(validator_address)
{
  //COMMNET: in the docs, the system panics if no self-unbonds. Why? In our view, if a user
  //attemps to withdraw but has no self-unbounds, the the transaction is a noop. Is there something
  //wrong about assuming that?
  else withdraw(validator_address, validator_address)
}
```

```go
tx_change_consensus_key(validator_address, consensus_key)
{
  //set consensus key at n + pipeline_length
  validators[validator_address].consensus_key[cur_epoch+pipeline_length] = consensus_key
}
```
## Delegator transactions

```go
tx_delegate(validator_address, delegator_address, amount)
{
  bond(validator_address, delegator_address, amount, pipeline_length)
}
```

```go
tx_undelegate(validator_address, delegator_address, amount)
{
  unbond(src_validator_address, delegator_address, amount)
}
```

```go
tx_redelegate(src_validator_address, dest_validator_address, delegator_address, amount)
{
  unbond(src_validator_address, delegator_address, amount)
  bond(dst_validator_address, delegator_address, amount, unbonding_length)
}
```

```go
tx_withdraw_unbonds_delegator(delegator_address)
{
  //COMMENT: When a validator withdraws and there are no unbonds, it panics. Shall
  //we do something similar here? IMO, we should never panic (including in the validator's case),
  //at the end, if there are no unbonds, the withdraw operation is a noop--nothing wrong with that. 
  forall (validator_address in validators) do
    withdraw(validator_address, delegator_address)
}
```

## PoS functions


```go
//This function is called by transactions tx_self_bond, tx_delegate and tx_redelegate
//the only possible values for offset_length are pipeline_length and ubonding_length
func bond(validator_address, delegator_address, amount, offset_length)
{
  if is_validator(validator_address) then
    //add amount bond to delta at n+offset_length
    bonds[delegator_address][validator_address].deltas[cur_epoch+offset_length] += amount
    //debit amount form delegator account and credit it to the PoS account
    balances[delegator_address] -= amount
    balances[pos] += amount
    //compute new total_deltas and write it at n+offset_length
    var total = total_deltas_at(validators[validator_address].total_deltas, cur_epoch+offset_length)
    validators[validator_address].total_deltas[cur_epoch+offset_length] = total + amount
    //update validator's voting_power, total_voting_power and validator_sets at n+offset_length
    power_before = total_deltas_at(validators[validator_address].voting_power, cur_epoch+offset_length)
    power_after = update_voting_power(validator_address, cur_epoch+offset_length)
    update_total_voting_power(cur_epoch+offset_length)
    update_validator_sets(validator_address, cur_epoch+offset_length, power_before, power_after)
}
```

```go
//This function is called by transactions tx_unbond, tx_undelegate and tx_redelegate
func unbond(validator_address, delegator_address, amount)
{
  //compute total bonds from delegator to validator
  //COMMENT: it computes deltas up to cur_epoch + unbonding_length, is this correct? This is like that to match from where 
  //the model starts decrementing bonds.
  var delbonds = compute_total_from_deltas(bonds[delegator_address][validator_address].deltas, cur_epoch + unbonding_length)
  //check if there are enough bonds
  //this serves to check that there are bonds (in the docs) and that these are greater than the amount we are trying to unbond
  if (delbonds < amount) then panic()
  //Decrement bond deltas and create unbonds
  var remain = amount
  //COMMENT: Why initializing epoch_counter to cur_epoch + unbonding_length + 1? First there cannot be positive bonds beyond
  //cur_epoch + pipeline_length. Second, this could lead to scenarios in which one starts unbonding before a bond is materialized.
  //See: https://github.com/informalsystems/partnership-heliax/issues/6
  var epoch_counter = cur_epoch + unbonding_length + 1
  while remain > 0 do
    epoch_counter = max{epoch | bonds[delegator_address][validator_address].deltas[epoch] > 0 && epoch < epoch_counter}
    var bond = bonds[delegator_address][validator_address].deltas[epoch_counter]
    if bond > remain then var unbond_amount = remain
    else var unbond_amount = bond
    unbonds[delegator_address][validator_address].deltas[(epoch_counter,cur_epoch+unbonding_length)] += unbond_amount
    remain -= unbond_amount
  //COMMENT: still unsure about this. Now it only creates a single bond record at cur_epoch+unbonding_length.
  bonds[delegator_address][validator_address].deltas[cur_epoch+unbonding_length] -= amount
  //compute new total_deltas and write it at n+unbonding_length
  var total = total_deltas_at(validators[validator_address].total_deltas, cur_epoch+unbonding_length)
  //COMMENT: invariant: given an epoch e, validators[validator_address].total_deltas[e] >= bonds[delegator_address][validator_address].deltas 
  // This is beacuse total_deltas includes selfbonds and delegated-bonds. Needs to be proved.
  //COMMENT: thinking more about this issue, maybe that's not true due to slashing! So there might be a problem here as total-deltas may go
  //below 0.
  //See: https://github.com/informalsystems/partnership-heliax/issues/7
  validators[validator_address].total_deltas[cur_epoch+unbonding_length] = total - amount
  //update validator's voting_power, total_voting_power and validator_sets at n+unbonding_length
  power_before = total_deltas_at(validators[validator_address].voting_power, cur_epoch+unbonding_length)
  power_after = update_voting_power(validator_address, cur_epoch+unbonding_length)
  update_total_voting_power(cur_epoch+unbonding_length)
  update_validator_sets(validator_address, cur_epoch+unbonding_length, power_before, power_after)
}
```

```go
//This function is called by transactions tx_withdraw_unbonds_validator and tx_withdraw_unbonds_delegator
func withdraw(validator_address, delegator_address)
{
  //COMMENT: check that the epoch check is done on unbond.end and not somehting else. In docs says unbond.epoch, which is unclear
  var delunbonds = {<start,end,amount> | amount = unbonds[delegator_address][validator_address].deltas[(start, end)] > 0 && end <= cur_epoch }
  //substract any pending slash before withdrawing
  forall (<start,end,amount> in selfunbonds) do
    //COMMENT: is the amount slashed here the same than the one slashed when evidence is found? This is an important point
    var amount_after_slashing = unbond.amount
    forall (slash in slashes[validator_address] s.t. start <= slash.epoch && slash.epoch <= end)
      amount_after_slashing *= unbond.amount * slash.rate
    balance[delegator_address] += amount_after_slashing
    balance[pos] -= amount_after_slashing
    //remove unbond
    unbonds[delegator_address][validator_address].deltas[(start,end)] = 0
    //COMMENT: the documentation says to "burn" slashed tokens. I guess this means moving them to the slash pool
    //Anyway, this is not model, as currently those tokens never leave the slash pool.
}
```

```go
//assuming evidence is of type Slash for simplicity
//COMMENT:can total_deltas go below zero due to slashing?
//Check https://github.com/informalsystems/partnership-heliax/pull/4#discussion_r833447459
func new_evidence(evidence){
  append(slashes[evidence.validator], evidence)
  //COMMENT: how to compute the slashed rate when there is no cubic slashing? now using evidence.slash_rate
  //COMMENT: the salshed amount is computed from total deltas up to evidence.epoch and its deducted at n+pipeline_length. Not saying this is a problem, but it is something to discuss
  //compute slash amount
  var total_evidence = total_deltas_at(validators[evidence.validator].total_deltas, evidence.epoch)
  var slashed_amount = total_evidence*evidence.rate
  //compute new total_deltas and write it at n+pipeline_length
  var total_offset = total_deltas_at(validators[evidence.validator].total_deltas, cur_epoch+pipeline_length)
  validators[evidence.validator].total_deltas[cur_epoch+pipeline_length] = total_offset - slashed_amount 
  //update validator's voting_power, total_voting_power and validator_sets at n+pipeline_length
  power_before = total_deltas_at(validators[validator_address].total_deltas, cur_epoch+pipeline_length)
  power_after = update_voting_power(evidence.validator, cur_epoch+pipeline_length)
  update_total_voting_power(cur_epoch+pipeline_length)
  update_validator_sets(evidence.validator, cur_epoch+pipeline_length, power_before, power_after)
}
```

```go
//COMMENT: shall we do updates to this state to happen once at the end of an epoch? This has been discussed.
//Tomas agreed is interesting, but they are not doing it rigth know.
//COMMENT: still unclear from the docs. Why are unbonds substracted? When creating unbonds, we already decrement bonds,
//so we should not substract them here again, unless I am missing something. This is now resolved: there was a typo in the spec.
func update_voting_power(validator_address, epoch)
{
  //compute bonds from total_deltas 
  //COMMENT: if I understand correctly, total_deltas is total_bonded_tokens, including both selfbonded and
  //delegated_bonds. This has been confirmed by Tomas.
  var bonds = total_deltas_at(validators[validator_address].total_deltas, epoch)
  //compute the new voting power
  var power_after = votes_per_token*bonds
  //update voting power and return it
  validators[validator_address].voting_power[epoch] = power_after
  return power_after
}
```
```go
func update_total_voting_power(epoch)
{
  var total = 0
  forall (validator in validator_sets[epoch].active U validator_sets[epoch].inactive) do
    total += validator.voting_power
  total_voting_power[cur_epoch+unbonding_length] = total
}
```
```go
//COMMENT: is there any way to break ties? Let's say an inactive validator increases its voting power such that
//it matches min_active.voting power. Who does make it to the active set?
func update_validator_sets(validator_address, epoch, power_before, power_after)
{
  var min_active = first(validator_sets[epoch].active)
  var max_inactive = last(validator_sets[epoch].inactive)
  if (power_before >= max_inactive.voting_power) then
    //if active but it loses power below the max_inactive then move validator to inactive
    //and promote max_inactive
    if (power_after < max_inactive.voting_power) then
      remove(validator_sets[epoch].active, validator_address)
      insert(validator_sets[epoch].active, max_inactive)
      remove(validator_sets[epoch].inactive, max_inactive.validator)
      insert(validator_sets[epoch].inactive, <validator_address, power_after>)
    //if active and its change in power does not degrade it to inactive, then update its voting power
    else
      remove(validator_sets[epoch].active, validator_address)
      insert(validator_sets[epoch].active, <validator_address, power_after>)
  else
    //if inactive and gains power above the min_active, then insert into active and
    //degrade min_active 
    if (power_after > min_active.voting_power) then
      remove(validator_sets[epoch].inactive, validator_address)
      add(validator_sets[epoch].inactive, min_active)
      remove(validator_sets[epoch].active, min_active.validator)
      add(validator_sets[epoch].active, <validator_address, power_after>)
    //if inactive and its change in power does not promote it to active, then update its voting power
    else
      remove(validator_sets[epoch].inactive, validator_address)
      insert(validator_sets[epoch].inactive, <validator_address, power_after>)
}
```


```go
//https://github.com/anoma/anoma/blob/c366704610f1f823fc696815e843f5a4ab3431ea/proof_of_stake/src/lib.rs#L1457
func is_validator(validator_address){
  var epoch = cur_epoch
  while epoch <= cur_epoch+pipeline_length
    if (read_epoched_field(validators[validator_address].state, epoch) not in {pending, candidate}) then return false
    epoch++
  return true
}
```

## Auxiliary functions

```go
func read_epoched_field(field, upper_epoch){
  var assigned_epochs = {epoch | field[epoch] != ⊥ && epoch <= upper_epoch}
  if (assigned_epochs is empty) then return ⊥
  else return field[max{assigned_epochs}]
}
```

```go
func total_deltas_at(total_deltas, upper_epoch){
  var value = read_epoched_field(total_deltas, upper_epoch)
  if (value == ⊥) then return 0
  else return value
}
```

```go
//I have added epoch to the function, I think it is simple.
func compute_total_from_deltas(deltas, upper_epoch)
{
  var epoch = 0
  var sum = 0
  while (epoch <= upper_epoch)
    sum += delta[epoch]
    epoch++
  }
  return sum
}
```
<!--
## Invariants (WIP)

### From the PoS validity predicate

These are derived from the check on the accumulators that the PoS validity predicate does.

Following, some simplifications on the notation and functions that we use in the invariants.

* To avoid convoluted notation, we avoid using functions such as read_epoched_field, total_deltas_at and compute_total_from_deltas to lookup epoched data. Thus, for instance when we write `validators[validator].total_deltas[epoch]`, we really mean `total_deltas_at(validators[validator].total_deltas, epoch)`. Similarly, when we write bonds[address][validator].deltas[epoch], we really mean compute_total_from_deltas(bonds[address][validator].deltas, epoch).

* Function `total_bonds(validator, epoch)` aggregates all the bonds of a given validator at a given epoch.

```go
total_bonds(validator, epoch)
{
  var total_bonds = 0
  var addresses = {address | bonds[address][validator].deltas[epoch] > 0}
  forall (address in addresses) do
    total_bonds += bonds[address][validator].deltas[epoch]
  return total_bonds
}
```

### Invariant 1
> for any epoch, validator . `validators[validator].total_deltas[epoch] >= 0`

https://github.com/anoma/anoma/blob/master/proof_of_stake/src/validation.rs#L694-L698
https://github.com/anoma/anoma/blob/master/proof_of_stake/src/validation.rs#L763-L767

### Invariant 2
> for any validator, epoch . `validators[validator].total_deltas[epoch] == total_bonds(validator, epoch)`

https://docs.anoma.network/master/explore/design/ledger/pos-integration.html:
"For each `total_deltas`, there must be the same delta value in `bond_delta`"
https://github.com/anoma/anoma/blob/master/proof_of_stake/src/validation.rs#L1244-L1250


### Invariant 3
> for any validator, epoch . `total_bonds(validator, epoch) `
-->

<!-- 
CUBIC SLASHING
```go
end_of_epoch()
{
  slashing()
  //Manu: is there an special state for jalied validators?
  jailing() //TODO
  rewarding() //TODO
}
```

```go
slashing(){
  //for each validator
  forall (address, validator in validators) do
    //compute set of slashes from the last two epochs
    var set_slashes = {slash | slash in slashes[address] && cur_epoch-1 <= slash.epoch] }
    //compute slash rate
    var slash_rate = calculate_slash_rate(set_slashes)
    forall (slash in set_slashes) do
      var max_epoch := max{epoch | validators[address].total_deltas[epoch] != 0 && epoch <= slash.epoch}
      var slashed_amount := validators[address].total_deltas[max_epoch]*slash_rate
      //compute new total_deltas and write it at n+pipeline_length
      var total = total_deltas_at(validators[address].total_deltas, cur_epoch+pipeline_length)
      validators[address].total_deltas[cur_epoch+pipeline_length] = total - slashed_amount 
      //update validator's voting_power, total_voting_power and validator_sets at n+pipeline_length
      validators[validator_address].voting_power[cur_epoch+pipeline_length] = compute_voting_power()
      total_voting_power[cur_epoch+pipeline_length] = compute_total_voting_power(cur_epoch+pipeline_length)
      validator_sets[cur_epoch+pipeline_length] = compute_validator_sets()
}
```
```go
//Cubic slashing function
calculate_slash_rate(slashes)
{
  var voting_power_fraction = 0
  forall (slash in slashes) do
    voting_power_fraction += slash.validator.voting_power
  return max{0.01, min{1, voting_power_fraction^2 * 9}}
}
```
-->