// -*- mode: Bluespec; -*-
/* ****************************************************************************
  This encodes the proof-of-stake system of Namada.

  Manuel Bravo, Informal Systems, 2023
**************************************************************************** */

module namada {

  import basicSpells.* from "./basicSpells"
  import manuSpells.* from "./manuSpells"

    /* ****************************************************************************
    * Data Types
    * ************************************************************************* */

    // Represent addresses as strings
    type Address = str

    // Represent epochs as integers
    type Epoch = int

    // Bond record to record the bond starting epoch
    type Bond = {
      start: Epoch,
      amount: int
    }

    // Unbond record to record when the associated bond started and the unbonding epoch
    type Unbond = {
      start: Epoch,
      end: Epoch,
      amount: int
    }

    // Slash record
    type Slash = {
      id: int,
      epoch: epoch,
      validator: Address,
      rate: int
    }

    // Delegator state
    type DelegatorState = {
      balance: int,
      bonded: Address -> Set[Bond],
      unbonded: Address -> Set[Unbond]
    }

    // Validator state
    type ValidatorState = {
      address: Address,
      stake: Epoch -> int,
      slashes: List[Slash],
      frozen: Epoch,
      totalUnbonded: Epoch -> Epoch -> int
    }

    // Proof-of-stake system state
    type PosState = {
      posAccount: int,
      slashPool: int,
      epoch: Epoch,
      counterTxs: int,
      enqueuedSlashes: Epoch -> Set[Slash],
      counterSlashes: int
    }

    // Result record returned by any of the three PoS functions: delegate, unbond and withdraw
    type ResultTx = {
      success: bool,
      delegatorState: DelegatorState,
      validatorState: ValidatorState,
      posState: PosState
    }

    /* ****************************************************************************
    * Specification Parameters
    * ************************************************************************* */

    // Max uint
    pure val MAX_UINT = 10

    // Users initial balances
    pure val INIT_BALANCE = 20

    // set of all user addresses
    pure val USERS = Set("alice", "bob")

    // set of all validator addresses
    pure val VALIDATORS = Set("alice")

    // transactions per epoch
    pure val TXS_EPOCH = 1

    // unbonding offset
    pure val UNBONDING_OFFSET = 2

    // pipeline offset
    pure val PIPELINE_OFFSET = 1

    // cubic offset
    pure val CUBIC_OFFSET = 1

    /* ****************************************************************************
    * State machine state
    * ************************************************************************* */

    // Delegator state
    var delegators: Address -> DelegatorState
    // Validator state
    var validators: Address -> ValidatorState
    // Proof-of-stake state
    var pos: PosState

    /* ****************************************************************************
    * Execution state
    * ************************************************************************* */

    // Used to limit the misbehaving of a validator: at most once within any window of unbonding offset epochs
    pure val limitEvidence = false

    // Used to guarantee every step produces a state transition
    // IMPORTANT: Set to false for tests
    pure val enforceStateTransition = true

    // Last transaction executed by step.
    // Amount is only relevant for delegate and unbond; it is alwasy 0 for withdraw.
    var lastTx: {tag: str, result: bool, user: Address, validator: Address, amount: int}

    /**************************************************************************
    * Helper functions
    * ************************************************************************* */

    pure def min(x, y) = if (x < y) x else y

    /*
    * The function addRecord adds an a record to a set of them.
    */
    pure def addRecord(setRecords, record) = setRecords.union(Set(record))

    pure def unbondBond(acc: {remainder: int, toRemove: Set[Bond], new: Bond}, bond: Bond): {remainder: int, toRemove: Set[Bond], new: Bond} = 
      val amountUnbonded = min(bond.amount, acc.remainder)
      {remainder: acc.remainder - amountUnbonded,
       toRemove: addRecord(acc.toRemove, bond),
       new: if (bond.amount > acc.remainder) {start: bond.start, amount: bond.amount - acc.remainder} else acc.new}

    pure def iterateBondsUpToAmount(bonds: Set[Bond], amount: int): {toRemove: Set[Bond], new: Bond} = {
      val result = bonds.fold({remainder: amount, toRemove: Set(), new: {start: -1, amount: 0}},
                              (acc, bond) => if (acc.remainder == 0) acc else unbondBond(acc, bond))
      {toRemove: result.toRemove, new: result.new}
    }

    pure def computeSlashableAmount(slash: Slash, initAmount: int, computedSlashes: Epoch -> int): int = {
      val updatedAmount = computedSlashes.keys().filter(x => x + UNBONDING_OFFSET < slash.epoch)
                                                .fold(initAmount, (acc, e) => acc - computedSlashes.get(e))
      updatedAmount*slash.rate
    }

    pure def applyListSlashes(listSlashes: List[Slash], amount: int): int = {

      listSlashes.foldl({finalAmount: amount, computedSlashes: Map()}, (acc, slash) => val slashAmount = computeSlashableAmount(slash, amount, acc.computedSlashes)
                                                                                       {finalAmount: acc.finalAmount - slashAmount,
                                                                                        computedSlashes: acc.map.set(slash.epoch, slashAmount)}).finalAmount
    }

    /**************************************************************************
    * Main functions
    * ************************************************************************* */


    /*
    * The function delegate is called when a user wants to delegate tokens to a validator.
    * 1. First it checks that the user has enough tokens in its account.
    * 2. Then it locks those tokens by transferring then from the user's account to the PoS special account.
    * 3. It records that the user has delegated amount tokens to the validator.
    * 4. It increases the validator's stake.
    */
    pure def delegate(delegatorState: DelegatorState, validatorState: ValidatorState, posState: PosState, amount: int): ResultTx = {
      if (amount <= delegatorState.balance) {
        val updatedDelegatorState = delegatorState.with("balance", delegatorState.balance - amount)
                                                  .with("bonded", delegatorState.bonded.set(validatorState.address,
                                                                                            addRecord(delegatorState.bonded.get(validatorState.address),
                                                                                                      {start: posState.epoch + PIPELINE_OFFSET, amount: amount})))
        val updatedValidatorState = validatorState.with("stake", validatorState.stake.set(posState.epoch + PIPELINE_OFFSET,
                                                                                          validatorState.stake.get(posState.epoch + PIPELINE_OFFSET) + amount))
        val updatedPosState = posState.with("posAccount", posState.posAccount + amount)
        {success: true, delegatorState: updatedDelegatorState, validatorState: updatedValidatorState, posState: updatedPosState}
      } else {
        {success: false, delegatorState: delegatorState, validatorState: validatorState, posState: posState}
      }
    }

    /*
    * The function unbond is called when a user wants to unbond tokens from a validator.
    * 1. First it checks that the user has enough tokens bonded to the validator.
    * 2. Then it records that amount of tokens is unbonded by subtracting amount from bonded and adding to unbonded.
    * 3. Finally, it decreases the validator's stake.
    */
    pure def unbond(delegatorState: DelegatorState, validatorState: ValidatorState, posState: PosState, amount: int): ResultTx = {
      val totalBonded = delegatorState.bonded.get(validatorState.address).fold(0, (sum, elem) => sum + elem.amount)      
      if (amount < totalBonded and validatorState.frozen < posState.epoch) {
        val endEpoch = posState.epoch + PIPELINE_OFFSET + UNBONDING_OFFSET
        val resultUnbonding = iterateBondsUpToAmount(delegatorState.bonded.get(validatorState.address), amount)
        val newUnbonds = resultUnbonding.toRemove.map(bond => if (bond.start == resultUnbonding.new.start) {start: bond.start, end: endEpoch, amount: bond.amount -  resultUnbonding.new.amount}
                                                              else {start: bond.start, end: endEpoch, amount: bond.amount})
        val updatedBonded = delegatorState.bonded.set(validatorState.address,
                                                      if (resultUnbonding.new.start == -1) delegatorState.bonded.get(validatorState.address).exclude(resultUnbonding.toRemove)
                                                      else delegatorState.bonded.get(validatorState.address).exclude(resultUnbonding.toRemove).union(Set(resultUnbonding.new)))                                                         
        val updatedDelegatorState = delegatorState.with("bonded", updatedBonded)
                                                  .with("unbonded", delegatorState.unbonded.set(validatorState.address, delegatorState.unbonded.get(validatorState.address).union(newUnbonds)))                                  
        val amountAfterSlashing = newUnbonds.fold(0, (sum, element) => val listSlashes = validatorState.slashes.select(slash => element.start <= slash.epoch)
                                                                       sum + applyListSlashes(listSlashes, element.amount))
        val updatedTotalUnbonded = newUnbonds.fold(validatorState.totalUnbonded.get(posState.epoch),
                                                   (acc, element) => acc.safeSet(element.start, acc.getOrElse(element.start, 0) + element.amount))
        val updatedValidatorState = validatorState.with("stake", validatorState.stake.set(posState.epoch + PIPELINE_OFFSET,
                                                                                          validatorState.stake.get(posState.epoch + PIPELINE_OFFSET) - amountAfterSlashing))
                                                  .with("totalUnbonded", validatorState.totalUnbonded.set(posState.epoch + PIPELINE_OFFSET, updatedTotalUnbonded))
        {success: true, delegatorState: updatedDelegatorState, validatorState: updatedValidatorState, posState: posState}
      } else {
        {success: false, delegatorState: delegatorState, validatorState: validatorState, posState: posState}
      }
    }

    /*
    * The function withdraw is called when a user wants to withdraw tokens from a validator.
    * 1. First it computes the amount of tokens that can be withdrawn and returns an error in case there are none.
    * 2. Then records that those tokens are withdrawn by removing the withdrawable unbond records from unbonded.
    * 3. Finally, it unlocks the tokens by transferring them from the PoS special account to the user's account.
    */
    pure def withdraw(delegatorState: DelegatorState, validatorState: ValidatorState, posState: PosState): ResultTx = {
      // Filter the the set of unbonds that can be withdrawn
      val setWithdrawn = delegatorState.unbonded.get(validatorState.address).filter(element => element.end <= posState.epoch)
      // Compute the total amount of withdrawable tokens
      val amount = setWithdrawn.fold(0, (sum, element) => sum + element.amount)
      if (amount > 0) {
        // Compute how much out of amount is withdrawn after slashing by leveraging applyListSlashes
        val amountAfterSlashing = setWithdrawn.fold(0, (sum, element) => val listSlashes = validatorState.slashes.select(slash => element.start <= slash.epoch and
                                                                                                                                  element.end > slash.epoch)
                                                                         sum + applyListSlashes(listSlashes, element.amount))
        // Remove the sent of withdrawn unbonds from the set of unbonds
        val updatedUnbonded = delegatorState.unbonded.get(validatorState.address).exclude(setWithdrawn)
        // Transfer withdrawn tokens from the PoS account to the user's account
        val updatedDelegatorState = delegatorState.with("unbonded", delegatorState.unbonded.set(validatorState.address, updatedUnbonded))
                                                  .with("balance", delegatorState.balance + amountAfterSlashing)
        val updatedPosState = posState.with("posAccount", posState.posAccount - amountAfterSlashing)
        {success: true, delegatorState: updatedDelegatorState, validatorState: validatorState, posState: updatedPosState}
      } else {
        {success: false, delegatorState: delegatorState, validatorState: validatorState, posState: posState}
      }
    }

    pure def computeTotalUnbonded(slash: Slash, prevSlashes: List[Slash], totalUnbonded: Epoch -> int): int = {
      val epochs = totalUnbonded.keys().filter(e => e <= slash.epoch and totalUnbonded.get(e) > 0)
      epochs.fold(0, (sum, e) => sum + applyListSlashes(prevSlashes.select(s => e <= s.epoch and s.epoch + UNBONDING_OFFSET < slash.epoch), totalUnbonded.get(e)))
    }

    pure def slashValidator(initMap: Epoch -> int, curEpoch: Epoch, stake: int, slash: Slash, prevSlashes: List[Slash], totalUnbonded: Epoch -> Epoch -> int, finalRate: int): Epoch -> int = {
      val initTotalUnbonded = slash.epoch.to(curEpoch).fold(0, (sum, e) => sum + computeTotalUnbonded(slash, prevSlashes, totalUnbonded.get(e)))
      val result = (curEpoch+1).to(curEpoch+PIPELINE_OFFSET).fold((initTotalUnbonded, initMap), (acc, e) => val updatedTotalUnbonded = acc._1 + computeTotalUnbonded(slash, prevSlashes, totalUnbonded.get(e))
                                                                                                            val slashedAmount = (stake - updatedTotalUnbonded) * finalRate
                                                                                                            (updatedTotalUnbonded, acc._2.set(e, acc._2.get(e) + slashedAmount)))
      result._2
    }

    pure def computeFinalRate(setSlashes: Set[Slash]): int = {
      1
    } 

    pure def endOfEpoch(validatorsState: Address -> ValidatorState, posState: PosState, curEpoch: Epoch): {validatorsState: Address -> ValidatorState, posState: PosState} = {
      val finalRate = computeFinalRate(posState.enqueuedSlashes.get(curEpoch-1).union(posState.enqueuedSlashes.get(curEpoch))
                                                                               .union(posState.enqueuedSlashes.get(curEpoch+1)))
      val initMap = VALIDATORS.mapBy(v => (curEpoch+1).to(curEpoch+PIPELINE_OFFSET).mapBy(e => 0))
      val mapValidatorSlash = posState.enqueuedSlashes.get(curEpoch).fold(initMap, (acc, slash) => acc.set(slash.validator, slashValidator(acc.get(slash.validator),
                                                                                                                                           curEpoch,
                                                                                                                                           validatorsState.get(slash.validator).stake.get(slash.epoch),
                                                                                                                                           slash,
                                                                                                                                           validatorsState.get(slash.validator).slashes,
                                                                                                                                           validatorsState.get(slash.validator).totalUnbonded,
                                                                                                                                           finalRate)))
      val updatedValidators = VALIDATORS.mapBy(v => validatorsState.get(v).with("stake",(curEpoch-UNBONDING_OFFSET+1).to(curEpoch+1+PIPELINE_OFFSET).mapBy(e => if (e < curEpoch+1+PIPELINE_OFFSET) validatorsState.get(v).stake.get(e) -
                                                                                                                                                                  if (e >= curEpoch+1) mapValidatorSlash.get(v).get(e) else 0
                                                                                                                                                                else validatorsState.get(v).stake.get(e-1) - mapValidatorSlash.get(v).get(e-1))) 
                                                                         .with("totalUnbonded", (curEpoch+1).to(curEpoch+1+PIPELINE_OFFSET).mapBy(e => if (e < curEpoch+1+PIPELINE_OFFSET) validatorsState.get(v).totalUnbonded.get(e)
                                                                                                                                                       else Map()))
                                                                         .with("slashes", posState.enqueuedSlashes.get(curEpoch).filter(s => s.validator == v).fold(validatorsState.get(v).slashes, (acc, s) => acc.append(s.with("rate", finalRate)))))                                                                            
      val updatedPos =  posState.with("epoch", curEpoch + 1)
                                .with("counterTxs", 0)
                                .with("slashPool", posState.enqueuedSlashes.get(curEpoch).fold(0, (sum, s) => sum + validatorsState.get(s.validator).stake.get(s.epoch)*finalRate))
                                .with("enqueuedSlashes", (curEpoch).to(curEpoch+1+UNBONDING_OFFSET).mapBy(e => if (e < curEpoch+1+UNBONDING_OFFSET) posState.enqueuedSlashes.get(e)
                                                                                                                 else Set()))                                                                      
      {validatorsState: updatedValidators, posState: updatedPos}                                                                                                                             
    }

    pure def proccessEvidence(e: Epoch, validatorState: ValidatorState, posState: PosState): {validatorState: ValidatorState, posState: PosState} = {
      val nextSlashCounter = posState.counterSlashes + 1
      val slash = {id: posState.counterSlashes + 1, epoch: e, validator: validatorState.address, rate: 1}
      {validatorState: validatorState.with("frozen", max(validatorState.frozen, e + UNBONDING_OFFSET)),
       posState: posState.with("counterSlashes", posState.counterSlashes + 1)
                         .with("enqueuedSlashes", posState.enqueuedSlashes.set(e + UNBONDING_OFFSET, posState.enqueuedSlashes.get(e + UNBONDING_OFFSET).union(Set(slash))))}
    }


    /* ****************************************************************************
    * Actions
    * ************************************************************************* */

    /*
    * The action commonTxAfter is called after a transaction is executed.
    * 1. It first checks if it is the last transaction of the current epoch.
    * 2. If it is the last transaction of the epoch, it calls the endOfEpoch.
    * 3. Otherwise, it updates the variables using the result of the transaciton.
    */

    action commonTxAfter(user: Address, validator: Address, result: ResultTx): bool = all {
      if (pos.counterTxs + 1 == TXS_EPOCH) {
        val resultEndOfEpoch = endOfEpoch(validators.set(validator, result.validatorState), result.posState, pos.epoch)
        all {
          delegators' = delegators.set(user, result.delegatorState),
          validators' = resultEndOfEpoch.validatorsState,
          pos' = resultEndOfEpoch.posState,
        }
      } else {
        all {
          delegators' = delegators.set(user, result.delegatorState),
          validators' = validators.set(validator, result.validatorState),
          pos' = result.posState.with("counterTxs", result.posState.counterTxs + 1)
        }
      }
    }

    action actionDelegate(user: Address, validator: Address, amount: int): bool = all {
      val result = delegate(delegators.get(user), validators.get(validator), pos, amount)
      all {
        if (enforceStateTransition) require(result.success) else true,
        commonTxAfter(user, validator, result),
        lastTx' = {tag: "Delegate", result: result.success, user: user, validator: validator, amount: amount}
      }
    }

    action actionUnbond(user: Address, validator: Address, amount: int): bool = all {
      val result = unbond(delegators.get(user), validators.get(validator), pos, amount)
      all {
        if (enforceStateTransition) require(result.success) else true,
        commonTxAfter(user, validator, result),
        lastTx' = {tag: "Unbond", result: result.success, user: user, validator: validator, amount: amount}
      }
    }

    action actionWithdraw(user: Address, validator: Address): bool = all {
      val result = withdraw(delegators.get(user), validators.get(validator), pos)
      all {
        if (enforceStateTransition) require(result.success) else true,
        commonTxAfter(user, validator, result),
        lastTx' = {tag: "Withdraw", result: result.success, user: user, validator: validator, amount: 0}
      }
    }

    action actionEvidence(e: Epoch, validator: Address): bool = all {
      if (limitEvidence) require(validators.get(validator).frozen < e) else true,
      val result = proccessEvidence(e, validators.get(validator), pos)
      all {
        validators' = validators.set(validator, result.validatorState),
        pos' = result.posState,
        delegators' = delegators,
        lastTx' = {tag: "Evidence", result: true, user: "", validator: validator, amount: e}
      }
    }

    /* ****************************************************************************
    * Invariants
    * ************************************************************************* */

    // Invariant 1: The total amount of tokens is constant.
    val totalAmountTokensConstant = USERS.fold(0, (sum, user) => sum + delegators.get(user).balance) + pos.posAccount + pos.slashPool== size(USERS)*INIT_BALANCE

    // Invariant 2: A delegator's balance cannot become negative.
    val balanceGreaterZero = USERS.forall(user => delegators.get(user).balance >= 0)

    // Invariant 3: A validator's stake cannot become negative.
    val stakeGreaterZero = VALIDATORS.forall(validator =>
                                             pos.epoch.to(pos.epoch + PIPELINE_OFFSET).forall(e => validators.get(validator).stake.get(e) >= 0))

    // Invariant 4: The PoS account cannot become negative.
    val posAccountGreaterZero = pos.posAccount >= 0

    // Invariant 5: The validator's stake is the sum of its delegations.
    val stakeEqualSumBonds = VALIDATORS.forall(validator => USERS.fold(0, (sum, user) => 
                                                                           sum + delegators.get(user).bonded.get(validator).fold(0, (total, elem) =>
                                                                                                                                     total + elem.amount) ) == validators.get(validator).stake.get(pos.epoch + PIPELINE_OFFSET))

    //Invarriant 6: The user's balance cannot become greater than the initial balance
    val boundedBalance = USERS.forall(user => delegators.get(user).balance <= INIT_BALANCE)

    // All invariants
    val allInvariants = totalAmountTokensConstant and
                        balanceGreaterZero and
                        stakeGreaterZero and
                        posAccountGreaterZero and
                        //stakeEqualSumBonds and
                        boundedBalance
    
    /* ****************************************************************************
    * Execution
    * ************************************************************************* */

    action allUnchanged: bool = all {
      delegators' = delegators,
      validators' = validators,
      pos' = pos,
      lastTx' = lastTx
    }

    // State initialization: assumes that users start with some initial balance.
    action init: bool = all {
      val initEpoch = UNBONDING_OFFSET
      all {
        delegators' = USERS.mapBy(user => {balance: INIT_BALANCE,
                                          bonded: VALIDATORS.mapBy(x => Set()),
                                          unbonded: VALIDATORS.mapBy(x => Set())}),
        validators' = VALIDATORS.mapBy(validator => {address: validator,
                                                     stake: 0.to(initEpoch+PIPELINE_OFFSET).mapBy(e => 0),
                                                     totalUnbonded: initEpoch.to(initEpoch+PIPELINE_OFFSET).mapBy(e => Map()),
                                                     slashes: List(),
                                                     frozen: 0}),
        pos' = {posAccount: 0,
                slashPool: 0,
                epoch: initEpoch,
                counterTxs: 0,
                enqueuedSlashes: (initEpoch-1).to(initEpoch+UNBONDING_OFFSET).mapBy(e => Set()),
                counterSlashes: 0},
        lastTx' = { tag: "Init", result: true, user: "", validator: "", amount: 0}
      }
    }

    /*
    * Execution of the state machine.
    * 1. Pick a random amount from 0 to MAX_UINT, a user and a validator
    * 2. Execute one of the actions: delegate, unbond or withdraw.
    */
    action step: bool = {
        nondet user = USERS.oneOf()
        nondet validator = VALIDATORS.oneOf()
        nondet amount = 1.to(MAX_UINT).oneOf()
        nondet e = (pos.epoch - UNBONDING_OFFSET).to(pos.epoch).oneOf()
        // Execute one of the available actions/methods
        any {
            actionEvidence(e, validator),
            actionDelegate(user, validator, amount),
            actionUnbond(user, validator, amount),
            actionWithdraw(user, validator)
        }
    }

    /*
    * The test testDelegate is a unitest-like test for the delegate function.
    */
    run delegateTest = {
      val delegatorState = {balance: INIT_BALANCE, bonded: USERS.mapBy(x => Set()), unbonded: USERS.mapBy(x => Set())}
      val validatorState = {address: "alice",
                            stake: 0.to(UNBONDING_OFFSET).mapBy(e => 0),
                            totalUnbonded: 1.to(1+PIPELINE_OFFSET).mapBy(e => Map()),
                            slashes: List(),
                            frozen: 0}
      val posState = {posAccount: 0,
                      slashPool: 0,
                      epoch: 1,
                      counterTxs: 0,
                      enqueuedSlashes: 0.to(UNBONDING_OFFSET).mapBy(e => Set()),
                      counterSlashes: 0}
      nondet amount = 0.to(MAX_UINT).oneOf()
      val result = delegate(delegatorState, validatorState, posState, amount)
      if (result.success) {
        all {
          assert(result.delegatorState.balance == INIT_BALANCE - amount),
          assert(result.delegatorState.bonded.get(validatorState.address).contains({start: 1 + PIPELINE_OFFSET, amount: amount})),
          assert(result.delegatorState.unbonded.get(validatorState.address) == Set()),
          assert(result.validatorState.stake.get(1 + PIPELINE_OFFSET) == amount),
          assert(result.posState.posAccount == amount)
        }
      } else {
        all {
          assert(amount > INIT_BALANCE),
          assert(result.delegatorState == delegatorState),
          assert(result.validatorState == validatorState),
          assert(result.posState == posState)
        }
      }
    }

    /*
    * The test testUnbondingPeriod checks that the unbonding period is enforced.
    */
    run successfulWithdrawTest = {
      nondet user = USERS.oneOf()
      nondet validator = VALIDATORS.oneOf()
      all {
        init
        .then(actionDelegate(user, validator, 10))
        .then(actionUnbond(user, validator, 5))
        .then(actionDelegate(user, validator, 1))
        .then(actionDelegate(user, validator, 1))
        .then(actionDelegate(user, validator, 1))
        .then(actionWithdraw(user, validator))
        .then(all{ assert(delegators.get(user).balance == 12), allUnchanged})
        
      }
    }

    /*
    * The test testUnbondingPeriod checks that the unbonding period is enforced.
    */
    run unbondingPeriodTest = {
      nondet user = USERS.oneOf()
      nondet validator = VALIDATORS.oneOf()
      all {
        init
        .then(actionDelegate(user, validator, 8))
        .then(actionUnbond(user, validator, 5))
        .then(actionWithdraw(user, validator))
        .then(all{ assert(delegators.get(user).balance == 12), allUnchanged})
      }
    }
}