------------------------- MODULE Staking ---------------------------------
(*
 * Modeling the Anoma's staking module.
 * This is a very minimal spec that includes delegate, unbond and withdraw
 *
 * Simplifications:
 *   - We assume only one validator to be delegated to.
 *   - Rewards are not specified.
 *   - Jailing is not specified.
 *   - Slashing and evidence handling is not specified.
 * 
 * Manuel Bravo, 2022
 *)
EXTENDS Integers, Apalache, Staking_typedefs

CONSTANTS
    \* Set of all user addresses.
    \* @type: Set(ADDR);
    UserAddrs,

    \* Set of all validator addresses.
    \* ValidatorAddrs must be a subset of UserAddrs
    \* @type: Set(ADDR);
    ValidatorAddrs,

    \* @type: Int;
    PipelineLength,

    \* @type: Int;
    UnbondingLength

VARIABLES
    \* Token balance for every account.
    \*
    \* @type: BALANCE;
    balanceOf,
    \* Balance of unbonded tokens that cannot be used during the bonding period.
    \*
    \* @type: EPOCHED;
    unbonded,
    \* Token that are delegated to Validator.
    \*
    \* @type: DELEGATEDEPOCHED;
    delegated,
    \* Tokens bonded at a given Validator.
    \*
    \* @type: EPOCHED;
    bonded


\* Variables that model transactions, epochs and offsets, not the state machine.
VARIABLES    
    \* The last executed transaction.
    \*
    \* @type: TX;
    lastTx,
    \* A serial number to assign unique ids to transactions
    \* @type: Int;
    nextTxId,
    \* Counts the transactions executed within an epoch
    \* @type: Int;
    txCounter,
    \* A serial number used to identify epochs
    \* @type: Int;
    epoch,
    \* Whether at least one transaction has failed
    \* @type: Bool;
    failed

\* the maximum value
MAX_UINT == 2^(256 - 60) - 1

\* 1 billion toekns in the initial supply
INITIAL_SUPPLY == 10^(9+18)

\* the number of tokens the validator has staked
INIT_VALIDATOR_STAKE == 1000000000000000000000

\* the amount of voting power per token
VOTES_PER_TOKEN == 1

\* tx per epoch
TXS_PER_EPOCH == 10

\* Initialize the balances
Init ==
    /\ balanceOf = [ a \in UserAddrs |-> 
        IF a \in ValidatorAddrs
        THEN INITIAL_SUPPLY - INIT_VALIDATOR_STAKE
        ELSE INITIAL_SUPPLY
       ]
    /\ unbonded = [ n \in 1..UnbondingLength, a \in UserAddrs |-> 0 ]
    /\ delegated = [ n \in 1..UnbondingLength, a \in UserAddrs, b \in ValidatorAddrs |->
        IF a \in ValidatorAddrs /\ a = b
        THEN INIT_VALIDATOR_STAKE
        ELSE 0
       ]
    /\ bonded = [ n \in 1..UnbondingLength, a \in ValidatorAddrs |-> INIT_VALIDATOR_STAKE ]
    /\ nextTxId = 0
    /\ epoch = 1
    /\ txCounter = 0
    /\ lastTx = [ id |-> 0, tag |-> "None", fail |-> FALSE ]
    /\ failed = FALSE


\* delegate `amount` coins to Validator
Delegate(sender, validator, amount) ==
    LET fail ==
        \/ amount < 0
        \/ amount > balanceOf[sender]
    IN
    /\ lastTx' = [ id |-> nextTxId, tag |-> "delegate", fail |-> fail,
                   sender |-> sender, toAddr |-> validator, value |-> amount ]
    /\ failed' = (fail \/ failed)
    /\  IF fail
        THEN
          UNCHANGED <<balanceOf, unbonded, delegated, bonded>>
        ELSE
          \* transaction succeeds
          \* update the balance of 'sender'
          /\ balanceOf' = [ balanceOf EXCEPT ![sender] = @ - amount]
          /\ delegated' = [ n \in 1..UnbondingLength, user \in UserAddrs, val \in ValidatorAddrs |-> 
                     IF n >= PipelineLength /\ user = sender /\ val = validator
                     THEN delegated[n, user, val] + amount
                     ELSE delegated[n, user, val]
                    ]
          /\ bonded' = [ n \in 1..UnbondingLength, user \in ValidatorAddrs |-> 
                     IF n >= PipelineLength /\ user = sender
                     THEN bonded[n, user] + amount
                     ELSE bonded[n, user]
                    ]
          /\ UNCHANGED unbonded


\* unbond `amount` tokens from Validator
Unbond(sender, validator, amount) ==
    LET fail ==
        \/ amount < 0
        \/ amount > delegated[UnbondingLength, sender, validator]
    IN
    /\ lastTx' = [ id |-> nextTxId, tag |-> "unbond", fail |-> fail,
                   sender |-> sender, toAddr |-> validator, value |-> amount ]
    /\ failed' = (fail \/ failed)
    /\  IF fail
        THEN
          UNCHANGED <<balanceOf, unbonded, delegated, bonded>>
        ELSE
          \* transaction succeeds
          /\ unbonded' = [ unbonded EXCEPT ![UnbondingLength, sender] = @ + amount ]
          /\ delegated' = [ delegated EXCEPT ![UnbondingLength, sender, validator] = @ - amount ]
          /\ bonded' = [ bonded EXCEPT ![UnbondingLength, validator] = @ - amount]
          /\ UNCHANGED  balanceOf
          

\* withdraw unbonded tokens
Withdraw(sender) ==
    LET fail ==
        \/ unbonded[1, sender] <= 0
    IN
    /\ lastTx' = [ id |-> nextTxId, tag |-> "withdraw", fail |-> fail,
                   sender |-> sender, toAddr |-> "withdraw", value |-> unbonded[1, sender] ]
    /\ failed' = (fail \/ failed)
    /\  IF fail
        THEN
          UNCHANGED <<balanceOf, unbonded, delegated, bonded>>
        ELSE
          \* transaction succeeds
          /\ balanceOf' = [ balanceOf EXCEPT ![sender] = @ + unbonded[1, sender] ]
          /\ unbonded' = [ n \in 1..UnbondingLength, user \in UserAddrs |-> 
                          IF user = sender
                          THEN unbonded[n, sender] - unbonded[1, sender]
                          ELSE unbonded[n, user]
                         ]
          /\ UNCHANGED  <<delegated, bonded>>

Common ==
    /\ nextTxId' = nextTxId + 1
    /\ txCounter' = txCounter + 1
    /\ UNCHANGED epoch

ShiftEpochoedVariables ==
    /\ unbonded' = [ n \in 1..UnbondingLength, user \in UserAddrs |-> 
                    IF n < UnbondingLength
                    THEN unbonded[n+1, user]
                    ELSE unbonded[n, user]
                   ]
    /\ delegated' = [ n \in 1..UnbondingLength, user \in UserAddrs, val \in ValidatorAddrs|-> 
                     IF n < UnbondingLength
                     THEN delegated[n+1, user, val]
                     ELSE delegated[n, user, val]
                    ]
    /\ bonded' = [ n \in 1..UnbondingLength, user \in ValidatorAddrs |-> 
                  IF n < UnbondingLength
                  THEN bonded[n+1, user]
                  ELSE bonded[n, user]
                 ]

AdvanceEpoch ==
    /\ epoch' = epoch + 1
    /\ txCounter' = 0
    /\ ShiftEpochoedVariables  
    /\ UNCHANGED <<balanceOf, lastTx, nextTxId, failed>>

Next ==
    IF txCounter = TXS_PER_EPOCH
    THEN
      \* move to the next epoch
      AdvanceEpoch
    ELSE
      \E sender \in UserAddrs:
      \E validator \in ValidatorAddrs:
      \E amount \in Int:
        /\ amount <= MAX_UINT
        /\ \/ Delegate(sender, validator, amount)
           \/ Unbond(sender, validator, amount)
           \/ Withdraw(sender)
        /\ Common

\* The transition relation assuming that no failure occurs
NextNoFail ==
    Next /\ ~failed /\ ~failed'

(* False invariants to debug the spec *)


===============================================================================