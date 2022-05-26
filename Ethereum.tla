------------------------------ MODULE Ethereum ------------------------------

EXTENDS Integers

CONSTANTS
    AccountId, \* the set of all account identifiers
    StellarAccountId,
    Amount,
    Time

Transaction == [from : AccountId, to : AccountId, amount : Amount, memo : StellarAccountId]

VARIABLES
    executed, \* executed transactions, per block
    time \* ethereum time

Init ==
    /\  executed = [t \in Time |-> {}]
    /\  time = 0

Tick ==
    /\  time' = time + 1
    /\  UNCHANGED <<executed>>
    /\  time' \in Time

Executed == UNION {executed[t] : t \in Time}

ExecuteTx(tx) ==
    /\  \neg tx \in Executed
    /\  tx.amount >= 0
    /\  tx.from # tx.to
    /\  executed' = [executed EXCEPT ![time] = @ \union {tx}]
    /\  UNCHANGED time

TypeOkay ==
    /\  executed \in [Time -> SUBSET Transaction]
    /\  time \in Time

Inv ==
  \A tx1 \in Executed : \A t1,t2 \in Time :
      \/  t1 = t2
      \/  tx1 \in executed[t1] => \neg tx1 \in executed[t2]

=============================================================================
