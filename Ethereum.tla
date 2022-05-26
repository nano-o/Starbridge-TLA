------------------------------ MODULE Ethereum ------------------------------

\* TODO We don't need explicit balances
\* TODO We don't need the mempool

EXTENDS Integers

CONSTANTS
    AccountId, \* the set of all account identifiers
    StellarAccountId,
    Amount,
    Time

Transaction == [from : AccountId, to : AccountId, amount : Amount, memo : StellarAccountId]

VARIABLES
    balance, \* a function mapping an account id to the account's balance
    mempool, \* pending transactions
    executed, \* executed transactions, per block
    time \* ethereum time


\* balance is a private variables
\* mempool and executed constitute the external interface of this module

Init ==
    /\  balance \in [AccountId -> Amount]
    /\  mempool = {}
    /\  executed = [t \in Time |-> {}]
    /\  time = 0

Tick ==
    /\  time' = time + 1
    /\  UNCHANGED <<balance, mempool, executed>>
    /\  time' \in Time

Executed == UNION {executed[t] : t \in Time}

ReceiveTx(tx) ==
    /\  \neg tx \in mempool \union Executed
    /\  mempool' = mempool \union {tx}
    /\  UNCHANGED <<balance, executed, time>>

ExecuteTx == \E tx \in mempool :
    /\  tx.amount >= 0
    /\  tx.from # tx.to
    /\  tx.amount <= balance[tx.from]
    /\  balance' = [balance EXCEPT ![tx.from] = @-tx.amount, ![tx.to] = @+tx.amount]
    /\  mempool' = mempool \ {tx}
    /\  executed' = [executed EXCEPT ![time] = @ \union {tx}]
    /\  UNCHANGED time
    /\  balance'[tx.to] \in Amount \* for Apalache

TypeOkay ==
    /\  balance \in [AccountId -> Amount]
    /\  mempool \in SUBSET Transaction
    /\  executed \in [Time -> SUBSET Transaction]
    /\  time \in Time

Inv ==
  \A tx1 \in mempool \cup Executed :
    /\  tx1 \in Executed => \neg tx1 \in mempool
    /\  tx1 \in mempool => \neg tx1 \in Executed
    /\  \A t1,t2 \in Time :
        \/  t1 = t2
        \/  tx1 \in executed[t1] => \neg tx1 \in executed[t2]

=============================================================================
