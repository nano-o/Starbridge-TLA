------------------------------ MODULE Stellar ------------------------------

EXTENDS Integers

CONSTANTS
    AccountId, \* the set of all account identifiers
    Amount,
    SeqNum,
    Time

Transaction == [from : AccountId, to : AccountId, amount : Amount, seq : SeqNum, maxTime : Time]

VARIABLES
    balance, \* a function mapping an account id to the account's balance
    seqNum, \* a function mapping an account id to the account's sequence number
    time, \* last ledger close time
    mempool, \* pending mempool; that's the interface to the outer world
    executed \* executed transactions

\* balance is a private variable
\* mempool, executed, time, and seqNum are interface variables

Init ==
    /\  balance = [a \in AccountId |-> 0]
    /\  seqNum = [a \in AccountId |-> 0]
    /\  time = 0
    /\  mempool = {}
    /\  executed = {}

Tick  ==
    /\  time' = time + 1
    /\  UNCHANGED <<balance, seqNum, mempool, executed>>
    /\  time' \in Time

ReceiveTx(tx) ==
    /\  mempool' = mempool \union {tx}
    /\  UNCHANGED <<time, balance, seqNum, executed>>

ExecuteTx == \E tx \in mempool :
    /\  tx.seq = seqNum[tx.from]
    /\  tx.maxTime <= time
    /\  tx.amount >= 0
    /\  tx.from # tx.to
    /\  tx.amount <= balance[tx.from]
    /\  seqNum' = [seqNum EXCEPT ![tx.from] = @+1]
    /\  balance' = [balance EXCEPT ![tx.from] = @-tx.amount, ![tx.to] = @+tx.amount]
    /\  mempool' = mempool \ {tx}
    /\  executed' = executed \union {tx}
    /\  UNCHANGED time
    /\  balance'[tx.to] \in Amount
    /\  seqNum'[tx.from] \in SeqNum

TypeOkay ==
    /\  balance \in [AccountId -> Amount]
    /\  seqNum \in [AccountId -> SeqNum]
    /\  time \in Time
    /\  time >= 0
    /\  mempool \in SUBSET Transaction
    /\  executed \in SUBSET Transaction

=============================================================================
