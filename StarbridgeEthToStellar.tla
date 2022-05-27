------------------------------ MODULE StarbridgeEthToStellar ------------------------------

EXTENDS Integers, Apalache

\* @typeAlias: STELLAR_TX = [src : STELLAR_ACCNT, from : STELLAR_ACCNT, to : STELLAR_ACCNT, amount : Int, seq : Int, maxTime : Int, depositId : HASH];
\* @typeAlias: ETH_TX = [from : ETH_ACCNT, to : ETH_ACCNT, amount : Int, stellarDst : STELLAR_ACCNT, hash : HASH, depositId : HASH];

CONSTANTS
  StellarAccountId,
  EthereumAccountId,
  Amount,
  SeqNum,
  Time,
  WithdrawWindow, \* time window the user has to execute a withdraw operation on Stellar
  Hash,
  BridgeStellarAccountId,
  BridgeEthereumAccountId

VARIABLES
    \* state of Stellar and Ethereum:
    \* @type: STELLAR_ACCNT -> Int;
    stellarSeqNum,
    \* @type: Int;
    stellarTime,
    \* @type: Set(STELLAR_TX);
    stellarMempool,
    \* @type: Set(STELLAR_TX);
    stellarExecuted,
    \* @type: Int -> Set(ETH_TX);
    ethereumExecuted,
    \* @type: Int;
    ethereumTime,

    \* state of the bridge:
    \* @type: Set(HASH);
    issuedWithdrawTx,
    \* @type: HASH -> STELLAR_TX;
    lastWithdrawTx, \* NOTE: this could be a partial function to avoid needing the variable above, but it's bad for Apalache's SMT encoding
    \* @type: Int;
    bridgeStellarTime,
    \* @type: STELLAR_ACCNT -> Int;
    bridgeStellarSeqNum,
    \* @type: Set(STELLAR_TX);
    bridgeStellarExecuted,
    \* @type: Set(HASH);
    refunded

ethereumVars == <<ethereumExecuted, ethereumTime>>
stellarVars == <<stellarSeqNum, stellarTime, stellarMempool, stellarExecuted>>
bridgeVars == <<issuedWithdrawTx, lastWithdrawTx, bridgeStellarTime, bridgeStellarSeqNum, bridgeStellarExecuted, refunded>>
bridgeChainsStateVars == <<bridgeStellarTime, bridgeStellarSeqNum, bridgeStellarExecuted>>

Stellar == INSTANCE Stellar WITH
    AccountId <- StellarAccountId,
    BridgeAccountId <- BridgeStellarAccountId,
    seqNum <- stellarSeqNum,
    time <- stellarTime,
    mempool <- stellarMempool,
    executed <- stellarExecuted

Ethereum == INSTANCE Ethereum WITH
    AccountId <- EthereumAccountId,
    executed <- ethereumExecuted,
    time <- ethereumTime

Init ==
    /\  issuedWithdrawTx = {}
    /\  lastWithdrawTx \in [Hash -> Stellar!Transaction]
    /\  bridgeStellarTime = 0
    /\  bridgeStellarSeqNum = [a \in StellarAccountId |-> 0]
    /\  bridgeStellarExecuted = {}
    /\  refunded = {}
    /\  Stellar!Init /\ Ethereum!Init

TypeOkay ==
    /\  issuedWithdrawTx \in SUBSET Hash
    /\  lastWithdrawTx \in [Hash -> Stellar!Transaction]
    /\  bridgeStellarTime \in Time
    /\  bridgeStellarSeqNum \in [StellarAccountId -> SeqNum]
    /\  bridgeStellarExecuted \in SUBSET Stellar!Transaction
    /\  refunded \in SUBSET Hash
    /\  Stellar!TypeOkay /\ Ethereum!TypeOkay

SyncWithStellar ==
    /\  bridgeStellarTime' = stellarTime
    /\  bridgeStellarSeqNum' = stellarSeqNum
    /\  bridgeStellarExecuted' = stellarExecuted
    /\  UNCHANGED <<ethereumVars, stellarVars, issuedWithdrawTx, lastWithdrawTx, refunded>>

\* A withdraw transaction is irrevocably invalid when its time bound has ellapsed or the sequence number of the receiving account is higher than the transaction's sequence number
\* Note that this is computed according to the bridge's last snapshot of the Stellar state (which might be stale).
\* @type: (STELLAR_TX) => Bool;
IrrevocablyInvalid(tx) ==
  \/  tx.maxTime < bridgeStellarTime
  \/  tx.seq < bridgeStellarSeqNum[tx.src]

\* timestamp of a transaction on Ethereum as seen by the bridge
TxTime(tx) == CHOOSE t \in Time : tx \in ethereumExecuted[t]

\* The bridge signs a new withdraw transaction when:
\* It never did so before for the same hash,
\* or the previous withdraw transaction is irrevocably invalid and the withdraw transaction has not been executed.
\* The transaction has a time bound set to WithdrawWindow ahead of the current time.
\* But what is the current time?
\* Initially it can be the time of the tx as recorded on ethereum, but what is it afterwards?
\* For now, we use previousTx.maxTime+WithdrawWindow
EmitWithdrawTransaction == \E tx \in Ethereum!Executed :
  /\  tx.to = BridgeEthereumAccountId
  /\  tx.hash \notin refunded
  /\  tx.hash \in issuedWithdrawTx
      => LET withdrawTx == lastWithdrawTx[tx.hash] IN
           /\ withdrawTx \notin bridgeStellarExecuted
           /\ IrrevocablyInvalid(withdrawTx)
  /\ \E seqNum \in SeqNum  : \* chosen by the client
      LET timeBound ==
            IF tx.hash \notin issuedWithdrawTx
              THEN TxTime(tx)+WithdrawWindow
              ELSE lastWithdrawTx[tx.hash].maxTime+WithdrawWindow
          withdrawTx == [
            src |-> tx.stellarDst,
            from |-> BridgeStellarAccountId,
            to |-> tx.stellarDst,
            amount |-> tx.amount,
            seq |-> seqNum,
            maxTime |-> timeBound,
            depositId |-> tx.hash]
      IN
        /\ timeBound \in Time \* for the model-checker
        /\ Stellar!ReceiveTx(withdrawTx)
        /\ issuedWithdrawTx' = issuedWithdrawTx \union {tx.hash}
        /\ lastWithdrawTx' = [lastWithdrawTx EXCEPT ![tx.hash] = withdrawTx]
  /\  UNCHANGED <<ethereumVars, bridgeChainsStateVars, refunded>>

\* @type: (ETH_TX, HASH) => ETH_TX;
RefundTx(tx, hash) == [
  from |-> BridgeEthereumAccountId,
  to |-> tx.from,
  amount |-> tx.amount,
  stellarDst |-> tx.stellarDst,
  depositId |-> tx.hash,
  hash |-> hash ]

RefundDeposit == \E tx \in Ethereum!Executed :
  /\  tx.to = BridgeEthereumAccountId
  /\  tx.hash \notin refunded
  /\  tx.hash \in issuedWithdrawTx =>
        LET withdrawTx == lastWithdrawTx[tx.hash] IN
          /\  withdrawTx \notin bridgeStellarExecuted
          /\  IrrevocablyInvalid(withdrawTx)
  /\  \E hash \in Hash : Ethereum!ExecuteTx(RefundTx(tx, hash))
  /\  refunded' = refunded \union {tx.hash}
  /\  UNCHANGED <<stellarVars, issuedWithdrawTx, lastWithdrawTx, bridgeChainsStateVars>>

ReceiveDeposit ==
  \* a client makes a deposit on Ethereum:
  /\ UNCHANGED <<stellarVars, bridgeVars>>
  /\ \E src \in EthereumAccountId \ {BridgeEthereumAccountId},
          x \in Amount \ {0}, dst \in StellarAccountId \ {BridgeStellarAccountId},
        hash \in Hash :
       LET tx == [
          from |-> src,
          to |-> BridgeEthereumAccountId,
          amount |-> x,
          stellarDst |-> dst,
          hash |-> hash,
          depositId |-> hash ] \* depositId does not matter here
       IN  Ethereum!ExecuteTx(tx)

Next ==
    \/  SyncWithStellar
    \/  ReceiveDeposit
    \/  EmitWithdrawTransaction
    \/  RefundDeposit
    \/ \* internal stellar transitions:
      /\ UNCHANGED <<ethereumVars, bridgeVars>>
      /\ \/  Stellar!Tick
         \/  Stellar!ExecuteTx
         \/  Stellar!BumpSeqNum
    \/ \* internal ethereum transitions:
      /\ UNCHANGED <<stellarVars, bridgeVars>>
      /\ Ethereum!Tick

\* uniqueness of hashes:
Inv0 == Ethereum!Inv
Inv0_ == TypeOkay /\ Inv0

\* time and sequence numbers are monotonic:
Inv1 ==
  /\  bridgeStellarTime <= stellarTime
  /\  \A a \in StellarAccountId : bridgeStellarSeqNum[a] <= stellarSeqNum[a]
Inv1_ == TypeOkay /\ Inv1

\* properties of withdraw transactions:
Inv2 == \A tx \in stellarMempool \union stellarExecuted :
  tx.from = BridgeStellarAccountId => \* it's a withdraw
    \* the withdraw has been recorded by the bridge:
    /\  tx.depositId \in issuedWithdrawTx
    \* the withdraw has a corresponding deposit transaction:
    /\ \E ethTx \in Ethereum!Executed:
      /\ ethTx.hash = tx.depositId
      /\ ethTx.to = BridgeEthereumAccountId
      /\ ethTx.amount = tx.amount
    \* if it's not the last issued withdrawal for a given hash, then it is irrevocably invalid and not executed:
    /\ \/ tx = lastWithdrawTx[tx.depositId]
       \/ IrrevocablyInvalid(tx) /\ tx \notin stellarExecuted
Inv2_ == TypeOkay /\ Inv2 /\ Inv1

\* properties of refund transactions:
Inv3 == \A refund \in Ethereum!Executed :
  refund.from = BridgeEthereumAccountId => \* if it's a refund:
    \* the refund is recorded by the bridge:
    /\ refund.depositId \in refunded
    \* the refund has a corresponding initiating transaction:
    /\ \E tx \in Ethereum!Executed :
        /\ tx.hash = refund.depositId
        /\ tx.to = BridgeEthereumAccountId
        /\ tx.amount = refund.amount
    \* and no two refunds are for the same transfer:
    /\ \A refund2 \in Ethereum!Executed :
      refund2.from = BridgeEthereumAccountId /\ refund.depositId = refund2.depositId
        => refund = refund2
Inv3_ == TypeOkay /\ Inv0 /\ Inv3

\* if a transaction is irrevocably invalid according to the bridge's snapshot of the Stellar state and it has been executed on Stellar , then it also has been executed according to the bridge's snapshot.
Inv4 == \A tx \in stellarExecuted :
  /\ tx.seq < stellarSeqNum[tx.src]
  /\ IrrevocablyInvalid(tx) => tx \in bridgeStellarExecuted
Inv4_ == TypeOkay /\ Inv1 /\ Inv4

\* a refunded withdraw transaction that sits in the mempool is invalid:
Inv6 == \A tx \in stellarMempool :
  /\ tx.from = BridgeStellarAccountId \* it's a withdraw
  /\ tx.depositId \in refunded \* it's been refunded
  => IrrevocablyInvalid(tx)
Inv6_ == TypeOkay /\ Inv1 /\ Inv2 /\ Inv6

\* an executed withdrawal cannot be refunded:
Inv7 == \A tx \in stellarExecuted :
  tx.from = BridgeStellarAccountId => \* it's a withdraw
    tx.depositId \notin refunded
Inv7_ == TypeOkay /\ Inv1 /\ Inv2 /\ Inv4 /\ Inv6 /\ Inv7

WithdrawTxs ==
  LET
    \* @type: Set(STELLAR_TX);
    all == { lastWithdrawTx[h] : h \in Hash }
  IN
    {tx \in all : tx.depositId \in issuedWithdrawTx}

\* there's at most one executed withdrawal per transfer:
Inv8 == \A tx1 \in stellarExecuted :
  /\ tx1.from = BridgeStellarAccountId => tx1 = lastWithdrawTx[tx1.depositId]
  /\ \A tx2 \in stellarExecuted :
    tx1.from = BridgeStellarAccountId /\ tx2.from = BridgeStellarAccountId =>
      tx1 = tx2 \/ tx1.depositId # tx2.depositId
Inv8_ == TypeOkay /\ Inv1 /\ Inv2 /\ Inv8

EthBridgeBalance == \* funds sent to the bridge on Ethereum minus refunds
  LET
    \* @type: (Int, ETH_TX) => Int;
    Step(n, tx) ==
      CASE
            tx.to = BridgeEthereumAccountId -> n + tx.amount
        []  tx.from = BridgeEthereumAccountId -> n - tx.amount
        []  OTHER -> n
  IN
    ApaFoldSet(Step, 0, Ethereum!Executed)

StellarWithdrawals ==
  LET
    \* @type: (Int, STELLAR_TX) => Int;
    Step(n, tx) ==
      IF tx.from = BridgeStellarAccountId
      THEN n + tx.amount
      ELSE n
  IN
    ApaFoldSet(Step, 0, stellarExecuted)

\* Funds deposited in the bridge account always exceed or are equal to the funds taken out.
\* Unfortunately this is too hard to check for Apalache.
MainInvariant ==
  /\ EthBridgeBalance - StellarWithdrawals >= 0
MainInvariant_ == \* check MainInvariant_ => MainInvariant
  TypeOkay /\ Inv0 /\ Inv1 /\ Inv2 /\ Inv3 /\ Inv4 /\ Inv6 /\ Inv7 /\ Inv8 /\ MainInvariant
MainInvariant__ == \* check MainInvariant__ => MainInvariant
  TypeOkay /\ Inv0 /\ Inv1 /\ Inv2 /\ Inv3 /\ Inv4 /\ Inv6 /\ Inv7 /\ Inv8

\* Instead we'll check the following two properties:
\* Every withdraw and refund has a matching deposit.
\* Every deposit has at most one matching withdraw or refund.

\* Every withdraw and refund has a matching deposit.
Inv9 ==
  /\ \A tx \in stellarExecuted : tx.from = BridgeStellarAccountId =>
    /\ \E ethTx \in Ethereum!Executed:
          /\ ethTx.hash = tx.depositId
          /\ ethTx.to = BridgeEthereumAccountId
          /\ ethTx.amount = tx.amount
  /\ \A tx \in Ethereum!Executed : tx.from = BridgeEthereumAccountId =>
    /\ \E tx2 \in Ethereum!Executed :
        /\ tx2.hash = tx.depositId
        /\ tx2.to = BridgeEthereumAccountId
        /\ tx2.amount = tx.amount
      => tx = tx2
Inv9_ ==
  TypeOkay /\ Inv9 /\ Inv1 /\ Inv2 /\ Inv3 /\ Inv4
Inv9__ == \* we have Inv9__ => Inv9
  TypeOkay /\ Inv1 /\ Inv2 /\ Inv3 /\ Inv4

\* Every deposit has at most one matching withdraw or refund.
Inv10 ==
  /\ \A stellarTx \in stellarExecuted, ethTx \in Ethereum!Executed :
    /\ stellarTx.from = BridgeStellarAccountId
    /\ ethTx.from = BridgeEthereumAccountId
    => stellarTx.depositId # ethTx.depositId
  /\ \A tx,tx2 \in stellarExecuted :
    /\ tx.from = BridgeStellarAccountId
    /\ tx2.from = BridgeStellarAccountId
    /\ tx # tx2
    => tx.depositId # tx2.depositId
  /\ \A tx,tx2 \in Ethereum!Executed :
    /\ tx.from = BridgeEthereumAccountId
    /\ tx2.from = BridgeEthereumAccountId
    /\ tx # tx2
    => tx.depositId # tx2.depositId
Inv10__ == \* we have Inv10__ => Inv10
  TypeOkay /\ Inv1 /\ Inv2 /\ Inv3 /\ Inv4 /\ Inv6 /\ Inv7

\* Canary:
Inv11 == FALSE
Inv11_ == Init
=============================================================================
