------------------------------ MODULE StarbridgeEthToStellar ------------------------------

\* TODO ideally, we would have a separate bridge module in which the private variables of the Stellar and Ethereum modules are not in scope
\* TODO to help Apalache, we could implicitely assume that all transactions on Stellar are from the bridge account

EXTENDS Integers, Apalache, FiniteSets, TLC

\* @typeAlias: STELLAR_TX = [src : STELLAR_ACCNT, from : STELLAR_ACCNT, to : STELLAR_ACCNT, amount : Int, seq : Int, maxTime : Int, memo : HASH];
\* @typeAlias: ETH_TX = [from : ETH_ACCNT, to : ETH_ACCNT, amount : Int, stellarDst : STELLAR_ACCNT, hash : HASH, refundId : HASH];

StellarAccountId == {"BRIDGE_OF_STELLAR_ACCNT","USER_OF_STELLAR_ACCNT","USER2_OF_STELLAR_ACCNT"}
EthereumAccountId == {"BRIDGE_OF_ETH_ACCNT","USER_OF_ETH_ACCNT","USER2_OF_ETH_ACCNT"}
Amount == 1..1 \* transfer amounts
SeqNum == 0..1 \* we need at least two consecutive seqnums to be able to execute transactions on Stellar
Time == 0..0
WithdrawWindow == 1 \* time window the user has to execute a withdraw operation on Stellar
(* Hash == {"0_OF_HASH","1_OF_HASH","2_OF_HASH","3_OF_HASH"} *)
Hash == {"0_OF_HASH","1_OF_HASH","2_OF_HASH"}

BridgeStellarAccountId == "BRIDGE_OF_STELLAR_ACCNT"
BridgeEthereumAccountId == "BRIDGE_OF_ETH_ACCNT"

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
    bridgeIssuedWithdrawTx,
    \* @type: HASH -> STELLAR_TX;
    bridgeLastWithdrawTx,
    \* @type: Int;
    bridgeStellarTime,
    \* @type: STELLAR_ACCNT -> Int;
    bridgeStellarSeqNum,
    \* @type: Set(STELLAR_TX);
    bridgeStellarExecuted,
    \* @type: Set(HASH);
    bridgeRefunded

ethereumVars == <<ethereumExecuted, ethereumTime>>
stellarVars == <<stellarSeqNum, stellarTime, stellarMempool, stellarExecuted>>
bridgeVars == <<bridgeIssuedWithdrawTx, bridgeLastWithdrawTx, bridgeStellarTime, bridgeStellarSeqNum, bridgeStellarExecuted, bridgeRefunded>>
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
    /\  bridgeIssuedWithdrawTx = {}
    /\  bridgeLastWithdrawTx \in [Hash -> Stellar!Transaction]
    /\  bridgeStellarTime = 0
    /\  bridgeStellarSeqNum = [a \in StellarAccountId |-> 0]
    /\  bridgeStellarExecuted = {}
    /\  bridgeRefunded = {}
    /\  Stellar!Init /\ Ethereum!Init

TypeOkay ==
    /\  bridgeIssuedWithdrawTx \in SUBSET Hash
    /\  bridgeLastWithdrawTx \in [Hash -> Stellar!Transaction]
    /\  bridgeStellarTime \in Time
    /\  bridgeStellarSeqNum \in [StellarAccountId -> SeqNum]
    /\  bridgeStellarExecuted \in SUBSET Stellar!Transaction
    /\  bridgeRefunded \in SUBSET Hash
    /\  Stellar!TypeOkay /\ Ethereum!TypeOkay

SyncWithStellar ==
    /\  bridgeStellarTime' = stellarTime
    /\  bridgeStellarSeqNum' = stellarSeqNum
    /\  bridgeStellarExecuted' = stellarExecuted
    /\  UNCHANGED <<ethereumVars, stellarVars, bridgeIssuedWithdrawTx, bridgeLastWithdrawTx, bridgeRefunded>>

\* A withdraw transaction is irrevocably invalid when its time bound has ellapsed or the sequence number of the receiving account is higher than the transaction's sequence number
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
SignWithdrawTransaction == \E tx \in Ethereum!Executed :
  /\  tx.to = BridgeEthereumAccountId
  /\  tx.hash \notin bridgeRefunded
  /\  tx.hash \in bridgeIssuedWithdrawTx
      => LET withdrawTx == bridgeLastWithdrawTx[tx.hash] IN
           /\ \neg withdrawTx \in bridgeStellarExecuted
           /\ IrrevocablyInvalid(withdrawTx)
  /\ \E seqNum \in SeqNum  : \* chosen by the client
      LET timeBound ==
            IF \neg tx.hash \in bridgeIssuedWithdrawTx
              THEN TxTime(tx)+WithdrawWindow
              ELSE bridgeLastWithdrawTx[tx.hash].maxTime+WithdrawWindow
          withdrawTx == [
            src |-> tx.stellarDst,
            from |-> BridgeStellarAccountId,
            to |-> tx.stellarDst,
            amount |-> tx.amount,
            seq |-> seqNum,
            maxTime |-> timeBound,
            memo |-> tx.hash]
      IN
        /\ timeBound \in Time \* for the model-checker
        /\ Stellar!ReceiveTx(withdrawTx)
        /\ bridgeIssuedWithdrawTx' = bridgeIssuedWithdrawTx \union {tx.hash}
        /\ bridgeLastWithdrawTx' = [bridgeLastWithdrawTx EXCEPT ![tx.hash] = withdrawTx]
  /\  UNCHANGED <<ethereumVars, bridgeChainsStateVars, bridgeRefunded>>

\* @type: (ETH_TX, HASH) => ETH_TX;
RefundTx(tx, hash) == [
  from |-> BridgeEthereumAccountId,
  to |-> tx.from,
  amount |-> tx.amount,
  stellarDst |-> tx.stellarDst,
  refundId |-> tx.hash,
  hash |-> hash ]

SignRefundTransaction == \E tx \in Ethereum!Executed :
  /\  tx.to = BridgeEthereumAccountId
  /\  tx.hash \notin bridgeRefunded
  /\  tx.hash \in bridgeIssuedWithdrawTx =>
        LET withdrawTx == bridgeLastWithdrawTx[tx.hash] IN
          /\  withdrawTx \notin bridgeStellarExecuted
          /\  IrrevocablyInvalid(withdrawTx)
  /\  \E hash \in Hash : Ethereum!ExecuteTx(RefundTx(tx, hash))
  /\  bridgeRefunded' = bridgeRefunded \union {tx.hash}
  /\  UNCHANGED <<stellarVars, bridgeIssuedWithdrawTx, bridgeLastWithdrawTx, bridgeChainsStateVars>>

UserInitiates ==
  \* a client initiates a transfer on Ethereum:
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
          refundId |-> hash ] \* refundId does not matter here
       IN  Ethereum!ExecuteTx(tx)

Next ==
    \/  SyncWithStellar
    \/  UserInitiates
    \/  SignWithdrawTransaction
    \/  SignRefundTransaction
    \/ \* internal stellar transitions:
      /\ UNCHANGED <<ethereumVars, bridgeVars>>
      /\ \/  Stellar!Tick
         \/  Stellar!ExecuteTx
         \/  Stellar!BumpSeqNum
    \/ \* internal ethereum transitions:
      /\ UNCHANGED <<stellarVars, bridgeVars>>
      /\ Ethereum!Tick


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
    /\  tx.memo \in bridgeIssuedWithdrawTx
    \* the withdraw has a corresponding initiating transaction:
    /\ \E ethTx \in Ethereum!Executed:
      /\ ethTx.hash = tx.memo
      /\ ethTx.to = BridgeEthereumAccountId
      /\ ethTx.amount = tx.amount
    \* if it's not the last issued withdrawal for a given hash, then it is irrevocably invalid:
    /\ \/ tx = bridgeLastWithdrawTx[tx.memo]
       \/ IrrevocablyInvalid(tx)
Inv2_ == TypeOkay /\ Inv2 /\ Inv1

\* properties of refund transactions:
Inv3 == \A refund \in Ethereum!Executed :
  refund.from = BridgeEthereumAccountId => \* if it's a refund:
    \* the refund is recorded by the bridge:
    /\ refund.refundId \in bridgeRefunded
    \* the refund has a corresponding initiating transaction:
    /\ \E tx \in Ethereum!Executed :
        /\ tx.hash = refund.refundId
        /\ tx.to = BridgeEthereumAccountId
        /\ tx.amount = refund.amount
    \* and no two refunds are for the same transfer:
    /\ \A refund2 \in Ethereum!Executed :
      refund2.from = BridgeEthereumAccountId => \* if it's a refund:
        refund = refund2 \/ refund.refundId # refund2.refundId
Inv3_ == TypeOkay /\ Inv0 /\ Inv3

\* a refunded withdraw transaction that sits in the mempool is invalid:
Inv6 == \A tx \in stellarMempool :
  /\ tx.from = BridgeStellarAccountId \* it's a withdraw
  /\ tx.memo \in bridgeRefunded \* it's been refunded
  => IrrevocablyInvalid(tx)
Inv6_ == TypeOkay /\ Inv1 /\ Inv2 /\ Inv6

\* an executed withdrawal cannot be refunded:
Inv7 == \A tx \in stellarExecuted :
  tx.from = BridgeStellarAccountId => \* it's a withdraw
    tx.memo \notin bridgeRefunded
Inv7_ == TypeOkay /\ Inv2 /\ Inv6 /\ Inv7

WithdrawTxs ==
  LET
    \* @type: Set(STELLAR_TX);
    all == { bridgeLastWithdrawTx[h] : h \in Hash }
  IN
    {tx \in all : tx.memo \in bridgeIssuedWithdrawTx}

\* there's at most one executed withdrawal per transfer:
Inv8 == \A tx1 \in stellarExecuted :
  /\ tx1.from = BridgeStellarAccountId => tx1 = bridgeLastWithdrawTx[tx1.memo]
  /\ \A tx2 \in stellarExecuted :
    tx1.from = BridgeStellarAccountId /\ tx2.from = BridgeStellarAccountId =>
      tx1 = tx2 \/ tx1.memo # tx2.memo
Inv8_ == TypeOkay /\ Inv1 /\ Inv2 /\ Inv8

\* Funds deposited in the bridge account always exceed or are equal to the funds taken out:
MainInvariant ==
  /\ EthBridgeBalance - StellarWithdrawals >= 0
MainInvariant_ == \* check MainInvariant_ => MainInvariant
  TypeOkay /\ Inv0 /\ Inv2 /\ Inv3 /\ Inv7 /\ Inv8
=============================================================================
