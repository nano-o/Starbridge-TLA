----------------------------- MODULE Starbridge -----------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
        EthAddr \* an address on Ethereum
     ,  StellarAddr \* an address on Stellar
     ,  EthTxId \* something that identifies a transaction uniquely, e.g. a hash
     ,  StellarTxId
     ,  Validator \* bridge validators
     ,  BridgeEthAddr \* the address of the bridge on Ethereum
     ,  BridgeStellarAddr \* the address of the bridge on Stellar
     ,  MaxAmount
     ,  Threshold \* the minimum number of validators that must agree on a transaction

EthTx == [id : EthTxId, from : EthAddr, to : EthAddr, amount : Nat]
StellarTx == [id : StellarTxId, from : StellarAddr, to : StellarAddr, amount : Nat]
RequestToBridge == [to : StellarAddr, ethId : EthTxId, amount : Nat]

ASSUME EthTxId = StellarTxId \* temporary assumption to make things simple

\* What is the Stellar transaction corresponding to a bridge tranfer request?
\* Below is a simple attempt at defining that.
CorrespondingStellarTxId(request) ==
    request.id
CorrespondingStellarTx(request) == [
    id |-> CorrespondingStellarTxId(request),
    from |-> BridgeStellarAddr,
    to |-> request.to, 
    amount |-> request.amount] 

(*
--algorithm EthToStellar {
    variables
        usedEthTxIds = {},
        ethChain = {}, \* should be a list, but a set is simpler and we don't care about the order of transactions
        requests = [v \in Validator |-> {}], \* requests sent to validators
        signatures = <<>>, \* map from Stellar transaction ID to validator that signed it
    define {
        TypeInvariant ==
            /\ \A v \in Validator :
                \A r \in requests[v] :
                    /\ r.id \in EthTxId
                    /\ r.amount \in 1..MaxAmount
        \* TODO:
        \* There should be at least as much tokens in the Ethereum bridge address as there are in the whole Stellar network
    }
    process (sendToStellar \in EthAddr \ {BridgeEthAddr})
        variables
            request = <<>>, \* the request made to the bridge 
    {
    \* a user on Ethereum wants to transfer assets to Stellar
l0:     with (txId \in EthTxId \ usedEthTxIds, amount \in 1..MaxAmount) {
            usedEthTxIds := usedEthTxIds \union {txId};
            with (ethTx = [id |-> txId, from |-> self, to |-> BridgeEthAddr, amount |-> amount])
            ethChain := ethChain \union {ethTx}; \* execute transaction on Ethereum
            with (to \in StellarAddr \ {BridgeStellarAddr})
            request := [id |-> txId, amount |-> amount, to |-> to];
            requests := [v \in Validator |-> requests[v] \union {request}]; \* send a request to all the bridge validators
        };
l1:     with (stellarTx = CorrespondingStellarTx(request))
        await   
            /\  stellarTx \in DOMAIN signatures
            /\  Cardinality(signatures[stellarTx]) >= Threshold
    }
    process (validator \in Validator) {
l0:     while (TRUE) {
            either {
                await requests[self] # {};
                with (r \in requests[self]) { \* pick a request and process it
                    \* check that the transfer was made on Ethereum:
                    with (src \in EthAddr)
                    with (tx = [id |-> r.id, from |-> src, to |-> BridgeEthAddr, amount |-> r.amount])
                    if (tx \in ethChain) {
                        requests[self] := requests[self] \ {r}; \* remove r from the set of pending requests
                        with (stellarTx = CorrespondingStellarTx(r)) {
                            if (stellarTx \notin DOMAIN signatures) {
                                await PrintT(stellarTx);
                                signatures := [tx_ \in DOMAIN signatures \union {stellarTx} |->
                                    IF tx_ = stellarTx
                                    THEN {self}
                                    ELSE signatures[tx_]]
                            }
                            else 
                                signatures[stellarTx] := @ \union self;
                        } 
                    }
                }
            }
            or {
                await \A a \in EthAddr \ {BridgeEthAddr} : pc[a] = "Done";
                goto "Done";
            }
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "c633ca88" /\ chksum(tla) = "655aaf75")
\* Label l0 of process sendToStellar at line 53 col 14 changed to l0_
VARIABLES usedEthTxIds, ethChain, requests, signatures, pc

(* define statement *)
TypeInvariant ==
    /\ \A v \in Validator :
        \A r \in requests[v] :
            /\ r.id \in EthTxId
            /\ r.amount \in 1..MaxAmount

VARIABLE request

vars == << usedEthTxIds, ethChain, requests, signatures, pc, request >>

ProcSet == (EthAddr \ {BridgeEthAddr}) \cup (Validator)

Init == (* Global variables *)
        /\ usedEthTxIds = {}
        /\ ethChain = {}
        /\ requests = [v \in Validator |-> {}]
        /\ signatures = <<>>
        (* Process sendToStellar *)
        /\ request = [self \in EthAddr \ {BridgeEthAddr} |-> <<>>]
        /\ pc = [self \in ProcSet |-> CASE self \in EthAddr \ {BridgeEthAddr} -> "l0_"
                                        [] self \in Validator -> "l0"]

l0_(self) == /\ pc[self] = "l0_"
             /\ \E txId \in EthTxId \ usedEthTxIds:
                  \E amount \in 1..MaxAmount:
                    /\ usedEthTxIds' = (usedEthTxIds \union {txId})
                    /\ LET ethTx == [id |-> txId, from |-> self, to |-> BridgeEthAddr, amount |-> amount] IN
                         ethChain' = (ethChain \union {ethTx})
                    /\ \E to \in StellarAddr \ {BridgeStellarAddr}:
                         request' = [request EXCEPT ![self] = [id |-> txId, amount |-> amount, to |-> to]]
                    /\ requests' = [v \in Validator |-> requests[v] \union {request'[self]}]
             /\ pc' = [pc EXCEPT ![self] = "l1"]
             /\ UNCHANGED signatures

l1(self) == /\ pc[self] = "l1"
            /\ LET stellarTx == CorrespondingStellarTx(request[self]) IN
                 /\  stellarTx \in DOMAIN signatures
                 /\  Cardinality(signatures[stellarTx]) >= Threshold
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << usedEthTxIds, ethChain, requests, signatures, 
                            request >>

sendToStellar(self) == l0_(self) \/ l1(self)

l0(self) == /\ pc[self] = "l0"
            /\ \/ /\ requests[self] # {}
                  /\ \E r \in requests[self]:
                       \E src \in EthAddr:
                         LET tx == [id |-> r.id, from |-> src, to |-> BridgeEthAddr, amount |-> r.amount] IN
                           IF tx \in ethChain
                              THEN /\ requests' = [requests EXCEPT ![self] = requests[self] \ {r}]
                                   /\ LET stellarTx == CorrespondingStellarTx(r) IN
                                        IF stellarTx \notin DOMAIN signatures
                                           THEN /\ PrintT(stellarTx)
                                                /\ signatures' =           [tx_ \in DOMAIN signatures \union {stellarTx} |->
                                                                 IF tx_ = stellarTx
                                                                 THEN {self}
                                                                 ELSE signatures[tx_]]
                                           ELSE /\ signatures' = [signatures EXCEPT ![stellarTx] = @ \union self]
                              ELSE /\ TRUE
                                   /\ UNCHANGED << requests, signatures >>
                  /\ pc' = [pc EXCEPT ![self] = "l0"]
               \/ /\ \A a \in EthAddr \ {BridgeEthAddr} : pc[a] = "Done"
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED <<requests, signatures>>
            /\ UNCHANGED << usedEthTxIds, ethChain, request >>

validator(self) == l0(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in EthAddr \ {BridgeEthAddr}: sendToStellar(self))
           \/ (\E self \in Validator: validator(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Thu May 05 12:54:08 PDT 2022 by nano
\* Created Mon Apr 11 15:36:08 PDT 2022 by nano
