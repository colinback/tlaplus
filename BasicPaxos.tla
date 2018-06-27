----------------------------- MODULE BasicPaxos -----------------------------
(***************************************************************************)
(* This is a specification of the Paxos algorithm without explicit leaders *)
(* or learners.  It refines the spec in Voting                             *)
(***************************************************************************)
EXTENDS Integers

(***************************************************************************)
(* The constant parameters and the set Ballots are the same as in Voting.  *)
(***************************************************************************)
CONSTANT Value, Acceptor, Quorum

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 
      
Ballot ==  1..100

(*************************************************************************)
(* An unspecified value that is not a ballot number.                     *)
(*************************************************************************)
None == CHOOSE v : v \notin Ballot

  
(***************************************************************************)
(* This is a message-passing algorithm, so we begin by defining the set    *)
(* Message of all possible messages.  The messages are explained below     *)
(* with the actions that send them.                                        *)
(***************************************************************************)
Message ==      [type : {"1a"}, bal : Ballot]
           \cup [type : {"1b"}, acc : Acceptor, bal : Ballot, 
                 mbal : Ballot \cup {-1}, mval : Value \cup {None}]
           \cup [type : {"2a"}, bal : Ballot, val : Value]
           \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]


VARIABLE maxBallot,
         acceptedBallot,     \* <<acceptedBallot[a], acceptedValue[a]>> is the vote with the largest
         acceptedValue,      \* ballot number cast by a; it equals <<-1, None>> if a has not cast any vote.
         msgs                \* The set of all messages that have been sent.

(***************************************************************************)
(* The type invariant and initial predicate.                               *)
(***************************************************************************)
TypeOK == /\ maxBallot \in [Acceptor -> Ballot \cup {-1}]
          /\ acceptedBallot \in [Acceptor -> Ballot \cup {-1}]
          /\ acceptedValue \in [Acceptor -> Value \cup {None}]
          /\ msgs \subseteq Message

Init == /\ maxBallot = [a \in Acceptor |-> -1]
        /\ acceptedBallot = [a \in Acceptor |-> -1]
        /\ acceptedValue = [a \in Acceptor |-> None]
        /\ msgs = {}

(***************************************************************************)
(* The actions.  We begin with the subaction (an action that will be used  *)
(* to define the actions that make up the next-state action.               *)
(***************************************************************************)
Send(m) == msgs' = msgs \cup {m}

(***************************************************************************)
(* In an implementation, there will be a leader process that orchestrates  *)
(* a ballot.  The ballot b leader performs actions Phase1a(b) and          *)
(* Phase2a(b).  The Phase1a(b) action sends a phase 1a message (a message  *)
(* m with m.type = "1a") that begins ballot b.                             *)
(***************************************************************************)
Phase1a(b) == /\ Send([type |-> "1a", bal |-> b])
              /\ UNCHANGED <<maxBallot, acceptedBallot, acceptedValue>>
          
(****************************************************************************)
(* Upon receipt of a ballot b phase 1a message, acceptor a can perform a    *)
(* Phase1b(a) action only if b > maxBallot[a]. The action sets maxBallot[a] *) 
(* to b and sends a phase 1b message to the leader containing the values of *)
(* accpetedBallot[a] and acceptedValue[a].                                  *)
(****************************************************************************)
Phase1b(a) == /\ \E m \in msgs : 
                  /\ m.type = "1a"
                  /\ m.bal > maxBallot[a]
                  /\ maxBallot' = [maxBallot EXCEPT ![a] = m.bal]
                  /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal, 
                            mbal |-> acceptedBallot[a], mval |-> acceptedValue[a]])
              /\ UNCHANGED <<acceptedBallot, acceptedValue>>

Phase2a(b, v) == /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
                 /\ \E Q \in Quorum : 
                    LET Q1b == {m \in msgs : /\ m.type = "1b"
                                 /\ m.acc \in Q
                                 /\ m.bal = b}
                        Q1bv == {m \in Q1b : m.mbal \geq 0}
                    IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a 
                        /\ \/ Q1bv = {}
                           \/ \E m \in Q1bv : 
                                /\ m.mval = v
                                /\ \A mm \in Q1bv : m.mbal \geq mm.mbal 
                 /\ Send([type |-> "2a", bal |-> b, val |-> v])
                 /\ UNCHANGED <<maxBallot, acceptedBallot, acceptedValue>>

Phase2b(a) == \E m \in msgs : /\ m.type = "2a"
                              /\ m.bal \geq maxBallot[a]
                              /\ maxBallot' = [maxBallot EXCEPT ![a] = m.bal]
                              /\ acceptedBallot' = [acceptedBallot EXCEPT ![a] = m.bal]
                              /\ acceptedValue' = [acceptedValue EXCEPT ![a] = m.val]
                              /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])
                              
(***************************************************************************)
(* In an implementation, there will be learner processes that learn from   *)
(* the phase 2b messages if a value has been chosen.  The learners are     *)
(* omitted from this abstract specification of the algorithm.              *)
(***************************************************************************)

(***************************************************************************)
(* Below are defined the next-state action and the complete spec.          *)
(***************************************************************************)
Next == \/ \E b \in Ballot : \/ Phase1a(b)
                             \/ \E v \in Value : Phase2a(b, v)
        \/ \E a \in Acceptor : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_<<maxBallot, acceptedBallot, acceptedValue, msgs>>

(***************************************************************************)
(* As we observed, votes are registered by sending phase 2b messages.  So  *)
(* the array `votes' describing the votes cast by the acceptors is defined *)
(* as follows.                                                             *)
(***************************************************************************)
votes == [a \in Acceptor |->  
           {<<m.bal, m.val>> : m \in {mm \in msgs: /\ mm.type = "2b"
                                                   /\ mm.acc = a }}]

(***************************************************************************)
(* We now instantiate module Voting, substituting the constants Value,     *)
(* Acceptor, and Quorum declared in this module for the corresponding      *)
(* constants of that module Voting, and substituting the variable maxBal   *)
(* and the defined state function `votes' for the correspondingly-named    *)
(* variables of module Voting.                                             *)
(***************************************************************************)
V == INSTANCE Voting 

THEOREM Spec => V!Spec
-----------------------------------------------------------------------------
(***************************************************************************)
(* Here is a first attempt at an inductive invariant used to prove this    *)
(* theorem.                                                                *)
(***************************************************************************)
Inv == /\ TypeOK
       /\ \A a \in Acceptor : IF acceptedBallot[a] = -1
                                THEN acceptedValue[a] = None
                                ELSE <<acceptedBallot[a], acceptedValue[a]>> \in votes[a]
       /\ \A m \in msgs : 
             /\ (m.type = "1b") => /\ maxBallot[m.acc] \geq m.bal
                                   /\ (m.mbal \geq 0) =>  
                                       <<m.mbal, m.mval>> \in votes[m.acc]
             /\ (m.type = "2a") => /\ \E Q \in Quorum : 
                                         V!ShowsSafeAt(Q, m.bal, m.val)
                                   /\ \A mm \in msgs : /\ mm.type = "2a"
                                                       /\ mm.bal = m.bal
                                                       => mm.val = m.val
       /\ V!Inv
=============================================================================
\* Modification History
\* Last modified Tue Jun 26 20:35:29 PDT 2018 by Administrator
\* Created Tue Jun 26 20:16:20 PDT 2018 by Administrator
