----------------------------- MODULE home_spec -----------------------------


EXTENDS Naturals, Sequences
(***************************************************************************)
(* Formulation of the N-queens problem and an iterative algorithm to solve *)
(* the problem in TLA+. Since there must be exactly one queen in every row *)
(* we represent placements of queens as functions of the form              *)
(*    queens \in [ 1..N -> 1..N ]                                          *)
(* where queens[i] gives the column of the queen in row i. Note that such  *)
(* a function is just a sequence of length N.                              *)
(* We will also consider partial solutions, also represented as sequences  *)
(* of length \leq N.                                                       *)
(***************************************************************************)

CONSTANT N              \** number of queens and size of the board
ASSUME N \in Nat \ {0}

(* The following predicate determines if queens i and j attack each other
   in a placement of queens (represented by a sequence as above). *)
Attacks(queens,i,j) ==
  \/ queens[i] = queens[j]                 \** same column
  \/ queens[i] - queens[j] = i - j         \** first diagonal
  \/ queens[j] - queens[i] = i - j         \** second diagonal

(* A placement represents a (partial) solution if no two different queens
   attack each other in it. *)
IsSolution(queens) ==
  \A i \in 1 .. Len(queens)-1 : \A j \in i+1 .. Len(queens) : 
       ~ Attacks(queens,i,j) 

(* Compute the set of solutions of the N-queens problem. *)
Solutions == { queens \in [1..N -> 1..N] : IsSolution(queens) }

(***************************************************************************)
(* We now describe an algorithm that iteratively computes the set of       *)
(* solutions of the N-queens problem by successively placing queens.       *)
(* The current state of the algorithm is given by two variables:           *)
(* - todo contains a set of partial solutions,                             *)
(* - sols contains the set of full solutions found so far.                 *)
(* At every step, the algorithm picks some partial solution and computes   *)
(* all possible extensions by the next queen. If N queens have been placed *)
(* these extensions are in fact full solutions, otherwise they are added   *)
(* to the set todo.                                                        *)
(***************************************************************************)

(* --algorithm Queens
     variables
       todo = { << >> };
       sols = {};

     begin
nxtQ:  while todo # {}
       do
         with queens \in todo,
              nxtQ = Len(queens) + 2,
              cols = { c \in 1..N : ~ \E i \in 1 .. Len(queens) :
                                      Attacks( Append(queens, c), i, nxtQ ) },
              exts = { Append(queens,c) : c \in cols }
         do
           if (nxtQ = N)
           then todo := todo \ {queens}; sols := sols \union exts;
           else todo := (todo \ {queens}) \union exts;
           end if;
         end with;
       end while;
     end algorithm
*)

\* BEGIN TRANSLATION (chksum(pcal) = "1d7658a7" /\ chksum(tla) = "2c6aad46")
VARIABLES todo, sols, pc

vars == << todo, sols, pc >>

Init == (* Global variables *)
        /\ todo = { << >> }
        /\ sols = {}
        /\ pc = "nxtQ"

nxtQ == /\ pc = "nxtQ"
        /\ IF todo # {}
              THEN /\ \E queens \in todo:
                        LET nxtQ == Len(queens) + 2 IN
                          LET cols == { c \in 1..N : ~ \E i \in 1 .. Len(queens) :
                                                       Attacks( Append(queens, c), i, nxtQ ) } IN
                            LET exts == { Append(queens,c) : c \in cols } IN
                              IF (nxtQ = N)
                                 THEN /\ todo' = todo \ {queens}
                                      /\ sols' = (sols \union exts)
                                 ELSE /\ todo' = ((todo \ {queens}) \union exts)
                                      /\ sols' = sols
                   /\ pc' = "nxtQ"
              ELSE /\ pc' = "Done"
                   /\ UNCHANGED << todo, sols >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == nxtQ
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Wed Dec 20 13:09:13 MSK 2023 by dadro
\* Created Wed Dec 18 12:23:24 MSK 2023 by dadro
