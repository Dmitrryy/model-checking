------------------------------- MODULE stack -------------------------------
EXTENDS Integers, TLC, Sequences, FiniteSets
Elem_num == 7
Status == {"Stack", "DataManager"}
Number == 1..Elem_num
Next_v == 0..Elem_num
Elems == [i: Number, n: Next_v, st: Status]


isStack(elem) == "Stack" \in Status /\ elem.st = "Stack"

IsDataManager(elem) == "DataManager" \in Status /\ elem.st = "DataManager"

initState == [i \in Number |-> CHOOSE e \in Elems: e.i = i /\ (e.n = i + 1 \/ (e.n = 0 /\ e.i = Elem_num))]

(*--fair algorithm stack
variables
    elems = initState,
    first = 1,
    mutex = FALSE
define
    Fold(op(_,_), acc) ==
        LET getelem[i \in Number] ==
            IF i = Elem_num THEN op(elems[i], acc)
            ELSE
                LET elem == elems[i]
                IN op(elem, getelem[elem.i + 1])
        IN getelem[1]
    
    Fill(op(_,_), acc) ==
        LET getelem[i \in Number] ==
            IF i = Elem_num THEN op(elems[i], acc)
            ELSE
                LET elem == elems[i]
                IN op(elem, getelem[elem.n])
        IN getelem[first]
    
    AllElems == Fold(LAMBDA b, acc: {b} \union acc, {})
    AllstackElems == Fold(LAMBDA b, acc: IF isStack(b) THEN {b} \union acc ELSE acc, {})
    AllDataManager == Fold(LAMBDA b, acc: IF IsDataManager(b) THEN {b} \union acc ELSE acc, {})
    AllInnerstackElems == Fold(LAMBDA b, acc: IF isStack(b) /\ ~(b.i = first) /\ ~(b.i = Elem_num) THEN {b} \union acc ELSE acc, {})

    \* invariants
    HavingHead == (elems[first].st = "Stack")
    HavingTail == (elems[Elem_num].st = "Stack")
    Acyclicity == ~(first = Elem_num)
    Linearity == \A e \in AllstackElems: (\A e2 \in AllstackElems: (e.i = e2.i) \/ ~(e.n = e2.n))
    LastIsTail == (elems[Elem_num].n = 0)
    FirstIsHead == \A e \in AllstackElems: ~(e.n = elems[first].i)
    Connectivity == (\A e \in AllstackElems: e.n \in Number \/ (e.n = 0 /\ e.i = Elem_num)) /\ (\A e \in AllstackElems: e.n \in Number \/ (e.n = 0 /\ e.i = Elem_num))
    invariants == HavingHead /\ HavingTail /\ Acyclicity /\ Linearity /\ LastIsTail /\ FirstIsHead /\ Connectivity
end define

\* sinchronization
\*=------------------------------------------------------------------
macro lock()
begin
    await ~mutex;
    mutex := TRUE;
end macro;

macro unlock()
begin
    mutex := FALSE;
end macro;
\*=------------------------------------------------------------------

macro pop() 
begin
    elems[first].st := "DataManager" || first := elems[first].n || elems[first].n := 0;
end macro;

macro push(e) 
begin
    elems[e.i].st := "Stack" || first := e.i || elems[e.i].n := first;
end macro;

procedure clear() 
begin
    clear_lock: lock();
    clear: while Cardinality(AllstackElems) > 2 do
        with e \in AllInnerstackElems do
            elems[e.i].st := "DataManager" || elems[e.i].n := 0;
        end with
    end while;
    clear_unlock: unlock();
end procedure;

fair process Main \in 1..2 begin
    main_loop:
    either
        pop_lock: lock();
        pop: if ~(elems[first].n = 0) then
            pop();
        end if;
        pop_unlock: unlock();
    or
        push_lock: lock();
        push: if Cardinality(AllDataManager) > 0 then
            with e \in AllDataManager do
                push(e);
            end with;
        end if;
        push_unlock: unlock();
    or
        call clear();
    end either;
    end_main_loop: goto main_loop
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "2cfc8a76" /\ chksum(tla) = "38feced9")
\* Label clear of procedure clear at line 81 col 12 changed to clear_
VARIABLES elems, first, mutex, pc, stack

(* define statement *)
Fold(op(_,_), acc) ==
    LET getelem[i \in Number] ==
        IF i = Elem_num THEN op(elems[i], acc)
        ELSE
            LET elem == elems[i]
            IN op(elem, getelem[elem.i + 1])
    IN getelem[1]

Fill(op(_,_), acc) ==
    LET getelem[i \in Number] ==
        IF i = Elem_num THEN op(elems[i], acc)
        ELSE
            LET elem == elems[i]
            IN op(elem, getelem[elem.n])
    IN getelem[first]

AllElems == Fold(LAMBDA b, acc: {b} \union acc, {})
AllstackElems == Fold(LAMBDA b, acc: IF isStack(b) THEN {b} \union acc ELSE acc, {})
AllDataManager == Fold(LAMBDA b, acc: IF IsDataManager(b) THEN {b} \union acc ELSE acc, {})
AllInnerstackElems == Fold(LAMBDA b, acc: IF isStack(b) /\ ~(b.i = first) /\ ~(b.i = Elem_num) THEN {b} \union acc ELSE acc, {})


HavingHead == (elems[first].st = "Stack")
HavingTail == (elems[Elem_num].st = "Stack")
Acyclicity == ~(first = Elem_num)
Linearity == \A e \in AllstackElems: (\A e2 \in AllstackElems: (e.i = e2.i) \/ ~(e.n = e2.n))
LastIsTail == (elems[Elem_num].n = 0)
FirstIsHead == \A e \in AllstackElems: ~(e.n = elems[first].i)
Connectivity == (\A e \in AllstackElems: e.n \in Number \/ (e.n = 0 /\ e.i = Elem_num)) /\ (\A e \in AllstackElems: e.n \in Number \/ (e.n = 0 /\ e.i = Elem_num))
invariants == HavingHead /\ HavingTail /\ Acyclicity /\ Linearity /\ LastIsTail /\ FirstIsHead /\ Connectivity


vars == << elems, first, mutex, pc, stack >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ elems = initState
        /\ first = 1
        /\ mutex = FALSE
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "main_loop"]

clear_lock(self) == /\ pc[self] = "clear_lock"
                    /\ ~mutex
                    /\ mutex' = TRUE
                    /\ pc' = [pc EXCEPT ![self] = "clear_"]
                    /\ UNCHANGED << elems, first, stack >>

clear_(self) == /\ pc[self] = "clear_"
                /\ IF Cardinality(AllstackElems) > 2
                      THEN /\ \E e \in AllInnerstackElems:
                                elems' = [elems EXCEPT ![e.i].st = "DataManager",
                                                       ![e.i].n = 0]
                           /\ pc' = [pc EXCEPT ![self] = "clear_"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "clear_unlock"]
                           /\ elems' = elems
                /\ UNCHANGED << first, mutex, stack >>

clear_unlock(self) == /\ pc[self] = "clear_unlock"
                      /\ mutex' = FALSE
                      /\ pc' = [pc EXCEPT ![self] = "Error"]
                      /\ UNCHANGED << elems, first, stack >>

clear(self) == clear_lock(self) \/ clear_(self) \/ clear_unlock(self)

main_loop(self) == /\ pc[self] = "main_loop"
                   /\ \/ /\ pc' = [pc EXCEPT ![self] = "pop_lock"]
                         /\ stack' = stack
                      \/ /\ pc' = [pc EXCEPT ![self] = "push_lock"]
                         /\ stack' = stack
                      \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "clear",
                                                                  pc        |->  "end_main_loop" ] >>
                                                              \o stack[self]]
                         /\ pc' = [pc EXCEPT ![self] = "clear_lock"]
                   /\ UNCHANGED << elems, first, mutex >>

pop_lock(self) == /\ pc[self] = "pop_lock"
                  /\ ~mutex
                  /\ mutex' = TRUE
                  /\ pc' = [pc EXCEPT ![self] = "pop"]
                  /\ UNCHANGED << elems, first, stack >>

pop(self) == /\ pc[self] = "pop"
             /\ IF ~(elems[first].n = 0)
                   THEN /\ /\ elems' = [elems EXCEPT ![first].st = "DataManager",
                                                     ![first].n = 0]
                           /\ first' = elems[first].n
                   ELSE /\ TRUE
                        /\ UNCHANGED << elems, first >>
             /\ pc' = [pc EXCEPT ![self] = "pop_unlock"]
             /\ UNCHANGED << mutex, stack >>

pop_unlock(self) == /\ pc[self] = "pop_unlock"
                    /\ mutex' = FALSE
                    /\ pc' = [pc EXCEPT ![self] = "end_main_loop"]
                    /\ UNCHANGED << elems, first, stack >>

push_lock(self) == /\ pc[self] = "push_lock"
                   /\ ~mutex
                   /\ mutex' = TRUE
                   /\ pc' = [pc EXCEPT ![self] = "push"]
                   /\ UNCHANGED << elems, first, stack >>

push(self) == /\ pc[self] = "push"
              /\ IF Cardinality(AllDataManager) > 0
                    THEN /\ \E e \in AllDataManager:
                              /\ elems' = [elems EXCEPT ![e.i].st = "Stack",
                                                        ![e.i].n = first]
                              /\ first' = e.i
                    ELSE /\ TRUE
                         /\ UNCHANGED << elems, first >>
              /\ pc' = [pc EXCEPT ![self] = "push_unlock"]
              /\ UNCHANGED << mutex, stack >>

push_unlock(self) == /\ pc[self] = "push_unlock"
                     /\ mutex' = FALSE
                     /\ pc' = [pc EXCEPT ![self] = "end_main_loop"]
                     /\ UNCHANGED << elems, first, stack >>

end_main_loop(self) == /\ pc[self] = "end_main_loop"
                       /\ pc' = [pc EXCEPT ![self] = "main_loop"]
                       /\ UNCHANGED << elems, first, mutex, stack >>

Main(self) == main_loop(self) \/ pop_lock(self) \/ pop(self)
                 \/ pop_unlock(self) \/ push_lock(self) \/ push(self)
                 \/ push_unlock(self) \/ end_main_loop(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: clear(self))
           \/ (\E self \in 1..2: Main(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in 1..2 : WF_vars(Main(self)) /\ WF_vars(clear(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Wed May 22 22:10:48 MSK 2024 by dadro
\* Created Wed May 15 22:00:13 MSK 2024 by dadro
