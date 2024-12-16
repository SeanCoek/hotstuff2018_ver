include "Tree.dfy"

module HotStuff_Spec {}
function getParent(s: SystemState, b: Block) : Block
requires b in s.ledger.parent
{
    s.ledger.parent[b]
}

function getRound(s: SystemState, b: Block) : Rounds
requires b in s.ledger.round
{
    s.ledger.round[b]
}

function diff(b: Block, c: Block, s: SystemState) : int
requires b in s.ledger.round && c in s.ledger.round
requires TypeOK(s)
{
    getRound(s, b) - getRound(s, c)
}


datatype Node = CNode | FNode


const CNodes : set<Node>
const FNodes : set<Node>
const Nodes := CNodes + FNodes

lemma{:axiom} FaultyLimitLemma()
ensures |Nodes| > 3*|FNodes|+1


predicate Quorum(nodes: set<Node>)
{
    |nodes| >= 2*|FNodes|+1
}


predicate Proposed(b: Block, s: SystemState)
// requires b in s.ledger.round
{
    && b in s.ledger.existsBlocks
    && b in s.ledger.round
    && s.ledger.round[b] != -1
}

predicate Confirmed(b: Block, s: SystemState)
requires b in s.ledger.round
requires b in s.votes
{
    && Proposed(b, s)
    && Quorum(s.votes[b])
}

predicate Committed(b: Block, s: SystemState)
requires TypeOK(s)
requires b in s.ledger.parent
{
    exists c | c in s.ledger.existsBlocks :: 
                                            && chain(b, c, s.ledger)
                                            && Confirmed(c, s)
}

/**
 * Action of Propose
 *
 */
predicate propose(b: Block, p: Block, r: Rounds, s: SystemState, s': SystemState)
requires TypeOK(s)
requires TypeOK(s')
requires b in s'.ledger.round
requires b in s'.ledger.parent
{
    && s'.ledger.round[b] == r
    && s'.ledger.parent[b] == p
}

predicate Propose(b: Block, p: Block, r: Rounds, s: SystemState, s': SystemState)
requires TypeOK(s)
requires TypeOK(s')
requires b in s.ledger.round
requires p in s.ledger.round && p in s.votes
requires b in s'.ledger.round
requires b in s'.ledger.parent
{
    && !Proposed(b, s)
    && Confirmed(p, s)
    && r > s.ledger.round[p]
    && propose(b, p, r, s, s')
    && s.lock == s'.lock
    && s.max == s'.max
    && s.votes == s'.votes
}
/* END of Propose */






/**
 * Action of Vote
 */
predicate vote(n: Node, b: Block, s: SystemState, s': SystemState)
requires TypeOK(s) && TypeOK(s')
requires b in s'.ledger.round
requires b in s'.votes
requires b in s.votes
requires n in s.lock && b in s.ledger.parent && s.ledger.parent[b] in s.ledger.parent && s.ledger.parent[s.ledger.parent[b]] in s.ledger.round
requires s.lock[n] in s.ledger.round
requires n in s'.max
{
    && s'.max[n] == s'.ledger.round[b]
    && (forall n' | n' in Nodes && n' != n :: s.max[n'] == s'.max[n'])
    && s'.votes[b] == s.votes[b] + {n}
    && (forall b | b in s.ledger.existsBlocks :: b in s'.votes.Keys && s.votes[b] == s'.votes[b])
    && if s.ledger.round[s.lock[n]] < s.ledger.round[s.ledger.parent[s.ledger.parent[b]]]
       then 
        && s'.lock[n] == s.ledger.parent[s.ledger.parent[b]]
        && (forall n' | n' in Nodes && n' != n :: s.lock[n'] == s'.lock[n'])
       else
        && s.lock == s'.lock
    // true
}


predicate Vote(n: Node, b: Block, s: SystemState, s': SystemState)
requires TypeOK(s) && TypeOK(s')
{
    && Proposed(b, s)
    && n in Nodes
    && (
        || !(n in CNodes)
        || (
            && s.ledger.round[b] > s.max[n]
            && s.ledger.round[s.lock[n]] <= s.ledger.round[s.ledger.parent[b]]
        )
    )
    && b in s'.ledger.round
    && vote(n, b, s, s')
    && s.ledger.round == s'.ledger.round
    && s.ledger.parent == s'.ledger.parent
    // true
}
/* END of Vote */


datatype SystemState = SystemState(
    ledger: Tree,
    votes: map<Block, set<Node>>,
    lock: map<Node, Block>,
    max: map<Node, Rounds>
)

predicate TypeOK(s: SystemState)
{
    && (forall b | b in s.ledger.existsBlocks :: ( && b in s.ledger.round.Keys 
                                                    && b in s.ledger.parent.Keys 
                                                    && b in s.votes.Keys
                                                 ))
    && (forall n | n in Nodes :: ( && n in s.lock.Keys 
                                   && n in s.max.Keys))
    && (forall b | b in s.ledger.round.Keys :: b in s.ledger.existsBlocks && exists r: Rounds {:trigger dummy(r)} :: r == getRound(s, b))
    && (forall b | b in s.ledger.parent.Keys :: b in s.ledger.existsBlocks && getParent(s, b) in s.ledger.existsBlocks)
    && (forall b | b in s.votes.Keys :: b in s.ledger.existsBlocks && s.votes[b] <= Nodes)
    && (forall n | n in s.lock.Keys :: n in Nodes && s.lock[n] in s.ledger.existsBlocks)
    && (forall n | n in s.max.Keys :: n in Nodes && exists r: Rounds {:trigger dummy(r)} :: r == s.max[n])
}

predicate SystemInit(s: SystemState)
requires TypeOK(s)
{
    && TreeInit(s.ledger)
    && s.votes == map[s.ledger.gen := Nodes]
    && (forall n | n in Nodes :: s.lock[n] == s.ledger.gen)
    && (forall n | n in Nodes :: s.max[n] == 0)
}

ghost predicate SystemNext(s: SystemState, s': SystemState)
requires TypeOK(s) && TypeOK(s')
{
    || (exists b, p, r: Rounds | b in s.ledger.existsBlocks && p in s.ledger.existsBlocks :: 
                && b in s'.ledger.round
                && Propose(b, p, r, s, s')
                && b in s'.ledger.round)
    || (exists b, n | b in s.ledger.existsBlocks && n in Nodes :: 
                && Vote(n, b, s, s'))
}


// ghost predicate Spec()
// {
//     &&(exists s: SystemState :: TypeOK(s) && SystemInit(s))
//     &&(forall s: SystemState, s': SystemState :: TypeOK(s) && TypeOK(s') && SystemNext(s, s'))
// }


ghost predicate Spec(trace:seq<SystemState>)
requires |trace| > 0

{
    && (forall i:nat | 0 <= i < |trace| :: TypeOK(trace[i]))
    && SystemInit(trace[0])
    && (
        forall i:nat | 0 <= i < |trace|-1 :: SystemNext(trace[i], trace[i+1])
    )
}


predicate cci(s: SystemState, b: Block, c: Block, i: nat)
requires TypeOK(s)
{
    && b in s.ledger.existsBlocks
    && c in s.ledger.existsBlocks
    && Committed(b, s)
    && Confirmed(c, s)
    && getRound(s, b) + i == getRound(s, c)
}

predicate cc(s: SystemState, b: Block, c: Block)
requires TypeOK(s)
{
    && b in s.ledger.existsBlocks
    && c in s.ledger.existsBlocks
    && Committed(b, s)
    && Confirmed(c, s)
    && getRound(s, b) <= getRound(s, c)
}


predicate iCorrect(s: SystemState, i: nat)
requires TypeOK(s)
{
    && (forall b, c | b in s.ledger.existsBlocks && c in s.ledger.existsBlocks ::
                cci(s, b, c, i) ==> Ancestor(b, c, s.ledger))
}

predicate Correct(s: SystemState)
requires TypeOK(s)
{ 
    (forall b, c | b in s.ledger.existsBlocks && c in s.ledger.existsBlocks ::
            cc(s, b, c) ==> Ancestor(b, c, s.ledger))
}

predicate Safe(s: SystemState)
requires TypeOK(s)
{
    (forall b, c | b in s.ledger.existsBlocks && c in s.ledger.existsBlocks :: 
                Committed(b, s) && Committed(c, s) ==> Ancestor(b, c, s.ledger) || Ancestor(c, b, s.ledger))
}


predicate IConf(s: SystemState)
requires TypeOK(s)
{
    (forall b | b in s.ledger.existsBlocks :: 
            Proposed(b, s) ==> Confirmed(s.ledger.parent[b], s))
}

predicate IPrepared(s: SystemState)
requires TypeOK(s)
{
    (forall b, n | b in s.ledger.existsBlocks && n in CNodes ::
                n in s.votes[b] ==> Proposed(b, s))
}

predicate IPr(s: SystemState)
requires TypeOK(s)
{
    (forall b | b in s.ledger.existsBlocks ::
            || getParent(s, b) == b
            || getRound(s, getParent(s, b)) < getRound(s, b))
}

predicate IPx(s: SystemState)
requires TypeOK(s)
{
    forall b | b in s.ledger.existsBlocks ::
            (getParent(s, b) == b) ==> getRound(s, b) in {0, -1}
}

/*
 Predicates defined in Tree.tla
 PType
 RType
 IPR
*/
predicate PType(s: SystemState)
requires TypeOK(s)
{
    forall b | b in s.ledger.existsBlocks :: getParent(s, b) in s.ledger.existsBlocks
}

predicate RType(s: SystemState)
requires TypeOK(s)
{
    forall b | b in s.ledger.existsBlocks :: exists r:Rounds {:trigger dummy(r)}  :: getRound(s, b) == r
}

predicate IPR(s: SystemState)
requires TypeOK(s)
{
    forall b | b in s.ledger.existsBlocks :: getRound(s, getParent(s, b)) <= getRound(s, b)
}
/*
 END :: Predicates defined in Tree.tla
*/


predicate IMax(s: SystemState)
requires TypeOK(s)
{
    forall b, n | b in s.ledger.existsBlocks && n in CNodes ::
            n in s.votes[b] ==> (s.max[n] >= getRound(s, b))
}

predicate ILockMax(s: SystemState)
requires TypeOK(s)
{
    (forall n | n in CNodes ::
            && getRound(s, s.lock[n]) <= s.max[n]
            && Proposed(s.lock[n], s))
}

predicate ILock(s: SystemState)
requires TypeOK(s)
{
    (forall b, n | b in s.ledger.existsBlocks && n in CNodes ::
            n in s.votes[b] ==> getRound(s, s.lock[n]) >= getRound(s, getParent(s, getParent(s, b))))
}

predicate IVote(s: SystemState)
requires TypeOK(s)
{
    (forall b, c, n | b in s.ledger.existsBlocks && c in s.ledger.existsBlocks && n in CNodes ::
            (&& n in s.votes[b]
                && n in s.votes[c]
                && getRound(s, b) <= getRound(s, c)
            ) ==> 
            (getRound(s, getParent(s, getParent(s, b))) <= getRound(s, getParent(s, c)))
    )
}

predicate IVote2(s: SystemState)
requires TypeOK(s)
{
    (forall b, c, n | b in s.ledger.existsBlocks && c in s.ledger.existsBlocks && n in CNodes ::
            (&& n in s.votes[b]
                && n in s.votes[c]
                && getRound(s, b) == getRound(s, c)
            ) ==> 
            (b == c)
    )
}



predicate Inv(s: SystemState)
{
    && TypeOK(s)
    && IVote(s)
    && IVote2(s)
    && IConf(s)
    && IPr(s)
    && IPx(s)
    && IMax(s)
    && ILockMax(s)
    && ILock(s)
    && IPrepared(s)
}

predicate dummy(i: nat) {true}

lemma ExistsI(s: SystemState)
requires TypeOK(s)
ensures (forall b, c | b in s.ledger.existsBlocks && c in s.ledger.existsBlocks :: cc(s, b, c)
        <==> exists i:nat :: cci(s, b, c, i))
{
    calc{ 
        true;
        { forall b, c | b in s.ledger.existsBlocks && c in s.ledger.existsBlocks {
                calc {
                    cc(s, b, c);
                    ==>
                    getRound(s, b) <= getRound(s, c);
                    ==
                    exists i:nat {:trigger dummy(i)} :: getRound(s, b) + i == getRound(s, c);
                }
            }
        }
    }
}


lemma CommittedConfirmed(s: SystemState)
requires TypeOK(s) && IConf(s)
ensures (forall b | b in s.ledger.existsBlocks :: Committed(b, s) ==> Confirmed(b, s))
{}


// lemma InductionStart(s: SystemState)
// requires TypeOK(s) && IConf(s) && IVote2(s)
// // ensures (forall b, c | b in s.ledger.existsBlocks && c in s.ledger.existsBlocks ::
// //                 cci(s, b, c, 0) ==> Ancestor(b, c, s.ledger))
// ensures forall b | b in s.ledger.existsBlocks :: Confirmed(b, s)
// {
//     forall b | b in s.ledger.existsBlocks
//     ensures Confirmed(b, s){
//         CommittedConfirmed(s);

//     }
// }

lemma TwoConfirmed(s: SystemState)
requires TypeOK(s) && IVote2(s)
ensures (forall b, c | b in s.ledger.existsBlocks && c in s.ledger.existsBlocks ::
                (&& Confirmed(b, s)
                 && Confirmed(c, s)
                 && getRound(s, b) == getRound(s, c)
                )
                ==> b == c)
// {}

lemma CanUseI(s: SystemState)
requires TypeOK(s)
ensures (forall i:nat :: iCorrect(s, i) ==> Correct(s))
// {}

lemma PTypeOK(s: SystemState)
requires TypeOK(s)
ensures PType(s)
{}

lemma IPHh(s: SystemState)
requires TypeOK(s) && IPr(s)
ensures IPR(s)
{}

lemma HTypeOK(s: SystemState)
requires TypeOK(s)
ensures RType(s)
// {
    // calc{
    //     TypeOK(s);
    //     ==>
    //     (&& forall b | b in s.ledger.existsBlocks :: b in s.ledger.round.Keys
    //     && (forall b | b in s.ledger.round.Keys :: b in s.ledger.existsBlocks && exists r: Rounds :: r == getRound(s, b))
    //     );
    // }
// }


lemma Init2Inv(s: SystemState)
requires SystemInit(s)
ensures Inv(s)

lemma Inv2Next(s: SystemState, s': SystemState)
requires Inv(s)
requires SystemNext(s, s')
ensures Inv(s')

lemma Inv2Correct(s: SystemState)
requires Inv(s)
ensures Correct(s)


/*
*   Thereom: If the state transitions (trace) satisfy system specification,
*            then all states in the trace should be Correct and hold some invarians. 
*
 */
lemma SpecCorrect(trace: seq<SystemState>)
requires |trace| > 0
requires Spec(trace)
ensures forall i | 0 <= i < |trace| :: (Correct(trace[i]) && Inv(trace[i]))
{
    // 1. Prove Initial State holds Invarians
    assert Inv(trace[0]) by {
        calc {
            Spec(trace);
            ==>
            SystemInit(trace[0]);
        }
        Init2Inv(trace[0]);
    }

    // 2. Prove Next State holds Invarians
    calc {
        forall i | 0 <= i < |trace|-1 :: SystemNext(trace[i], trace[i+1]);
        ==>
        forall i | 0 <= i < |trace|-1 :: Inv(trace[i+1]);
    }
    // assert forall i | 0 <= i < |trace|-1 :: Inv(trace[i+1]) by {
    //     calc {
    //         Spec(trace);
    //         ==>
    //         forall i | 0 <= i < |trace|-1 :: SystemNext(trace[i], trace[i+1]);
    //         ==> 
    //         forall i | 0 <= i < |trace|-1 :: Inv2Next(trace[i], trace[i+1]);
    //     }
    // }

    // 3. Since the Initial state and Next state hold Invarians,
    //    Then all the states hold Invarians.
    assert forall s | s in trace :: Inv(s);

    // 4.  Invarians imply Correct
    assert forall s | s in trace :: Correct(s) by {
        forall s | s in trace {Inv2Correct(s);}
    }
     
}

lemma LemmaSafe(s: SystemState)
requires Inv(s) && Correct(s)
ensures Safe(s)
{

}
