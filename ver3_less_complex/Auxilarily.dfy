include "Type.dfy"
include "common/sets.dfy"

module M_AuxilarilyFunc {
    import opened M_SpecTypes
    import opened M_Set

    /**
     * @returns Set union of a sequence of sets
     */
    function setUnionOnSeq<T>(sets : seq<set<T>>) : set<T>
    {
        if sets == [] then
            {}
        else
            sets[0] + setUnionOnSeq(sets[1..])
    }

    /**
    * @returns The maximum number of Byzantine validators allowed in a network
    *          of `setSize` validators
    */
    function f(setSize:nat) : nat
    {
        if setSize == 0 then
            0
        else
            (setSize - 1) / 3
    }

    /**
    * @returns The minimum size that any two subsets of validators for a
    *          network with `setSize` validators must have to guarantee that
    *          their intersection includes at least one honest validator under
    *          the assumption that no more than `f(setSeize)` validators are
    *          Byzantine.
    */
    function quorum(setSize : nat) : (ret: nat)
    requires setSize > 0
    ensures ret <= setSize
    {
        (setSize*2 - 1) / 3 + 1
    }  

    lemma LemmaTwoQuorumIntersection(
                                    allNodes : set<Address>,
                                    byzNodes : set<Address>,
                                    q1 : set<Address>,
                                    q2 : set<Address>)
    requires |allNodes| > 0
    requires q1 <= allNodes && |q1| == quorum(|allNodes|)
    requires q2 <= allNodes && |q2| == quorum(|allNodes|)
    requires |byzNodes| <= f(|allNodes|)
    ensures var honest := allNodes - byzNodes; q1 * q2 * honest != {}
    {
        var honest := allNodes - byzNodes;
        // prove q1*q2*honest != {}
        calc {
            |q1 * q2 * honest|;
            ==
            |(q1*q2) * honest|;
            ==
            |q1*q2| + |honest| - |(q1*q2) + honest|;
            >=
            |q1*q2| + |allNodes| - |byzNodes| - |(q1*q2) + honest|;
            >= calc {
                |q1 * q2|;
                ==
                |q1| + |q2| - |q1+q2|;
                >= calc {
                    |q1+q2|;
                    <= { LemmaSubsetCardinality(q1+q2, allNodes); }
                    |allNodes|;
                    }
                |q1| + |q2| - |allNodes|;
                }
            |q1| + |q2| - |byzNodes| - |(q1*q2) + honest|;
            >= {LemmaSubsetCardinality((q1*q2)+honest, allNodes);}
            |q1| + |q2| - |byzNodes| - |allNodes|;
            ==
            2 * quorum(|allNodes|) - |byzNodes| - |allNodes|;
            >=
            2 * quorum(|allNodes|) - f(|allNodes|) - |allNodes|;
            >=
            1;
        }
    }

    lemma LemmaHonestInQuorum<T> (allNodes: set<T>, byzNodes: set<T>, q1: set<T>)
    requires allNodes != {}
    requires q1 <= allNodes
    requires |q1| == quorum(|allNodes|)
    requires |byzNodes| <= f(|allNodes|)
    ensures var honest := allNodes - byzNodes; q1 * honest != {}
    {
        var honest := allNodes - byzNodes;

        calc {
            |q1 * honest|;
            ==
            |q1| + |honest| - |q1 + honest|;
            >=
            |q1| + |allNodes| - |byzNodes| - |q1 + honest|;
            >= { LemmaSubsetCardinality(q1+honest, allNodes); }
            |q1| - |byzNodes|;
            >=
            quorum(|allNodes|) - f(|allNodes|);
            >= 
            1;
        }
    }

    function leader(round : nat) : Address

    function getMatchMsg(msgs : set<Msg>, msgType : MsgType, view : nat) : set<Msg>
    {
        set m | && m in msgs
                && m.mType == msgType
                && m.viewNum == view
    }

    // method ExtractSignatrues(msgs : set<Msg>) returns (sgns : set<Signature>)
    // {
    //     sgns := {};
    //     var remaining := msgs;
    //     while remaining != {}
    //         decreases |remaining|
    //     {
    //         var m :| m in remaining;
    //         sgns := sgns + {m.partialSig};
    //         remaining := remaining - {m};
    //     }
    // }

    function ExtractSignatrues(msgs : set<Msg>) : set<Signature>


    ghost function getMatchQC(msgs : set<Msg>, msgType : MsgType, view : nat) : set<Cert>
    {
        // set qc | qc in msg.justify ::
        //                 && qc.mType == msgType
        //                 && qc.viewNum == view
        set m | && m in msgs 
                && m.justify.Cert?
                && m.justify.cType == msgType    
                && m.justify.viewNum == view
              ::
                m.justify
    }

    function getHighQC(msgs : set<Msg>) : Cert
    ensures getHighQC(msgs).Cert?
    ensures getHighQC(msgs).block.Block?

    function getNewBlock(parent : Block) : Block
    requires parent.Block?
    ensures getNewBlock(parent).Block?
    ensures {:axiom}getNewBlock(parent).parent == parent

    function getAncestors(b : Block) : set<Block>
    requires b.Block?
    {
        match (b.parent != EmptyBlock){
            case true => {b} + getAncestors(b.parent)
            case false => {b}
        }
    }

    predicate extension(child : Block, parent : Block)
    requires child.Block?
    {
        parent in getAncestors(child)
    }

    predicate safeNode(block : Block, qc : Cert, lockedQC : Cert)
    requires block.Block? && lockedQC.Cert? && qc.Cert?
    {
        || extension(block, lockedQC.block)
        || qc.viewNum > lockedQC.viewNum
    }

    function Multicast(m : Msg, recipients : set<Address>) : set<MsgWithRecipient>
    {
        set r | r in recipients :: MsgWithRecipient(m, r)
    }

    predicate NoConflict(b1 : Block, b2 : Block)
    requires b1.Block? && b2.Block?
    {
        || b1 == b2
        || extension(b1, b2)
        || extension(b2, b1)
    }

    /**
     * A valid Quorum Certificate should hold the following constraints
     */
    predicate ValidQC(qc : Cert)
    // requires qc.Cert?
    {
        && qc.Cert?
        && (forall s | s in qc.signatures
                    ::  && s.Signature?
                        && s.mType == qc.cType
                        && s.viewNum == qc.viewNum
                        && s.block == qc.block
                        && s.signer in All_Nodes
            )
        && (forall s1, s2 | s1 in qc.signatures && s2 in qc.signatures
                         :: s1.signer != s2.signer
                         )
        && |qc.signatures| >= quorum(|All_Nodes|)
    }

    function getVotesInValidQC(qc : Cert) : (votes: set<Signature>)
    requires ValidQC(qc)
    ensures |votes| >= quorum(|All_Nodes|)
    {
        qc.signatures
    }

    function getMajoritySignerInValidQC(qc : Cert) : (ret : set<Address>)
    requires ValidQC(qc)
    ensures forall s | s in qc.signatures :: s.signer in All_Nodes
    ensures |ret| >= quorum(|All_Nodes|)
    {
        var votes := getVotesInValidQC(qc);
        set vote | vote in votes
                    :: vote.signer
    }

}