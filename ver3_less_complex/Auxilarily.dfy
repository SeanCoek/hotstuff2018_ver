include "Type.dfy"
include "common/sets.dfy"

module M_AuxilarilyFunc {
    import opened M_SpecTypes
    import opened M_Set
    import opened Std.Collections.Seq
    import opened Std.Collections.Set

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
    function quorum(setSize : nat) : (r: nat)
    // requires setSize > 0
    ensures r <= setSize
    {
        // 2*(setSize - 1) / 3 + 1
        // 2 * f(setSize) + 1
        // if setSize <= 3
        // then 
        //     setSize - f(setSize) + 1
        // else
        //     2 * f(setSize) + 1
        if setSize == 0 then 0 else setSize - f(setSize)
    }  

    lemma LemmaTwoQuorumIntersection(
                                    allNodes : set<Address>,
                                    byzNodes : set<Address>,
                                    q1 : set<Address>,
                                    q2 : set<Address>)
    requires |allNodes| > 0
    requires q1 <= allNodes && |q1| >= quorum(|allNodes|)
    requires q2 <= allNodes && |q2| >= quorum(|allNodes|)
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
            >=
            2 * quorum(|allNodes|) - |byzNodes| - |allNodes|;
            >=
            2 * quorum(|allNodes|) - f(|allNodes|) - |allNodes|;
            >=
            1;

            // 2 * (2*f + 1) - f - n
            // 2 * (2 * (n-1)/3 + 1) - (n-1)/3 - n

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

    function getMatchMsg(msgs : set<Msg>, msgType : MsgType, view : nat) : (r : set<Msg>)
    ensures forall m | m in r :: m in msgs && m.mType == msgType && m.viewNum == view
    ensures forall m | m in msgs :: (m.mType == msgType && m.viewNum == view) ==> m in r
    // {
    //     set m | && m in msgs
    //             && m.mType == msgType
    //             && m.viewNum == view
    // }

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

    function ExtractSignatrues(msgs : set<Msg>) : (r : set<Signature>)
    ensures |r| == |msgs|
    ensures forall s | s in r :: exists m | m in msgs :: m.partialSig == s


    ghost function getMatchQC(msgs : set<Msg>, msgType : MsgType, view : nat) : (r : set<Cert>)
    ensures forall c | c in r :: c.Cert? && c.cType == msgType && c.viewNum == view
    ensures forall c | c in r :: exists m | m in msgs :: m.justify == c
    ensures forall c | c in r :: ValidQC(c)
    // {
    //     set m | && m in msgs 
    //             && m.justify.Cert?
    //             && m.justify.cType == msgType    
    //             && m.justify.viewNum == view
    //             && ValidQC(m.justify)
    //           ::
    //             m.justify
    // }

    function getHighQC(msgs : set<Msg>) : (r : Cert)
    ensures r.Cert?
    ensures r.block.Block?
    ensures forall m | m in msgs :: m.justify.Cert? ==> r.viewNum >= m.justify.viewNum
    ensures exists m | m in msgs :: m.justify == r

    function getNewBlock(parent : Block) : (r : Block)
    ensures r.Block?
    ensures r.parent == parent
    ensures r.parent != r

    function getAncestors(b : Block) : (r : seq<Block>)
    // requires b.Block?
    // ensures b.parent.Block? ==> |r| > 0 && r[|r|-1] == b
    ensures |r| > 0 && r[|r|-1] == b
    ensures forall i | 0 <= i < |r| :: r[i].Block?
    ensures forall i, j | 0 <= i < j < |r| :: r[i] != r[j]  // None duplication
    ensures forall i | 0 <= i < |r|-1 :: r[i] == r[i+1].parent
    // {
    //     match (b.Block?) {
    //         case true =>
    //                     match (b.parent != EmptyBlock){
    //                         case true => getAncestors(b.parent) + [b.parent]
    //                         // case false => [b]
    //                         case false => []
    //                     }
    //         case false => []
    //     }
    // }

    predicate extension(child : Block, parent : Block)
    requires child.Block?
    {
        // && child.Block?
        // parent in getAncestors(child)
        getAncestors(parent) <= getAncestors(child)
        // Seq.IsPrefix(getAncestors(parent), getAncestors(child))
    }

    lemma Lemma_AncestorOfParentIsPrefixOfAncestorOfChild(child : Block, parent : Block)
    requires child.Block? && parent.Block?
    requires extension(child, parent)
    ensures Seq.IsPrefix(getAncestors(parent), getAncestors(child))
    {
        // var acstr_p, acstr_c := getAncestors(parent), getAncestors(child);
        // assert parent in acstr_c;
        // assert parent == acstr_p[|acstr_p|-1];
        // assert acstr_p <= acstr_c by {
        //     if |acstr_c| == 2 {
        //         assert acstr_c == [parent, child] by {
        //             assert |acstr_c| == 2;
        //             assert parent in acstr_c;
        //             assert child == acstr_c[|acstr_c|-1];
        //             assert forall i, j | 0 <= i < j < |acstr_c| :: acstr_c[i] != acstr_c[j];
                
        //         }
        //     }
        // }
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
     * Refer to the function "tverify(<qc.type, qc.view, qc.node>, qc.sig)" described in the paper
     * It is supposed to be a threshold decryption
     */
    predicate ValidQC(qc : Cert)
    // requires qc.Cert?
    // requires |All_Nodes| > 0
    {
        && |All_Nodes| > 0
        && qc.Cert?
        && qc.block.Block?
        && (forall s | s in qc.signatures
                    ::  && s.Signature?
                        && s.mType == qc.cType
                        && s.viewNum == qc.viewNum
                        && s.block == qc.block
                        && s.signer in All_Nodes
            )
        && (forall s1, s2 | && s1 in qc.signatures 
                            && s2 in qc.signatures
                            && s1 != s2
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

    function splitMsgByBlocks(msgs : set<Msg>) : (r : set<set<Msg>>)
    ensures |msgs| > 0 ==> |r| > 0
    ensures forall mset | mset in r :: mset <= msgs
    ensures forall mset1, mset2 | mset1 in r && mset2 in r :: (mset1 != mset2) ==> |mset1 * mset2| == 0
    ensures (forall mset | mset in r :: (forall m1, m2 | m1 in mset && m2 in mset :: m1.block == m2.block))
    // {
    //     set m | 
    //             && m <= msgs
    //             && (forall e1, e2 | e1 in m && e2 in m
    //                                 :: e1.block == e2.block)
    // }

    function getMaxLengthSet<T>(sets : set<set<T>>) : (r : set<T>)
    ensures r in sets
    ensures forall s | s in sets :: |r| >= |s|


    function argmin<T>(s: set<T>, f: T -> int) : (ret : T)
    requires s != {}
    ensures forall x :: x in s ==> f(ret) <= f(x)
    ensures ret in s
    {
        // var min :| min in s && forall x :: x in s ==> f(min) <= f(x);
        // min
        var min :| min in s;
        min
        // var remaining := s - {min};
        // if remaining != {}
        // {
        //     var y := argmin(remaining, f);
        //     ret := if y <= min then y else min;
        // }
        // else
        // {
        //     assert remaining == {};
        //     out := min;
        // }
    }

    function argminView(s: set<Msg>) : (ret : Msg)
    requires s != {}
    requires forall x | x in s :: x.justify.Cert?
    ensures forall x :: x in s ==> ret.justify.viewNum <= x.justify.viewNum
    ensures ret in s
    {
        var min :| min in s && forall x :: x in s ==> min.justify.viewNum <= x.justify.viewNum;
        min
    }

    function argmax<T>(s: set<T>, f: T -> int) : (ret : T)
    requires s != {}
    ensures forall x :: x in s ==> f(ret) >= f(x)
    ensures ret in s
    {
        var max :| max in s && forall x :: x in s ==> f(max) >= f(x);
        max
    }

}