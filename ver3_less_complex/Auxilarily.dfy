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
    function quorum(setSize : nat) : nat
    {
        (setSize*2 - 1) / 3 + 1
    }  

    function leader(round : nat, c : Configuration) : Address

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

    predicate ValidQC(qc : Cert)
    requires qc.Cert?
    {
        var sgns := qc.signatures;
        forall s | s in sgns
                :: && s.Signature?
                   && s.mType == qc.cType
                   && s.viewNum == qc.viewNum
                   && s.block == qc.block
    }
}