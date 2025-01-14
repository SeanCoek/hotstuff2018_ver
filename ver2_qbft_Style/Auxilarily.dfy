include "Type.dfy"

module M_AuxilarilyFunc {
    import opened M_SpecTypes

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
    {
        c.nodes[round % |c.nodes|]
    }

    function getMatchMsg(msgs : set<Msg>, msgType : MsgType, view : nat) : set<Msg>
    {
        set m | m in msgs :: 
                    && m.mType == msgType
                    && m.viewNum == view
    }

    function getMatchQC(msgs : set<Msg>, msgType : MsgType, view : nat) : set<Msg>
    {
        set qc | qc in msg.justify ::
                        && qc.mType == msgType
                        && qc.viewNum == view
    }

    method getHighQC(msgs : set<Msg>) returns (qc : Cert)

    function getNewBlock(parent : Block) : Block
    ensures getNewBlock(parent).parent == parent

    function getAncestors(b : Block) : set<Block>
    {
        match (b.parent != EmptyBlock){
            case true => {b} + getAncestors(b.parent)
            case false => {b}
        }
    }

    predicate extension(child : Block, parent : Block)
    {
        parent in getAncestors(child)
    }

    predicate safeNode(node : Block, qc : Cert, lockedQC : Cert)
    {
        || extension(node, lockedQC.node)
        || qc.viewNum > lockedQC.viewNum
    }

    function Multicast(m : Msg, recipients : set<Address>) : set<MsgWithRecipient>
    {
        set r | r in recipients :: MsgWithRecipient(m, r)
    }
}