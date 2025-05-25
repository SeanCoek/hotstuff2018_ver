include "Type.dfy"
include "Auxilarily.dfy"

module M_Adversary {
    import opened M_SpecTypes
    import opened M_AuxilarilyFunc

    /**
     * Definition of Byzantine nodes. We group all Byzantine nodes as a adversary.
     * @param byz_nodes -> ID of all Byzantine nodes
     * @param msgRecieved -> Messages recieved by all Byzantine nodes
     */
    datatype Adversary = Adversary(
        byz_nodes : set<Address>,
        msgRecieved : set<Msg>
    )

    /**
     * Initial state of adversary
     */
    predicate AdversaryInit(a : Adversary)
    {
        && a.byz_nodes == M_SpecTypes.Adversary_Nodes
        && a.byz_nodes <= M_SpecTypes.All_Nodes  // byzantine nodes should exists in the set of all nodes.
        && |a.byz_nodes| <= f(|M_SpecTypes.All_Nodes|)    // the counts of byzantine nodes should not exceed 1/3 of all nodes.
    }

    /**
     * Definiton of transition state for adversary
     * @param a -> current(or old) state of adversary
     * @param inMsg -> Messages recieved by current adversary
     * @param a' -> next(or new) state of adversary
     * @param outMsg -> Messages sent by current adversary when state transition happens.
     */
    predicate AdversaryNext(
        a : Adversary, 
        inMsg : set<Msg>,
        a' : Adversary, 
        // outMsg : set<MsgWithRecipient>
        outMsg : set<Msg>
        )
    {
        var msgRecieved := a.msgRecieved + inMsg;
        && a' == a.(
            msgRecieved := msgRecieved
        )
        && (forall m | m in outMsg ::
                    || m in msgRecieved // keep the recieved message unchanged and forward to other nodes.
                    // TODO: further faulty behavirous can be updated here, using disjunction `||`
            )
    }
}