include "Type.dfy"
include "Adversary.dfy"
include "Replica.dfy"
include "Auxilarily.dfy"

module M_System {

    import opened M_SpecTypes
    import opened M_Replica
    import opened M_Adversary
    import opened M_AuxilarilyFunc

    /**
     * Definition of a system state
     * @param configuration -> infomations about system settings, such like node address, genesis block, etc.
     * @param nodeStates -> a map storing node states, using node address as key
     * @param adversary -> structure for Byzantine nodes
     * @param msgSent -> all message sent by replicas
     */
    datatype SystemState = SystemState(
        // configuration : Configuration,
        nodeStates : map<Address, ReplicaState>,
        adversary : Adversary,
        msgSent : set<Msg>
    )

    /**
     * Replicas not in adversary are considered as an honest node
     * return `true` if and only if replica exists in the set of all nodes and not in the set of Byzantine nodes.
     */
    predicate IsHonest(ss : SystemState, r : Address)
    {
        r in ss.nodeStates.Keys - ss.adversary.byz_nodes
        // r in M_SpecTypes.Honest_Nodes
    }

    predicate Inv_Node_Constraint(ss : SystemState)
    {
        && |M_SpecTypes.All_Nodes| > 0
        && |Adversary_Nodes| <= f(|All_Nodes|)
        && M_SpecTypes.Honest_Nodes * M_SpecTypes.Adversary_Nodes == {}
        && ss.nodeStates.Keys == M_SpecTypes.All_Nodes
        && ss.adversary.byz_nodes == M_SpecTypes.Adversary_Nodes
    }

    ghost predicate ValidSystemState(ss : SystemState)
    {
        && Inv_Node_Constraint(ss)
        && forall replica | IsHonest(ss, replica) :: ValidReplicaState(ss.nodeStates[replica])
    }

    lemma LemmaInitialSystemStateHoldsValidity(ss : SystemState)
    requires SystemInit(ss)
    ensures ValidSystemState(ss)
    {
        // Replica initialization would not change configuration
        // calc {
        //     forall r | r in ss.nodeStates
        //                     :: 
        //                     && ReplicaInit(ss.nodeStates[r], r)
        //                     && ReplicaInit(ss.nodeStates[r], r)
        //     ;
        //     // ==>
        //     // c1 == c2;
        // }

    //    assert Inv_Constant_Fields(ss);
    }

    lemma LemmaSystemTransitionHoldsValidity(ss : SystemState, ss' : SystemState)
    requires ValidSystemState(ss)
    requires SystemNext(ss, ss')
    ensures ValidSystemState(ss')
    {
        // Prove a valid state after system transition will still be valid
    }

    /**
     * Definition of initial state of system
     */
    ghost predicate SystemInit(ss : SystemState)
    // ensures ValidSystemState(ss)
    {
        && Inv_Node_Constraint(ss)
        // && ValidSystemState(ss)
        && ss.nodeStates.Keys == M_SpecTypes.All_Nodes
        && (forall r | r in ss.nodeStates :: ReplicaInit(ss.nodeStates[r], r))
        && AdversaryInit(ss.adversary)
    }


    /**
     * Definiton of system state transition triggered by a particular node
     * @param ss -> current system state
     * @param ss' -> next system state
     * @param replica -> address of the node causing this state transition
     * @param inMsg -> messages recieved by this node
     * @param outMsg -> messages sent when state transition happens
     */
    ghost predicate SystemNextByOneReplica(
        ss : SystemState, 
        ss' : SystemState, 
        replica : Address, 
        // inMsg: multiset<Msg>,
        inMsg : set<Msg>,
        outMsg : set<Msg>)
    {
        && var msgRecievedSingleSet := set mr:Msg | mr in inMsg;
        && replica in ss.nodeStates
        // fixed set of replica
        && ss.nodeStates.Keys == ss'.nodeStates.Keys
        // separate different actions by replica's honesty
        && (
            if IsHonest(ss, replica) then
                && ss'.nodeStates == ss.nodeStates[replica := ss'.nodeStates[replica]]
                && ss'.adversary == ss.adversary
                && ReplicaNext(ss.nodeStates[replica], msgRecievedSingleSet, ss'.nodeStates[replica], outMsg)
            else
                && ss'.nodeStates == ss.nodeStates
                && AdversaryNext(ss.adversary, msgRecievedSingleSet, ss'.adversary, outMsg)
        )
        && ss.adversary.byz_nodes == ss'.adversary.byz_nodes
        && ss'.msgSent == ss.msgSent + outMsg
    }

    /**
     * Definition of transition state of system
     * @param ss -> current system state
     * @param ss' -> next system state
     */
    ghost predicate SystemNext(ss : SystemState, ss' : SystemState)
    requires ValidSystemState(ss)
    // ensures ValidSystemState(ss')
    {
        || ss == ss'
        || (exists replica, msgRecievedByNodes, msgSentByNodes
                   | msgRecievedByNodes <= ss.msgSent
                  :: SystemNextByOneReplica(ss, ss', replica, msgRecievedByNodes, msgSentByNodes))
    }
}