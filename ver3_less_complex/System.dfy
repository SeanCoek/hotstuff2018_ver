include "Type.dfy"
include "Adversary.dfy"
include "Replica.dfy"
include "Auxilarily.dfy"
include "Axioms.dfy"
include "Invariants.dfy"

module M_System {

    import opened M_SpecTypes
    import opened M_Replica
    import opened M_Adversary
    import opened M_AuxilarilyFunc
    import opened M_Axiom
    import opened M_Invariants

    /**
     * Definition of a system state
     * @param nodeStates -> a map storing node states, using node address as key
     * @param adversary -> structure for Byzantine nodes
     * @param msgSent -> all message sent by replicas
     */
    datatype SystemState = SystemState(
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

    predicate Inv_Node_System(ss : SystemState)
    {
        && Inv_Node_Constraint()
        && ss.nodeStates.Keys == M_SpecTypes.All_Nodes
        && ss.adversary.byz_nodes == M_SpecTypes.Adversary_Nodes
    }

    ghost predicate ValidSystemState(ss : SystemState)
    {
        NoOuterClient();
        && Inv_Node_System(ss)
        && (forall replica | replica in ss.nodeStates.Keys :: ss.nodeStates[replica].msgSent <= ss.msgSent)
        && (forall replica | IsHonest(ss, replica) :: ValidReplicaState(ss.nodeStates[replica]))
        && (forall replica | IsHonest(ss, replica) :: ss.nodeStates[replica].msgReceived <= ss.msgSent)

        // && forall m | m in ss.msgSent && IsHonest(ss, m.sender)
        //            :: m in ss.nodeStates[m.sender].msgSent
    }

    // lemma LemmaInitialSystemStateHoldsValidity(ss : SystemState)
    // requires SystemInit(ss)
    // ensures ValidSystemState(ss)
    // {

    // }

    // lemma LemmaSystemTransitionHoldsValidity(ss : SystemState, ss' : SystemState)
    // requires ValidSystemState(ss)
    // requires SystemNext(ss, ss')
    // ensures ValidSystemState(ss')
    // {
    //     // Prove a valid state after system transition will still be valid
    //     if ss == ss' {
    //         assert ValidSystemState(ss');
    //     }
    //     else {
    //         // assert false;
    //         forall replica, msgReceivedByNodes, msgSentByNodes
    //                 | && msgReceivedByNodes <= ss.msgSent
    //                   && SystemNextByOneReplica(ss, ss', replica, msgReceivedByNodes, msgSentByNodes)
    //         ensures ValidSystemState(ss') {
    //             LemmaSystemNextByOneReplicaIsValid(ss, ss', replica, msgReceivedByNodes, msgSentByNodes);
    //         }
    //     }
    // }

    // lemma LemmaReplicaMsgReceivedMustBeSent(
    //     ss : SystemState,
    //     ss' : SystemState
    // )
    // requires ValidSystemState(ss)
    // requires SystemNext(ss, ss')
    // ensures forall r | IsHonest(ss', r) :: ss'.nodeStates[r].msgReceived <= ss'.msgSent
    // {
    //     if ss == ss' {

    //     }
    //     else {
    //         // assert false;
    //         var replica, msgReceivedByNodes, msgSentByNodes
    //                :|   && msgReceivedByNodes <= ss.msgSent
    //                     && SystemNextByOneReplica(ss, ss', replica, msgReceivedByNodes, msgSentByNodes);
    //         LemmaSystemNextByOneReplicaIsValid(ss, ss', replica, msgReceivedByNodes, msgSentByNodes);
    //     }
    // }

    // lemma LemmaInvNodeInSystemNextByOneReplica(
    //     ss : SystemState, 
    //     ss' : SystemState, 
    //     replica : Address,
    //     inMsg : set<Msg>,
    //     outMsg : set<Msg>)
    // requires ValidSystemState(ss)
    // requires inMsg <= ss.msgSent
    // requires SystemNextByOneReplica(ss, ss', replica, inMsg, outMsg)
    // ensures Inv_Node_System(ss')
    // {

    // }

    // lemma LemmaHonestReplicaIsValidInSystemNextByOneReplica(
    //     ss : SystemState, 
    //     ss' : SystemState, 
    //     replica : Address,
    //     inMsg : set<Msg>,
    //     outMsg : set<Msg>)
    // requires ValidSystemState(ss)
    // requires inMsg <= ss.msgSent
    // requires SystemNextByOneReplica(ss, ss', replica, inMsg, outMsg)
    // ensures forall r | IsHonest(ss', r) :: ValidReplicaState(ss'.nodeStates[r])
    // {
    //     if IsHonest(ss, replica) {
    //         LemmaReplicaNextIsValid(ss.nodeStates[replica],
    //                                 inMsg,
    //                                 ss'.nodeStates[replica],
    //                                 outMsg);
    //     }
    // }

    // lemma LemmaHonestSentMsgCapturedBySystemInSystemNextByOneReplica(
    //         ss : SystemState, 
    //         ss' : SystemState, 
    //         replica : Address,
    //         inMsg : set<Msg>,
    //         outMsg : set<Msg>)
    // requires ValidSystemState(ss)
    // requires inMsg <= ss.msgSent
    // requires SystemNextByOneReplica(ss, ss', replica, inMsg, outMsg)
    // ensures forall m | m in outMsg && IsHonest(ss', m.sender) :: m in ss'.nodeStates[m.sender].msgSent
    // {
    //     if IsHonest(ss, replica) {
    //         var r := ss.nodeStates[replica];
    //         var r' := ss'.nodeStates[replica];
    //         // LemmaMsgRelationInReplicaNext(rState, inMsg, rState', outMsg);
    //         LemmaMsgSentWithBySameReplicaInReplicaNext(r, inMsg, r', outMsg);
    //         assert forall m | m in outMsg :: m.sender == replica;
    //     }
    //     // else {
            
    //     // }
    // }

    // lemma LemmaHonestReplicaMsgReceivedIsSubsetOfSystemMsgSentInSystemNextByOneReplica(
    //     ss : SystemState, 
    //     ss' : SystemState, 
    //     replica : Address,
    //     inMsg : set<Msg>,
    //     outMsg : set<Msg>)
    // requires ValidSystemState(ss)
    // requires inMsg <= ss.msgSent
    // requires SystemNextByOneReplica(ss, ss', replica, inMsg, outMsg)
    // ensures forall r | IsHonest(ss', r) :: ss'.nodeStates[r].msgReceived <= ss'.msgSent
    // {
    //     if IsHonest(ss, replica) {
    //         var rState := ss.nodeStates[replica];
    //         var rState' := ss'.nodeStates[replica];
    //         LemmaMsgRelationInReplicaNext(rState, inMsg, rState', outMsg);
    //     }
    // }

    // lemma LemmaReplicaMsgSentIsSubsetOfSystemMsgSentInSystemNextByOneReplica(
    //     ss : SystemState, 
    //     ss' : SystemState, 
    //     replica : Address,
    //     inMsg : set<Msg>,
    //     outMsg : set<Msg>)
    // requires ValidSystemState(ss)
    // requires inMsg <= ss.msgSent
    // requires SystemNextByOneReplica(ss, ss', replica, inMsg, outMsg)
    // ensures forall r | r in ss'.nodeStates.Keys :: ss'.nodeStates[r].msgSent <= ss'.msgSent
    // {
    //     if IsHonest(ss, replica) {
    //         var rState := ss.nodeStates[replica];
    //         var rState' := ss'.nodeStates[replica];
    //         LemmaMsgRelationInReplicaNext(rState, inMsg, rState', outMsg);
    //         assert rState'.msgSent <= ss'.msgSent;
    //     }
    //     else {
    //         forall r_byz | r_byz in ss.adversary.byz_nodes
    //         ensures ss'.nodeStates[r_byz].msgSent <= ss'.msgSent {
    //             var byzState := ss.nodeStates[r_byz];
    //             var byzState' := ss'.nodeStates[r_byz];
    //             // assert forall r | r in ss.nodeStates.Keys :: ss.nodeStates[r].msgSent <= ss.msgSent by {
    //             //     assert ValidSystemState(ss);
    //             // }
    //             assert byzState'.msgSent <= ss'.msgSent;
    //         }
    //     }
    // }

    // lemma LemmaSystemNextByOneReplicaIsValid(
    //     ss : SystemState, 
    //     ss' : SystemState, 
    //     replica : Address,
    //     inMsg : set<Msg>,
    //     outMsg : set<Msg>)
    // requires ValidSystemState(ss)
    // requires inMsg <= ss.msgSent
    // requires SystemNextByOneReplica(ss, ss', replica, inMsg, outMsg)
    // ensures ValidSystemState(ss')
    // {
    //     LemmaInvNodeInSystemNextByOneReplica(ss, ss', replica, inMsg, outMsg);
    //     LemmaReplicaMsgSentIsSubsetOfSystemMsgSentInSystemNextByOneReplica(ss, ss', replica, inMsg, outMsg);
    //     LemmaHonestReplicaIsValidInSystemNextByOneReplica(ss, ss', replica, inMsg, outMsg);
    //     LemmaHonestReplicaMsgReceivedIsSubsetOfSystemMsgSentInSystemNextByOneReplica(ss, ss', replica, inMsg, outMsg);
    // }

    /**
     * Definition of initial state of system
     */
    ghost predicate SystemInit(ss : SystemState)
    // ensures ValidSystemState(ss)
    {
        && Inv_Node_System(ss)
        && ss.msgSent == getMultiInitialMsg(ss.nodeStates.Keys)
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
    requires ValidSystemState(ss)
    {
        && var msgReceivedSingleSet := set mr:Msg | mr in inMsg;
        && replica in ss.nodeStates.Keys
        // fixed set of replica
        && ss.nodeStates.Keys == ss'.nodeStates.Keys
        // separate different actions by replica's honesty
        && (
            if IsHonest(ss, replica) then
                && ss'.nodeStates == ss.nodeStates[replica := ss'.nodeStates[replica]]
                && ss'.adversary == ss.adversary
                && ReplicaNext(ss.nodeStates[replica], msgReceivedSingleSet, ss'.nodeStates[replica], outMsg)
            else
                // && ss'.nodeStates == ss.nodeStates
                // assert replica in ss.adversary.byz_nodes;
                && AdversaryNext(ss.adversary, msgReceivedSingleSet, ss'.adversary, outMsg)
                && (forall r | r in ss.adversary.byz_nodes
                            :: && ss'.nodeStates[r].msgReceived == ss.nodeStates[r].msgReceived + msgReceivedSingleSet
                               && ss'.nodeStates[r].msgSent == ss.nodeStates[r].msgSent + outMsg
                )
                && (forall r | IsHonest(ss, r)
                            :: ss'.nodeStates[r] == ss.nodeStates[r])
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
        || (exists replica, msgReceivedByNodes, msgSentByNodes
                   | msgReceivedByNodes <= ss.msgSent
                  :: SystemNextByOneReplica(ss, ss', replica, msgReceivedByNodes, msgSentByNodes))
    }
}