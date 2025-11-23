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
        && forall replica | IsHonest(ss, replica) :: ss.nodeStates[replica].msgReceived <= ss.msgSent
        && forall replica | replica in ss.nodeStates.Keys :: ss.nodeStates[replica].msgSent <= ss.msgSent
        // && forall m | m in ss.msgSent
        //            :: (exists r | r in ss.nodeStates.Keys
        //                        :: m in ss.nodeStates[r].msgSent)
    }

    lemma LemmaInitialSystemStateHoldsValidity(ss : SystemState)
    requires SystemInit(ss)
    ensures ValidSystemState(ss)
    {

    }

    lemma LemmaSystemTransitionHoldsValidity(ss : SystemState, ss' : SystemState)
    requires ValidSystemState(ss)
    requires SystemNext(ss, ss')
    ensures ValidSystemState(ss')
    {
        // Prove a valid state after system transition will still be valid
        if ss == ss' {
            assert ValidSystemState(ss');
        }
        else {
            forall replica, msgReceivedByNodes, msgSentByNodes
                    | && msgReceivedByNodes <= ss.msgSent
                      && SystemNextByOneReplica(ss, ss', replica, msgReceivedByNodes, msgSentByNodes)
            ensures ValidSystemState(ss') {
                LemmaSystemNextByOneReplicaIsValid(ss, ss', replica, msgReceivedByNodes, msgSentByNodes);
            }
        }
    }

    lemma LemmaReplicaMsgReceivedMustBeSent(
        ss : SystemState,
        ss' : SystemState
    )
    requires ValidSystemState(ss)
    requires SystemNext(ss, ss')
    ensures forall r | IsHonest(ss', r) :: ss'.nodeStates[r].msgReceived <= ss'.msgSent
    {
        if ss == ss' {

        }
        else {
            var replica, msgReceivedByNodes, msgSentByNodes
                   :|   && msgReceivedByNodes <= ss.msgSent
                        && SystemNextByOneReplica(ss, ss', replica, msgReceivedByNodes, msgSentByNodes);
            LemmaSystemNextByOneReplicaIsValid(ss, ss', replica, msgReceivedByNodes, msgSentByNodes);
        }
    }

    lemma LemmaSystemMsgSentIsUnionOfAllMsgSentInReplicaNext()


    lemma LemmaSystemNextByOneReplicaIsValid(
        ss : SystemState, 
        ss' : SystemState, 
        replica : Address,
        inMsg : set<Msg>,
        outMsg : set<Msg>)
    requires ValidSystemState(ss)
    requires inMsg <= ss.msgSent
    requires SystemNextByOneReplica(ss, ss', replica, inMsg, outMsg)
    ensures ValidSystemState(ss')
    {
        var r := ss.nodeStates[replica];
        var r' := ss'.nodeStates[replica];
        if IsHonest(ss, replica) {
            var msgReceivedSingleSet := set mr | mr in inMsg;
            LemmaReplicaNextIsValid(r,
                                msgReceivedSingleSet,
                                r',
                                outMsg);
            assert ValidReplicaState(r');

            assert ReplicaNext(r, msgReceivedSingleSet, r', outMsg);
            assert r'.msgReceived >= r.msgReceived + msgReceivedSingleSet by {
                LemmaMsgRelationInReplicaNext(r, 
                                                msgReceivedSingleSet, 
                                                r', 
                                                outMsg);
            }
            assert r'.msgReceived <= ss'.msgSent by {
                assert ss'.msgSent == ss.msgSent + outMsg;
                LemmaMsgRelationInReplicaNext(r, msgReceivedSingleSet, r', outMsg);
                assert r'.msgReceived - r.msgReceived <= outMsg;
            }
            assert r'.msgSent <= ss'.msgSent by {
                assert ss'.msgSent == ss.msgSent + outMsg;
                LemmaMsgRelationInReplicaNext(r, msgReceivedSingleSet, r', outMsg);
                assert r'.msgSent == r.msgSent + outMsg;
                assert r.msgSent <= ss.msgSent by {
                    assert ValidSystemState(ss);
                }
            }
        }
        else {
            // assert ValidSystemState(ss');
        }
    }

    /**
     * Definition of initial state of system
     */
    ghost predicate SystemInit(ss : SystemState)
    // ensures ValidSystemState(ss)
    {
        && Inv_Node_Constraint(ss)
        && ss.msgSent == {}
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