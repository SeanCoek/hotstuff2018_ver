include "Type.dfy"
include "Adversary.dfy"
include "Replica.dfy"

module M_System {

    import opened M_SpecTypes
    import opened M_Replica
    import opened M_Adversary

    /**
     * Definition of a system state
     * @param configuration -> infomations about system settings, such like node address, genesis block, etc.
     * @param nodeStates -> a map storing node states, using node address as key
     * @param adversary -> structure for Byzantine nodes
     */
    datatype SystemState = SystemState(
        configuration : Configuration,
        nodeStates : map<Address, ReplicaState>,
        adversary : Adversary
    )

    /**
     * Replicas not in adversary are considered as an honest node
     * return `true` if and only if replica exists in the set of all nodes and not in the set of Byzantine nodes.
     */
    predicate IsHonest(ss : SystemState, r : Address)
    {
        r in ss.nodeStates.Keys - ss.adversary.byz_nodes
    }

    ghost predicate ValidSystemState(ss : SystemState)
    {
        forall replica | IsHonest(ss, replica) :: ValidReplicaState(ss.nodeStates[replica])
    }

    /**
     * Definition of initial state of system
     */
    predicate SystemInit(ss : SystemState, c : Configuration)
    {
        && (forall r | r in ss.nodeStates :: ReplicaInit(ss.nodeStates[r], r, c))
        && AdversaryInit(ss.adversary, c)
    }


    /**
     * Definiton of system state transition triggered by a particular node
     * @param ss -> current system state
     * @param ss' -> next system state
     * @param replica -> address of the node causing this state transition
     * @param inMsg -> messages recieved by this node
     * @param outMsg -> messages sent when state transition happens
     */
    predicate SystemNextByOneReplica(
        ss : SystemState, 
        ss' : SystemState, 
        replica : Address, 
        inMsg: multiset<MsgWithRecipient>,
        outMsg : set<MsgWithRecipient>)
    {
        && (forall mr:MsgWithRecipient | mr in inMsg :: mr.recipient == replica)
        && var msgRecievedSingleSet := set mr:MsgWithRecipient | mr in inMsg :: mr.msg;
        && replica in ss.nodeStates
        && ss.nodeStates.Keys == ss'.nodeStates.Keys
        && (
            if IsHonest(ss, replica) then
                && ss'.nodeStates == ss.nodeStates[replica := ss'.nodeStates[replica]]
                && ss'.adversary == ss.adversary
                && ReplicaNext(ss.nodeStates[replica], ss'.nodeStates[replica], outMsg)
            else
                && ss'.nodeStates == ss.nodeStates
                && AdversaryNext(ss.adversary, msgRecievedSingleSet, ss'.adversary, outMsg)
        )
        && ss'.configuration == ss.configuration
    }

    /**
     * Definition of transition state of system
     * @param ss -> current system state
     * @param ss' -> next system state
     */
    ghost predicate SystemNext(ss : SystemState, ss' : SystemState)
    {
        || ss == ss'
        || (exists replica,
                   msgRecievedByNodes,
                   msgSentByNodes
                     :: SystemNextByOneReplica(ss, ss', replica, msgRecievedByNodes, msgSentByNodes))
    }
}