include "Type.dfy"
include "Adversary.dfy"
include "Replica.dfy"

module M_System {

    import opened M_SpecTypes
    import opened M_Replica
    import opened M_Adversary


    datatype SystemState = SystemState(
        configuration : Configuration,
        nodes : map<Address, ReplicaState>,
        adversary : Adversary
    )

    predicate IsHonest(ss : SystemState, r : Address)
    {
        r in ss.nodes.Keys - ss.adversary.nodes
    }

    predicate SystemInit(ss : SystemState, c : Configuration)
    {
        && (forall r | r in ss.nodes :: ReplicaInit(ss.nodes[r], r, c))
        && AdversaryInit(ss.adversary, ss.nodes.Keys)
    }

    predicate SystemNextByOneReplica(ss : SystemState, ss' : SystemState, r : Address, outMsg : set<MsgWithRecipient>)
    {
        && (
            if IsHonest(ss, r) then
                ReplicaNext(ss.nodes[r], ss'.nodes[r])
            else
                AdversaryNext(ss.adversary, ss'.adversary)
        )
    }

    ghost predicate SystemNext(ss : SystemState, ss' : SystemState, outMsg : set<MsgWithRecipient>)
    {
        || ss == ss'
        || (exists r :: SystemNextByOneReplica(ss, ss', r, outMsg))
    }
}