include "Type.dfy"
include "System.dfy"
include "Trace.dfy"
include "Invariants.dfy"
include "Replica.dfy"

module M_Thereom {
    import opened M_SpecTypes
    import opened M_System
    import opened M_Trace
    import opened M_Invariants
    import opened M_Replica

    predicate consistentBlockchains(bc1 : Blockchain, bc2 : Blockchain)
    {
        || bc1 <= bc2
        || bc2 <= bc1
    }

    ghost predicate consistency(t : Trace)
    {
        forall i, r1, r2 |
                    && IsHonest(t(i), r1)
                    && IsHonest(t(i), r2)
                :: consistentBlockchains(t(i).nodeStates[r1].bc, t(i).nodeStates[r2].bc)
    }

    ghost predicate Inv_All(ss : SystemState)
    {
        && Inv_Constant_Fields(ss)
        && Inv_Honest_Node_Only_Vote_One_Proposal_At_Same_View(ss)
        && Inv_Honest_Node_Only_Vote_One_Prepare_At_Same_View(ss)
        && Inv_Honest_Node_Only_Vote_One_PreCommit_At_Same_View(ss)
    }

    /**
     * Here we conduct our safety proof by 3 steps:
     * Step 1 : Initial system state holds invariants.
     * Step 2 : All system transition holds invariants as well.
     * Step 3 : These invariants imply the safety property.
     */

    lemma Lemma_Inv_Implies_Safety(ss : SystemState)
    requires ValidSystemState(ss)
    ensures forall r1, r2 | 
                            // && r1 in ss.nodeStates
                            // && r2 in ss.nodeStates
                            && IsHonest(ss, r1)
                            && IsHonest(ss, r2)
                          :: consistentBlockchains(ss.nodeStates[r1].bc, ss.nodeStates[r2].bc)
    {
        // var r1, r2 :| IsHonest(ss, r1) && IsHonest(ss, r2);
        // assert ValidReplicaState(ss.nodeStates[r1]);
        assert forall r | IsHonest(ss, r) :: ValidReplicaState(ss.nodeStates[r]);

        assert ss.nodeStates.Keys - ss.adversary.byz_nodes != {};
        var r1, r2 :| IsHonest(ss, r1) && IsHonest(ss, r2);
    }


}