include "Type.dfy"
include "System.dfy"
include "Trace.dfy"
include "Invariants.dfy"

module M_Thereom {
    import opened M_SpecTypes
    import opened M_System
    import opened M_Trace
    import opened M_Invariants

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


    // lemma LemmaBlockchainConsistency(t : Trace, c : Configuration)
    // requires ValidTrace(t, c)
    // ensures consistency(t)
    // {
        
    // }

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

    lemma Lemma_Initial_State_Holds_Inv(ss : SystemState)
    requires SystemInit(ss, ss.configuration)
    ensures Inv_All(ss)
    {}


    lemma Lemma_State_Transition_Holds_Inv(ss : SystemState, ss' : SystemState)
    requires SystemNext(ss, ss')
    ensures Inv_All(ss) && Inv_All(ss')
    {}


    lemma Lemma_Inv_Implies_Safety(ss : SystemState)
    requires Inv_All(ss)
    ensures forall r1, r2 | 
                            && r1 in ss.nodeStates
                            && r2 in ss.nodeStates
                            && IsHonest(ss, r1)
                            && IsHonest(ss, r2)
                          :: consistentBlockchains(ss.nodeStates[r1].bc, ss.nodeStates[r2].bc)
    {}


    // lemma LemmaBlockchainConsistency()
}