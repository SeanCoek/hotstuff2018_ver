include "Type.dfy"
include "System.dfy"


module M_Invariants {
    import opened M_SpecTypes
    import opened M_System


    ghost predicate inv_Honest_Node_Only_Vote_One_Proposal_At_Same_View(ss : SystemState)
    {
        forall r | IsHonest(ss, r) ::
            var msgRecieved := ss.nodeStates[r].msgRecieved;
            forall m1, m2 | 
                            && m1 in msgRecieved
                            && m2 in msgRecieved
                            && m1.mType == MT_Prepare
                            && m2.mType == MT_Prepare
                            && m1.partialSig.signer == m2.partialSig.signer
                            && IsHonest(ss, m1.partialSig.signer)
                            && m1.viewNum == m2.viewNum
                          ::
                            m1 == m2
    }

    ghost predicate inv_Honest_Node_Only_Vote_One_Prepare_At_Same_View(ss : SystemState)
    {
        forall r | IsHonest(ss, r) ::
            var msgRecieved := ss.nodeStates[r].msgRecieved;
            forall m1, m2 | 
                            && m1 in msgRecieved
                            && m2 in msgRecieved
                            && m1.mType == MT_PreCommit
                            && m2.mType == MT_PreCommit
                            && m1.partialSig.signer == m2.partialSig.signer
                            && IsHonest(ss, m1.partialSig.signer)
                            && m1.viewNum == m2.viewNum
                          ::
                            m1 == m2
    }

    ghost predicate inv_Honest_Node_Only_Vote_One_PreCommit_At_Same_View(ss : SystemState)
    {
        forall r | IsHonest(ss, r) ::
            var msgRecieved := ss.nodeStates[r].msgRecieved;
            forall m1, m2 | 
                            && m1 in msgRecieved
                            && m2 in msgRecieved
                            && m1.mType == MT_Commit
                            && m2.mType == MT_Commit
                            && m1.partialSig.signer == m2.partialSig.signer
                            && IsHonest(ss, m1.partialSig.signer)
                            && m1.viewNum == m2.viewNum
                          ::
                            m1 == m2
    }

}