include "Type.dfy"
include "System.dfy"
include "Auxilarily.dfy"


module M_Invariants {
    import opened M_SpecTypes
    import opened M_System
    import opened M_AuxilarilyFunc



    /**
     * Invariant: Constant fields kept by the system, e.g. Node counts(Honest & Byzantine), Node role(Honest always be honest?)
     */
    ghost predicate inv_Constant_Fields(ss : SystemState)
    // {
    // }

    /**
     * Invariant: All Blockchain should be consistent by its own. Consistency -> the former block should be parent of the later block.
     */
    ghost predicate inv_Blockchain_Inner_Consistency(b : Blockchain)
    {
        forall i1, i2 | i1 == i2-1 // TODO: Could be to strong
                      ::
                        && b[i1] == b[i2].parent
    }


    /**
     * Invariant: Each honest node are forced to vote PROPOSAL only one time at the same view. See Page(6): PROOF of Lemma 1
     */
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


    /**
     * Invariant: Each honest node are forced to vote only one PREPARE message from leader at the same view. See Page(6): PROOF of Lemma 1
     */
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


    /**
     * Invariant: Each honest node are forced to vote only one PRECOMMIT message from leader at the same view. See Page(6): PROOF of Lemma 1
     */
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

    ghost predicate inv_Honest_Node_Commit_Not_Conflict_Block(ss : SystemState)
    {
        forall r1, r2 | 
                        && IsHonest(ss, r1)
                        && IsHonest(ss, r2)
                      ::
                        && NoConflict(ss.nodeStates[r1].commitQC.block, ss.nodeStates[r2].commitQC.block)   //TODO: define block confliction
            
    }

}