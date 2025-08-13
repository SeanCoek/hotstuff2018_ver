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
    ghost predicate Inv_Constant_Fields(ss : SystemState)
    {
      && ss.adversary.byz_nodes == M_SpecTypes.Adversary_Nodes
      && ss.nodeStates.Keys == M_SpecTypes.All_Nodes
    }


    /**
     * Invariant: Each honest node are forced to vote PROPOSAL only one time at the same view. See Page(6): PROOF of Lemma 1
     */
    ghost predicate Inv_Honest_Node_Only_Vote_One_Proposal_At_Same_View(ss : SystemState)
    {
        forall r | IsHonest(ss, r) ::
            var msgReceived := ss.nodeStates[r].msgReceived;
            forall m1, m2 | 
                            && m1 in msgReceived
                            && m2 in msgReceived
                            && m1.mType == MT_Prepare
                            && m2.mType == MT_Prepare
                            && m1.partialSig.Signature?
                            && m2.partialSig.Signature?
                            && m1.partialSig.signer == m2.partialSig.signer
                            && IsHonest(ss, m1.partialSig.signer)
                            && m1.viewNum == m2.viewNum
                          ::
                            && m1 == m2
                            && m1.partialSig.block == m2.partialSig.block
    }


    /**
     * Invariant: Each honest node are forced to vote only one PREPARE message from leader at the same view. See Page(6): PROOF of Lemma 1
     */
    ghost predicate Inv_Honest_Node_Only_Vote_One_Prepare_At_Same_View(ss : SystemState)
    {
        forall r | IsHonest(ss, r) ::
            var msgReceived := ss.nodeStates[r].msgReceived;
            forall m1, m2 | 
                            && m1 in msgReceived
                            && m2 in msgReceived
                            && m1.mType == MT_PreCommit
                            && m2.mType == MT_PreCommit
                            && m1.partialSig.Signature?
                            && m2.partialSig.Signature?
                            && m1.partialSig.signer == m2.partialSig.signer
                            && IsHonest(ss, m1.partialSig.signer)
                            && m1.viewNum == m2.viewNum
                          ::
                            && m1 == m2
                            && m1.partialSig.block == m2.partialSig.block
    }


    /**
     * Invariant: Each honest node are forced to vote only one PRECOMMIT message from leader at the same view. See Page(6): PROOF of Lemma 1
     */
    ghost predicate Inv_Honest_Node_Only_Vote_One_PreCommit_At_Same_View(ss : SystemState)
    {
        forall r | IsHonest(ss, r) ::
            var msgReceived := ss.nodeStates[r].msgReceived;
            forall m1, m2 | 
                            && m1 in msgReceived
                            && m2 in msgReceived
                            && m1.mType == MT_Commit
                            && m2.mType == MT_Commit
                            && m1.partialSig.Signature?
                            && m2.partialSig.Signature?
                            && m1.partialSig.signer == m2.partialSig.signer
                            && IsHonest(ss, m1.partialSig.signer)
                            && m1.viewNum == m2.viewNum
                          ::
                            && m1 == m2
                            && m1.partialSig.block == m2.partialSig.block
    }

    ghost predicate Inv_Honest_Node_Commit_Not_Conflict_Block(ss : SystemState)
    {
        forall r1, r2 | 
                        && IsHonest(ss, r1)
                        && IsHonest(ss, r2)
                      ::
                        && ss.nodeStates[r1].commitQC.Cert?
                        && ss.nodeStates[r2].commitQC.Cert?
                        && ss.nodeStates[r1].commitQC.block.Block?
                        && ss.nodeStates[r2].commitQC.block.Block?
                        && NoConflict(ss.nodeStates[r1].commitQC.block, ss.nodeStates[r2].commitQC.block)   //TODO: define block confliction
            
    }

    // ghost predicate Inv_

}