include "Type.dfy"
include "System.dfy"
include "Trace.dfy"
include "Invariants.dfy"
include "Replica.dfy"
include "Auxilarily.dfy"
include "Lemmas.dfy"

module M_Thereom {
    import opened M_SpecTypes
    import opened M_System
    import opened M_Trace
    import opened M_Invariants
    import opened M_Replica
    import opened M_AuxilarilyFunc
    import opened M_Lemma

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
     * Step 1 : Initial system state holds invariants. (see `Lemma_Initial_State_Holds_Is_Valid` in System.dfy)
     * Step 2 : All system transition holds invariants as well. (see `Lemma_System_Next_Is_Valid` in System.dfy)
     * Step 3 : These invariants imply the safety property.
     */


    /**
     * Sytem invariants (described in `ValidSystemState`) imply the safety property.
     *
    */
    lemma Lemma_Inv_Implies_Safety(ss : SystemState)
    requires ValidSystemState(ss)
    ensures forall r1, r2 | 
                            && IsHonest(ss, r1)
                            && IsHonest(ss, r2)
                         :: 
                            consistentBlockchains(ss.nodeStates[r1].bc, ss.nodeStates[r2].bc)
    {

        forall r1, r2 | 
                        && IsHonest(ss, r1)
                        && IsHonest(ss, r2)
        ensures consistentBlockchains(ss.nodeStates[r1].bc, ss.nodeStates[r2].bc)
        {
            var s1, s2 := ss.nodeStates[r1], ss.nodeStates[r2];
            if ReplicaInit(s1, s1.id) && ReplicaInit(s2, s2.id) {
                assert s1.bc <= s2.bc || s2.bc <= s1.bc;
            }
        }
    }


    /**
     * Theorem 2. If w and b are conflicting nodes, then they cannot beboth committed, each by a correct replica.
     *
     * Proof. We prove this important theorem by contradiction. 
     * Let qc1 denote a valid commitQC (i.e., qc1.type = commit) such that qc1.node = w, 
     * and qc2 denote a valid commitQC suchthat qc2.node = b. 
     * Denote v1 = qc1.viewNumber and v2 =qc2.viewNumber. 
     * By Lemma 1, v1 , v2. W.l.o.g. assume v1 < v2.
     *
     * We will now denote by vs the lowest view higher than v1 for which there is a valid prepareQC, 
     * qcs (i.e., qcs.type = prepare) where qcs.viewNumber = vs , and qcs.node conflicts with w. 
     * Formally, we define the following predicate for any prepareQC: 
     * E(prepareQC) := (v1 < prepareQC.viewNumber ≤ v2) ∧ (prepareQC.node conflicts with w).
     *
     * We can now set the first switching point qcs: qcs := argmin {prepareQC.viewNumber | prepareQC is valid ∧ E(prepareQC)}.
     * Note that, by assumption such a qcs must exist; 
     * for example, qcs could be the prepareQC formed in view v2.
     *
     * Of the correct replicas that sent a partial result tsignr (⟨qc1.type, qc1.viewNumber, qc1.node⟩), 
     * let r be the first that contributed tsignr (⟨qcs.type, qcs.viewNumber , qcs.node⟩);
     * such an r must exist since otherwise, one of qc1.sig and qcs.sig could not have been created. 
     *
     * During view v1, replica r updates its lock locked lockedQC to a precommitQC on w at Line 25 of Algorithm 2.
     * Due to the minimality of vs, the lock that replica r has on w is not changed before qcs is formed. 
     * Otherwise r must have seen some other prepareQC with lower view because Line 17 comes before Line 25, 
     * contradicting to the minimality. 
     *
     * Now consider the invocation of safeNode in the prepare phase of view vs by replica r, 
     * with a message m carrying m.node = qcs.node. By assumption, m.node conflicts with lockedQC.node, 
     * and so the disjunct at Line 26 of Algorithm 1 is false. 
     * Moreover, m.justify.viewNumber > v1 would violate the minimality of vs, and so the disjunct in Line 27 of Algorithm 1is also false.
     * Thus, safeNode must return false and r cannot cast a prepare vote on the conflicting branch in view vs, a contradiction. 
     * Q.E.D.
     *
     */

    lemma Thm_Two_Conflict_Block_Cant_Be_Committed_By_Honest_Replica(ss : SystemState)
    requires ValidSystemState(ss)
    ensures !(exists r, m1 : Msg, m2 : Msg :: && IsHonest(ss, r)
                                              && m1 in ss.nodeStates[r].msgRecieved
                                              && m2 in ss.nodeStates[r].msgRecieved
                                              && m1.mType == MT_Decide
                                              && m2.mType == MT_Decide
                                              && ValidQC(m1.justify)
                                              && ValidQC(m2.justify)
                                              && m1.justify.block.Block?
                                              && m2.justify.block.Block?
                                              && !NoConflict(m1.justify.block, m2.justify.block)
             )
    {
        // The negation of the conclusion
        if (exists r, m1 : Msg, m2 : Msg :: && IsHonest(ss, r)
                                              && m1 in ss.nodeStates[r].msgRecieved
                                              && m2 in ss.nodeStates[r].msgRecieved
                                              && m1.mType == MT_Decide
                                              && m2.mType == MT_Decide
                                              && ValidQC(m1.justify)
                                              && ValidQC(m2.justify)
                                              && m1.justify.block.Block?
                                              && m2.justify.block.Block?
                                              && !NoConflict(m1.justify.block, m2.justify.block)
             )
        {
            var r, m1, m2 :| && IsHonest(ss, r)
                            && m1 in ss.nodeStates[r].msgRecieved
                            && m2 in ss.nodeStates[r].msgRecieved
                            && m1.mType == MT_Decide
                            && m2.mType == MT_Decide
                            && ValidQC(m1.justify)
                            && ValidQC(m2.justify)
                            && m1.justify.block.Block?
                            && m2.justify.block.Block?
                            && !NoConflict(m1.justify.block, m2.justify.block);

            assert m1.justify.viewNum != m2.justify.viewNum by {
                LemmaViewDiffOnConflictCertificate(ss);
            }

            // By asserting false at the end, we could check whether the `IF` statement succeed or not
            // Asserting false should always raise en error, if not, then this assertion never been called, which means the IF statement is false.
            assert false;
        }
    }

    lemma Lemma_Test_Contradiction()
    ensures 1 + 1 == 2
    {
        if !(1+1==2) {
            assert false;
        }
        assert false;
    }
}