include "Type.dfy"
include "System.dfy"
include "Trace.dfy"
include "Invariants.dfy"
include "Replica.dfy"
include "Auxilarily.dfy"
include "Lemmas_bak.dfy"
include "common/sets.dfy"

module M_Thereom_bak {
    import opened M_SpecTypes
    import opened M_System
    import opened M_Trace
    import opened M_Invariants
    import opened M_Replica
    import opened M_AuxilarilyFunc
    import opened M_Lemma_bak
    import opened M_Set

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
    lemma LemmaInvImpliesSafety(ss : SystemState)
    // requires ValidSystemState(ss)
    requires Reachable(ss)
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
            // Here we should prove: s1.bc <= s2.bc || s2.bc <= s1.bc
            LemmaReachableStateIsValid(ss);
            assert ValidReplicaState(s1) && ValidReplicaState(s2);
            if s1.bc != [M_SpecTypes.Genesis_Block] && s2.bc != [M_SpecTypes.Genesis_Block] {
                assert exists m1 | && m1 in s1.msgReceived
                                    && m1.mType.MT_Decide?
                                    && m1.justify.Cert?
                                    && m1.justify.cType == MT_Commit
                                    && ValidQC(m1.justify)
                                    && m1.justify.block.Block?
                                ::
                                    s1.bc <= getAncestors(m1.justify.block);
                var m1 :| && m1 in s1.msgReceived
                                    && m1.mType.MT_Decide?
                                    && m1.justify.Cert?
                                    && m1.justify.cType == MT_Commit
                                    && ValidQC(m1.justify)
                                    && m1.justify.block.Block?
                                    && s1.bc <= getAncestors(m1.justify.block);

                assert exists m2 | && m2 in s2.msgReceived
                                   && m2.mType.MT_Decide?
                                   && m2.justify.Cert?
                                   && m2.justify.cType.MT_Commit?
                                   && ValidQC(m2.justify)
                                   && m2.justify.block.Block?
                                ::
                                   s2.bc <= getAncestors(m2.justify.block);
                var m2 :| && m2 in s2.msgReceived
                                   && m2.mType.MT_Decide?
                                   && m2.justify.Cert?
                                   && m2.justify.cType.MT_Commit?
                                   && ValidQC(m2.justify)
                                   && m2.justify.block.Block?
                                   && s2.bc <= getAncestors(m2.justify.block);

                assert m1 in ss.msgSent by {
                    assert s1.msgReceived <= ss.msgSent by {
                        LemmaMsgReceivedByReplicaIsSubsetOfAllMsgSentBySystem(ss);
                    }
                }
                assert m2 in ss.msgSent by {
                    assert s2.msgReceived <= ss.msgSent by {
                        LemmaMsgReceivedByReplicaIsSubsetOfAllMsgSentBySystem(ss);
                    }
                }

                assert exists m1_p : Msg :: && m1_p in ss.msgSent
                                            && m1_p.mType == MT_Prepare
                                            && ValidQC(m1_p.justify)
                                            && m1_p.justify.cType == MT_Prepare
                                            && m1_p.justify.block == m1.justify.block
                                            && m1_p.justify.viewNum == m1.justify.viewNum by {
                    LemmaExistValidPrepareQCForEveryValidCommitQC(ss);
                }

                assert exists m2_p : Msg :: && m2_p in ss.msgSent
                                            && m2_p.mType == MT_Prepare
                                            && ValidQC(m2_p.justify)
                                            && m2_p.justify.cType == MT_Prepare
                                            && m2_p.justify.block == m2.justify.block
                                            && m2_p.justify.viewNum == m2.justify.viewNum by {
                    LemmaExistValidPrepareQCForEveryValidCommitQC(ss);
                }

                var m1_p :| && m1_p in ss.msgSent
                                            && m1_p.mType == MT_Prepare
                                            && ValidQC(m1_p.justify)
                                            && m1_p.justify.cType == MT_Prepare
                                            && m1_p.justify.block == m1.justify.block
                                            && m1_p.justify.viewNum == m1.justify.viewNum;
                var m2_p :| && m2_p in ss.msgSent
                                            && m2_p.mType == MT_Prepare
                                            && ValidQC(m2_p.justify)
                                            && m2_p.justify.cType == MT_Prepare
                                            && m2_p.justify.block == m2.justify.block
                                            && m2_p.justify.viewNum == m2.justify.viewNum;
                
                if m1_p.justify.viewNum <= m2_p.justify.viewNum {
                    assert extension(m2_p.justify.block, m1_p.justify.block) by {
                        LemmaPrepareQCWithLowerViewIsExtensionOfPrepareQCWithHigherView(ss);
                    }
                } else {
                    assert extension(m1_p.justify.block, m2_p.justify.block) by {
                        LemmaPrepareQCWithLowerViewIsExtensionOfPrepareQCWithHigherView(ss);
                    }
                }

                assert || extension(m1.justify.block, m2.justify.block)
                       || extension(m2.justify.block, m1.justify.block);
                
                var m1_acstr, m2_acstr := getAncestors(m1.justify.block), getAncestors(m2.justify.block); 

                assert s2.bc <= m2_acstr;
                assert s1.bc <= m1_acstr;

                // assert m2_acstr <= m1_acstr || m1_acstr <= m2_acstr by {
                //     if extension(m1.justify.block, m2.justify.block) {
                //         Lemma_AncestorOfParentIsPrefixOfAncestorOfChild(m1.justify.block, m2.justify.block);
                //     }
                //     else {
                //         Lemma_AncestorOfParentIsPrefixOfAncestorOfChild(m2.justify.block, m1.justify.block);
                //     }
                // }
                assert m2_acstr <= m1_acstr || m1_acstr <= m2_acstr;
                assert s2.bc <= s1.bc || s1.bc <= s2.bc;
                
            }
            else {  // s1.bc == [M_SpecTypes.Genesis_Block] || s2.bc == [M_SpecTypes.Genesis_Block]
                // OBSERVE 
                // by the invariant that an honest replica always holds a local blockchain starting with Genesis_Block
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

    lemma Thm_Two_Conflict_Block_Cant_Be_Both_Committed_By_Honest_Replica(ss : SystemState)
    // requires ValidSystemState(ss)
    requires Reachable(ss)
    ensures !(exists r, m1 : Msg, m2 : Msg :: && IsHonest(ss, r)
                                              && m1 in ss.nodeStates[r].msgReceived
                                              && m2 in ss.nodeStates[r].msgReceived
                                              && m1.mType == MT_Decide
                                              && m2.mType == MT_Decide
                                              && ValidQC(m1.justify)
                                              && ValidQC(m2.justify)
                                              && m1.justify.cType == MT_Commit
                                              && m1.justify.cType == m2.justify.cType
                                              && m1.justify.block.Block?
                                              && m2.justify.block.Block?
                                              && !NoConflict(m1.justify.block, m2.justify.block)
             )
    {
        // The negation of the conclusion
        if (exists r, m1 : Msg, m2 : Msg :: && IsHonest(ss, r)
                                              && m1 in ss.nodeStates[r].msgReceived
                                              && m2 in ss.nodeStates[r].msgReceived
                                              && m1.mType == MT_Decide
                                              && m2.mType == MT_Decide
                                              && ValidQC(m1.justify)
                                              && ValidQC(m2.justify)
                                              && m1.justify.cType == MT_Commit
                                              && m1.justify.cType == m2.justify.cType
                                              && m1.justify.block.Block?
                                              && m2.justify.block.Block?
                                              && !NoConflict(m1.justify.block, m2.justify.block)
             )
        {
            var r, m1, m2 :| && IsHonest(ss, r)
                            && m1 in ss.nodeStates[r].msgReceived
                            && m2 in ss.nodeStates[r].msgReceived
                            && m1.mType == MT_Decide
                            && m2.mType == MT_Decide
                            && ValidQC(m1.justify)
                            && ValidQC(m2.justify)
                            && m1.justify.cType == MT_Commit
                            && m1.justify.cType == m2.justify.cType
                            && m1.justify.block.Block?
                            && m2.justify.block.Block?
                            && !NoConflict(m1.justify.block, m2.justify.block);
            
            var qc1, qc2 := m1.justify, m2.justify;
            var w, b := qc1.block, qc2.block;
            var v1, v2 := qc1.viewNum, qc2.viewNum;

            // Proof: qc1.viewNum != qc2.viewNum
            calc {
                true;
                ==> {LemmaMsgReceivedByReplicaIsSubsetOfAllMsgSentBySystem(ss);}
                ss.nodeStates[r].msgReceived <= ss.msgSent;
                ==>
                m1 in ss.msgSent && m2 in ss.msgSent;
                ==> {
                    LemmaReachableStateIsValid(ss);
                    LemmaViewDiffOnConflictCertificate(ss);}
                v1 != v2;
            }

            // W.l.o.g. Assume qc1.viewNum is greater than qc2.viewNum
            assume v1 < v2;

            // Get all messages sent in the system with a valid prepare certificate
            var allPrepareQCMsg := getValidPrepareQCMsgs(ss);

            // Proof: Such messages must exist, cause every valid commit-certificate could be formed 
            // only if there exists a corresponding prepare-certificate. And here we have two valid 
            // commit-certifiacte (qc1, qc2).
            assert allPrepareQCMsg != {} by {
                LemmaMsgReceivedByReplicaIsSubsetOfAllMsgSentBySystem(ss);
                assert ss.nodeStates[r].msgReceived <= ss.msgSent;
                assert m2 in ss.msgSent;
                assert ValidQC(m2.justify);
                assert m2.justify.cType == MT_Commit;
                LemmaExistValidPrepareQCForEveryValidCommitQC(ss);
                assert exists m : Msg :: && m in ss.msgSent
                                        && m.mType == MT_Prepare
                                        && ValidQC(m.justify)
                                        && m.justify.cType == MT_Prepare
                                        && m in allPrepareQCMsg;    // Q.E.D.
                // assert exists m : Msg :: && m in ss.msgSent
                //                          && m.mType == MT_Prepare
                //                          && ValidQC(m.justify)
                //                          && m.justify.cType == MT_Prepare
                //                          && m in allPrepareQCMsg
                //                          && m.justify.block == m2.justify.block
                //                          && m.justify.viewNum == m2.justify.viewNum;
    
            }

            // Get all prepare message matching the following predicate : 
            // (qc1.viewNum < prepareQC.viewNum ≤ qc2.viewNum) ∧ (prepareQC.block conflicts with qc1.block)
            var matchingPrepareQCMsg := getMatchingPrepareQCMsgs(allPrepareQCMsg, qc1, qc2);

            // Proof: Such matching messages must exist, cause there exists at least one message satisfying the predicate.
            // e.g. the corresponding prepare message for commit-certificate `qc2`
            assert matchingPrepareQCMsg != {} by {
            LemmaMsgReceivedByReplicaIsSubsetOfAllMsgSentBySystem(ss);
            assert ss.nodeStates[r].msgReceived <= ss.msgSent;
            assert m2 in ss.msgSent;
            assert ValidQC(m2.justify);
            assert m2.justify.cType == MT_Commit;
            LemmaExistValidPrepareQCForEveryValidCommitQC(ss);
            // assert !NoConflict(qc1.block, qc2.block);
            // assert allPrepareQCMsg != {};
            // assert forall m | && m in allPrepareQCMsg
            //                 :: && ValidQC(m.justify);
            // assert ValidQC(qc1);
            // assert ValidQC(qc2);
            // assert qc1.viewNum < qc2.viewNum;
            // var matchM :| && matchM in allPrepareQCMsg
            //                          && PredConflictPrepareQCWithHigherViewNum(matchM.justify, qc1, qc2);
            // assert matchM in matchingPrepareQCMsg;
            // assert matchingPrepareQCMsg != {};
            assert exists m : Msg :: && m in allPrepareQCMsg
                                     && PredConflictPrepareQCWithHigherViewNum(m.justify, qc1, qc2)
                                     && m in matchingPrepareQCMsg; // Q.E.D.
            }

            // Get the message with minimal view number
            var qcsMsg := argminView(matchingPrepareQCMsg);
            assert qc1.viewNum < qcsMsg.justify.viewNum <= qc2.viewNum;
            assert !NoConflict(qcsMsg.justify.block, qc1.block);
            // assert !(exists m : Msg :: m in )

            var signers1 := getMajoritySignerInValidQC(qc1);
            var signers2 := getMajoritySignerInValidQC(qcsMsg.justify);
            assert signers1 * signers2 * Honest_Nodes != {} by {
                LemmaTwoQuorumIntersection(All_Nodes, Adversary_Nodes, signers1, signers2);
            }
            var replica :| replica in signers1 * signers2 * Honest_Nodes;

            // Proof: the prepare-certificate in qcsMsg could never be created in a valid system
            // i.e. The existence of qcsMsg will violated the precondition `ValidSystemState(ss)`
            LemmaReachableStateIsValid(ss);
            LemmaVoteMsgInValidQCAlsoRecievedByVoter(ss);
            assert exists voteMsg : Msg :: 
                                          && voteMsg in ss.nodeStates[replica].msgReceived
                                          && voteMsg.partialSig.Signature?
                                          && voteMsg.partialSig.signer == replica
                                          && voteMsg.partialSig.mType == qcsMsg.justify.cType
                                          && voteMsg.partialSig.viewNum == qcsMsg.justify.viewNum
                                          && voteMsg.partialSig.block == qcsMsg.justify.block
                                          ;
            
            var voteMsgByReplica : Msg :| 
                                          && voteMsgByReplica in ss.nodeStates[replica].msgReceived
                                          && voteMsgByReplica.partialSig.Signature?
                                          && voteMsgByReplica.partialSig.signer == replica
                                          && voteMsgByReplica.partialSig.mType == qcsMsg.justify.cType
                                          && voteMsgByReplica.partialSig.viewNum == qcsMsg.justify.viewNum
                                          && voteMsgByReplica.partialSig.block == qcsMsg.justify.block
                                          ;
            // assert 
            //         && voteMsgByReplica.partialSig.Signature?
            //         && voteMsgByReplica.partialSig.signer == replica
            //         && voteMsgByReplica.partialSig.mType == MT_Prepare;

            // assert replica in Honest_Nodes;
            
            
            assert ss.nodeStates.Keys - ss.adversary.byz_nodes == Honest_Nodes by {
                // assert ss.nodeStates.Keys == All_Nodes;
                // assert ss.adversary.byz_nodes == Adversary_Nodes;
                // assert Honest_Nodes * ss.adversary.byz_nodes == {};
                // assert ss.nodeStates.Keys == Honest_Nodes + ss.adversary.byz_nodes;
                // assert |ss.nodeStates.Keys| == |Honest_Nodes| + |ss.adversary.byz_nodes|;
                LemmaAdditiveOnSeparateSet(ss.nodeStates.Keys, ss.adversary.byz_nodes, Honest_Nodes);
            }
            assert IsHonest(ss, replica);

            LemmaReplicaVotePrepareOnlyIfItRecievedASafetyPrepareQC(ss, replica, qc1);
            assert exists m1 : Msg :: && m1 in ss.nodeStates[replica].msgReceived
                                               && m1.mType == MT_Prepare
                                               && ValidQC(m1.justify)
                                               && m1.justify.cType == MT_Prepare
                                               && m1.justify.viewNum > qc1.viewNum
                                               && m1.block.Block?
                                               && extension(m1.block, m1.justify.block)
                                               && safeNode(m1.block, m1.justify, qc1)
                                               && voteMsgByReplica.partialSig.block == m1.block
                                               && m1.justify.viewNum < voteMsgByReplica.partialSig.viewNum;

            var proposal_qcs : Msg :| && proposal_qcs in ss.nodeStates[replica].msgReceived
                                               && proposal_qcs.mType == MT_Prepare
                                               && ValidQC(proposal_qcs.justify)
                                               && proposal_qcs.justify.cType == MT_Prepare
                                               && proposal_qcs.justify.viewNum > qc1.viewNum
                                               && proposal_qcs.block.Block?
                                               && extension(proposal_qcs.block, proposal_qcs.justify.block)
                                               && safeNode(proposal_qcs.block, proposal_qcs.justify, qc1)
                                               && voteMsgByReplica.partialSig.block == proposal_qcs.block
                                               && proposal_qcs.justify.viewNum < voteMsgByReplica.partialSig.viewNum;
            calc {
                !NoConflict(qcsMsg.justify.block, qc1.block);
                ==>
                !NoConflict(proposal_qcs.block, qc1.block);
                ==>
                !extension(proposal_qcs.block, qc1.block);
            }

            assert proposal_qcs.justify.viewNum <= qc2.viewNum by {
                assert proposal_qcs.justify.viewNum < voteMsgByReplica.partialSig.viewNum;
                assert voteMsgByReplica.partialSig.viewNum == qcsMsg.justify.viewNum;
                assert qcsMsg.justify.viewNum <= qc2.viewNum;
            }
            assert qc1.viewNum < proposal_qcs.justify.viewNum <= qc2.viewNum;


            assert extension(proposal_qcs.block, proposal_qcs.justify.block);
            assert !NoConflict(proposal_qcs.block, qc1.block);
            
            assert exists m1_p : Msg :: && m1_p in ss.msgSent
                                        && m1_p.mType == MT_Prepare
                                        && ValidQC(m1_p.justify)
                                        && m1_p.justify.cType == MT_Prepare
                                        && m1_p.justify.block == qc1.block
                                        && m1_p.justify.viewNum == qc1.viewNum by {
                LemmaExistValidPrepareQCForEveryValidCommitQC(ss);
            }

            assert exists m2_p : Msg :: && m2_p in ss.msgSent
                                        && m2_p.mType == MT_Prepare
                                        && ValidQC(m2_p.justify)
                                        && m2_p.justify.cType == MT_Prepare
                                        && m2_p.justify.block == qc2.block
                                        && m2_p.justify.viewNum == qc2.viewNum by {
                LemmaExistValidPrepareQCForEveryValidCommitQC(ss);
            }

            var m1_p :| && m1_p in ss.msgSent
                                        && m1_p.mType == MT_Prepare
                                        && ValidQC(m1_p.justify)
                                        && m1_p.justify.cType == MT_Prepare
                                        && m1_p.justify.block == qc1.block
                                        && m1_p.justify.viewNum == qc1.viewNum;
            var m2_p :| && m2_p in ss.msgSent
                                        && m2_p.mType == MT_Prepare
                                        && ValidQC(m2_p.justify)
                                        && m2_p.justify.cType == MT_Prepare
                                        && m2_p.justify.block == qc2.block
                                        && m2_p.justify.viewNum == qc2.viewNum;
            if m1_p.justify.viewNum <= m2_p.justify.viewNum {
                    assert extension(m2_p.justify.block, m1_p.justify.block) by {
                        LemmaPrepareQCWithLowerViewIsExtensionOfPrepareQCWithHigherView(ss);
                    }
                } else {
                    assert extension(m1_p.justify.block, m2_p.justify.block) by {
                        LemmaPrepareQCWithLowerViewIsExtensionOfPrepareQCWithHigherView(ss);
                    }
                }

                assert || extension(qc1.block, qc2.block)
                       || extension(qc2.block, qc1.block);
                
                // var m1_acstr, m2_acstr := getAncestors(m1.justify.block), getAncestors(m2.justify.block); 

                // assert s2.bc <= m2_acstr;
                // assert s1.bc <= m1_acstr;

                // assert m2_acstr <= m1_acstr || m1_acstr <= m2_acstr by {
                //     if extension(m1.justify.block, m2.justify.block) {
                //         Lemma_AncestorOfParentIsPrefixOfAncestorOfChild(m1.justify.block, m2.justify.block);
                //     }
                //     else {
                //         Lemma_AncestorOfParentIsPrefixOfAncestorOfChild(m2.justify.block, m1.justify.block);
                //     }
                // }
                // assert s2.bc <= s1.bc || s1.bc <= s2.bc;

            /*  
            *   Assumption: 
                            (1) qc1 and qc2 are valid COMMIT-certificate;
                            (2) qc1.block conflicts with qc2.block;
                            (3) qc1.viewNum < qc2.viewNum
            *   Example: 
            *   ---------------------------------
            *  |   qc1.block := G -> B1 -> B2    |
            *  |   qc1.viewNum := 5              |
            *  |   (replica's lockedQC)          |
            *   ---------------------------------
            *
            *   ----------------------------------------
            *  |    qc2.block := G -> B1 -> B3 -> B4    |
            *  |    qc2.viewNum := 10                   |
            *   ----------------------------------------
            *   
            *   ---------------------------------
            *  |    qcs.block := G -> B1 -> B3   |
            *  |    5 < qcs.viewNum <= 10        |
            *  |    (type = PREPARE)             |
            *   ---------------------------------
            *   
            *   Proposal of qcs.block : proposal_qcs
            *   -----------------------------------------
            *  |    proposal_qcs.block := G -> B1 -> B3  |
            *  |    proposal_qcs.viewNum == qcs.viewNum  |
            *  |    proposal_qcs.justify == ?            |
            *   -----------------------------------------
            *   
            *   To successfully vote proposal_qcs,
            *   here we need proposal_qcs satisfying all the following constraints
            *   (1) proposal_qcs.block extends proposal_qcs.justify.block
            *   (2) || proposal_qcs.block extends qc1.block (locedQC)   ==> FAIL
            *       || proposal_qcs.justify.viewNum > qc1.block.viewNum
            *   
            *   E.g. 
            *   ------------------------------------------------------
            *  |    proposal_qcs.block := G -> B1 -> B3               |
            *  |    proposal_qcs.viewNum == qcs.viewNum               |
            *  |    proposal_qcs.justify == G -> B1                   |
            *  |    proposal_qcs.justify.viewNum > qc1.viewNum        | 
            *   ------------------------------------------------------
            *   
            *   Need to prove such an justify never exist
            *
            */
            

            // By asserting false at the end, we could check whether the `IF` statement succeed or not
            // Asserting false should always raise en error, if not, then this assertion never been called, which means the IF statement is false.
            assert false;
        }
    }

    predicate PredConflictPrepareQCWithHigherViewNum(prepareQC : Cert, commitQC1 : Cert, commitQC2 : Cert)
    requires ValidQC(prepareQC)
    requires ValidQC(commitQC1)
    requires ValidQC(commitQC2)
    requires commitQC1.viewNum < commitQC2.viewNum
    requires !NoConflict(commitQC1.block, commitQC2.block)
    {
        && commitQC1.viewNum < prepareQC.viewNum <= commitQC2.viewNum
        && !NoConflict(commitQC1.block, prepareQC.block)
    }

    function getValidPrepareQCMsgs(ss : SystemState) : set<Msg>
    {
        set m | && m in ss.msgSent
                && m.mType == MT_Prepare
                && ValidQC(m.justify)
                && m.justify.cType == MT_Prepare
                // && PredConflictPrepareQCWithHigherViewNum(m.justify, qc1, qc2)
    }

    function getMatchingPrepareQCMsgs(msgsWithPrepareQC : set<Msg>, commitQC1 : Cert, commitQC2: Cert) : set<Msg>
    requires forall m | && m in msgsWithPrepareQC
                     :: && ValidQC(m.justify)
                        && m.justify.cType == MT_Prepare
    requires ValidQC(commitQC1)
    requires ValidQC(commitQC2)
    requires commitQC1.viewNum < commitQC2.viewNum
    requires !NoConflict(commitQC1.block, commitQC2.block)
    {
        set m | && m in msgsWithPrepareQC
                && PredConflictPrepareQCWithHigherViewNum(m.justify, commitQC1, commitQC2)

    }
}