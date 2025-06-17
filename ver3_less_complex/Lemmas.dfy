include "Type.dfy"
include "Auxilarily.dfy"
include "System.dfy"

module M_Lemma {
    import opened M_SpecTypes
    import opened M_AuxilarilyFunc
    import opened M_System

    lemma{:axiom} Axiom_Byz_Constraints()
    ensures |Adversary_Nodes| <= f(|All_Nodes|)
    ensures Adversary_Nodes * Honest_Nodes == {}

    lemma{:axiom} Axiom_Common_Constraints()
    ensures All_Nodes != {}

    lemma{:axiom} NoOuterClient()
    ensures forall cert : Signature :: cert.signer in All_Nodes

    lemma LemmaExistVoteMsgIfCertificateFormed(ss : SystemState)
    requires ValidSystemState(ss)
    ensures forall m : Msg | && m in ss.msgSent
                             && ValidQC(m.justify)
                          ::
                             && (forall s : Signature | && s in m.justify.signatures
                                                        && s.Signature?
                                                     ::
                                                        && (exists m : Msg | && m in ss.msgSent
                                                                          ::
                                                                             && m.partialSig.Signature?
                                                                             && m.partialSig == s
                                                            ) 
                                )
    // {

    // }

    lemma LemmaHonestNodeOnlyVoteOnceInOneView(ss : SystemState)
    requires ValidSystemState(ss)
    ensures forall m1 : Msg, m2 : Msg | && m1 in ss.msgSent
                                        && m2 in ss.msgSent
                                        && m1.partialSig.Signature?
                                        && m2.partialSig.Signature?
                                        && m1.partialSig.signer == m2.partialSig.signer
                                        && IsHonest(ss, m1.partialSig.signer)
                                        && m1.partialSig.mType == m2.partialSig.mType
                                        && m1.partialSig.viewNum == m2.partialSig.viewNum
                                      ::
                                        m1.partialSig.block != m2.partialSig.block

    // ensures forall s1 : Signature, s2 : Signature | 
    //                                                 && s1.Signature?
    //                                                 && s2.Signature?
    //                                                 && s1.signer == s2.signer
    //                                                 && IsHonest(ss, s1.signer)
    //                                                 && s1.viewNum == s2.viewNum
    //                                                 && s1.mType == s2.mType
    //                                               ::
    //                                                 s1.block == s2.block
    {

    }

    /**
     * Lemma: for 2 valid certificate, if they are not conflict, then their coressponding view number should be different
     */
    lemma LemmaViewDiffOnConflictCertificatePrepare(ss : SystemState)
    // requires All_Nodes != {}
    requires ValidSystemState(ss)
    ensures forall r1, r2, cert1, cert2 | && IsHonest(ss, r1)
                                          && IsHonest(ss, r2)
                                          && cert1 == ss.nodeStates[r1].prepareQC && cert1.Cert? 
                                          && cert2 == ss.nodeStates[r2].prepareQC && cert2.Cert?
                                          && cert1.block.Block?
                                          && cert2.block.Block?
                                          && !NoConflict(cert1.block, cert2.block)
                                        ::
                                          cert1.viewNum != cert2.viewNum

    {

        forall r1, r2, cert1, cert2 |   && IsHonest(ss, r1)
                                        && IsHonest(ss, r2)
                                        && cert1 == ss.nodeStates[r1].prepareQC && cert1.Cert? 
                                        && cert2 == ss.nodeStates[r2].prepareQC && cert2.Cert?
                                        && cert1.block.Block?
                                        && cert2.block.Block?
                                        && !NoConflict(cert1.block, cert2.block)

        ensures cert1.viewNum != cert2.viewNum
        {
            // calc {
            //     !NoConflict(cert1.block, cert2.block);
            //     ==>
            //     cert1.block != cert2.block;
            // }
            
            var signers1 := getMajoritySignerInValidQC(cert1);
            var signers2 := getMajoritySignerInValidQC(cert2);
            LemmaTwoQuorumIntersection(All_Nodes, Adversary_Nodes, signers1, signers2);
            // assert signers1 * signers2 * Honest_Nodes != {} by
            // {
            //     LemmaTwoQuorumIntersection(All_Nodes, Adversary_Nodes, signers1, signers2);
            // }
            // var replica :| replica in signers1 * signers2 * Honest_Nodes;
            // var sign1 :| && sign1 in cert1.signatures
            //              && sign1.signer == replica;
            // var sign2 :| && sign2 in cert2.signatures
            //              && sign2.signer == replica;
            // assert sign1 != sign2;
            // calc {
            //     // sign1 != sign2
            //     // ==>
            //     cert1.viewNum != cert2.viewNum;
            // }
            // assert sign1.signer == sign2.signer;
            // assert sign1.mType == sign2.mType;
            // assert sign1.block != sign2.block;
            // assert cert1.viewNum != cert2.viewNum by {
            //     LemmaHonestNodeOnlyVoteOnceInOneView(ss);
            // }
            LemmaHonestNodeOnlyVoteOnceInOneView(ss);
        }
    } 

    
    /**
     * Lemma: for 2 valid certificate, if they are not conflict, then their coressponding view number should be different
     */
    lemma LemmaViewDiffOnConflictCertificate(ss : SystemState)
    requires ValidSystemState(ss)
    ensures forall m1, m2, cert1, cert2 |   && m1 in ss.msgSent
                                            && m2 in ss.msgSent
                                            && cert1 == m1.justify
                                            && cert2 == m2.justify
                                            && ValidQC(cert1)
                                            && ValidQC(cert2)
                                            && cert1.cType == cert2.cType
                                            && cert1.block.Block?
                                            && cert2.block.Block?
                                            && !NoConflict(cert1.block, cert2.block)
                                        ::
                                            cert1.viewNum != cert2.viewNum
    {
        // forall r1, r2, cert1, cert2 |   && IsHonest(ss, r1)
        //                                 && IsHonest(ss, r2)
        //                                 && ValidQC(cert1)
        //                                 && ValidQC(cert2)
        //                                 && cert1.cType == cert2.cType
        //                                 && cert1.block.Block?
        //                                 && cert2.block.Block?
        //                                 && !NoConflict(cert1.block, cert2.block)
        forall  m1, m2, cert1, cert2 |  && m1 in ss.msgSent
                                        && m2 in ss.msgSent
                                        && cert1 == m1.justify
                                        && cert2 == m2.justify
                                        && ValidQC(cert1)
                                        && ValidQC(cert2)
                                        && cert1.cType == cert2.cType
                                        && cert1.block.Block?
                                        && cert2.block.Block?
                                        && !NoConflict(cert1.block, cert2.block)
        ensures cert1.viewNum != cert2.viewNum
        {
            var signers1 := getMajoritySignerInValidQC(cert1);
            var signers2 := getMajoritySignerInValidQC(cert2);
            // LemmaTwoQuorumIntersection(All_Nodes, Adversary_Nodes, signers1, signers2);
            assert signers1 * signers2 * Honest_Nodes != {} by
            {
                LemmaTwoQuorumIntersection(All_Nodes, Adversary_Nodes, signers1, signers2);
            }
            var replica :| replica in signers1 * signers2 * Honest_Nodes;
            var sign1 :| && sign1 in cert1.signatures
                         && sign1.signer == replica;
            var sign2 :| && sign2 in cert2.signatures
                         && sign2.signer == replica;
            assert sign1 != sign2;
            calc {
                sign1 != sign2;
                ==> { LemmaHonestNodeOnlyVoteOnceInOneView(ss);
                      LemmaExistVoteMsgIfCertificateFormed(ss);
                    }
                cert1.viewNum != cert2.viewNum;
            }
        }
    }

    lemma LemmaMsgRecievedByReplicaIsSubsetOfAllMsgSentBySystem(ss : SystemState)
    requires ValidSystemState(ss)
    ensures forall r, msgs | && IsHonest(ss, r)
                             && msgs == ss.nodeStates[r].msgRecieved
                          ::
                             && msgs <= ss.msgSent
    // {

    // }

    lemma LemmaExistValidPrepareQCForEveryValidPrecommitQC(ss : SystemState)
    requires ValidSystemState(ss)
    ensures forall m : Msg | && m in ss.msgSent
                             && ValidQC(m.justify)
                             && m.justify.cType == MT_PreCommit
                          ::
                            //  && (exists m2 : Msg :: && m2 in ss.msgSent
                            //                      && ValidQC(m2.justify)
                            //                      && m2.justify.cType == MT_PreCommit
                            //                      && m2.justify.block == m.justify.block
                            //                      && m2.justify.viewNum == m.justify.viewNum
                            // )
                             && (exists m3 : Msg :: && m3 in ss.msgSent
                                                 && ValidQC(m3.justify)
                                                 && m3.justify.cType == MT_Prepare
                                                 && m3.justify.block == m.justify.block
                                                 && m3.justify.viewNum == m.justify.viewNum
                            )
    // {

    // }

    lemma LemmaExistValidPrecommitQCForEveryValidCommitQC(ss : SystemState)
    requires ValidSystemState(ss)
    ensures forall m : Msg | && m in ss.msgSent
                             && ValidQC(m.justify)
                             && m.justify.cType == MT_Commit
                          ::
                             && (exists m2 : Msg :: && m2 in ss.msgSent
                                                 && ValidQC(m2.justify)
                                                 && m2.justify.cType == MT_PreCommit
                                                 && m2.justify.block == m.justify.block
                                                 && m2.justify.viewNum == m.justify.viewNum
                            )
    // {

    // }


    lemma LemmaExistValidPrepareQCForEveryValidCommitQC(ss : SystemState)
    requires ValidSystemState(ss)
    ensures forall m : Msg | && m in ss.msgSent
                             && ValidQC(m.justify)
                             && m.justify.cType == MT_Commit
                          ::
                             && (exists m2 : Msg :: && m2 in ss.msgSent
                                                    && m2.mType == MT_Prepare
                                                    && ValidQC(m2.justify)
                                                    && m2.justify.cType == MT_Prepare
                                                    && m2.justify.block == m.justify.block
                                                    && m2.justify.viewNum == m.justify.viewNum)
    {
        LemmaExistValidPrecommitQCForEveryValidCommitQC(ss);
        LemmaExistValidPrepareQCForEveryValidPrecommitQC(ss);
    }




    lemma LemmaReplicaVotePrepareOnlyIfItRecievedASafetyPrepareQC(ss : SystemState, r : Address, lockedQC : Cert)
    requires ValidSystemState(ss)
    requires ValidQC(lockedQC)
    requires IsHonest(ss, r)
    ensures forall m : Msg | && m in ss.nodeStates[r].msgRecieved
                          :: 
                            // && m.mType == MT_Prepare
                            && m.partialSig.Signature?
                            && m.partialSig.signer == r
                            && m.partialSig.mType == MT_Prepare
                            ==>
                            (exists m1 : Msg :: && m1 in ss.nodeStates[r].msgRecieved
                                               && m1.mType == MT_Prepare
                                               && ValidQC(m1.justify)
                                               && m1.justify.cType == MT_Prepare
                                               && m1.justify.viewNum > lockedQC.viewNum
                                               && m1.block.Block?
                                               && extension(m1.block, m1.justify.block)
                                               && safeNode(m1.block, m1.justify, lockedQC)
                                               && m.partialSig.block == m1.block
                                               && m1.justify.viewNum < m.partialSig.viewNum
                            )
    
    lemma LemmaVoteMsgInValidQCAlsoRecievedByVoter(ss : SystemState)
    requires ValidSystemState(ss)
    ensures forall m : Msg | && m in ss.msgSent
                             && ValidQC(m.justify)
                          ::
                            //  && var signers := getMajoritySignerInValidQC(m.justify)
                             && var signatures := getVotesInValidQC(m.justify);
                             && forall s | s in signatures
                                        :: 
                                          && (exists voteMsg : Msg :: 
                                                                     && voteMsg in ss.nodeStates[s.signer].msgRecieved
                                                                     && voteMsg.partialSig == s)
    // {}

    lemma LemmaPrepareQCExtension(ss : SystemState)
    requires ValidSystemState(ss)
    ensures forall m1, m2 : Msg | && m1 in ss.msgSent
                                  && m2 in ss.msgSent
                                  && ValidQC(m1.justify)
                                  && ValidQC(m2.justify)
                                  && m1.justify.cType == MT_Prepare
                                  && m2.justify.cType == MT_Prepare
                                  && m1.justify.viewNum <= m2.justify.viewNum
                                ::
                                  extension(m2.justify.block, m1.justify.block)
    {
        LemmaPrepareQCCanOnlyFormedByExtend(ss);
    }
    
    lemma LemmaPrepareQCCanOnlyFormedByExtend(ss : SystemState)
    requires ValidSystemState(ss)
    ensures forall m : Msg | && m in ss.msgSent
                             && ValidQC(m.justify)
                             && m.justify.cType == MT_Prepare
                          ::
                             forall m_acs : Msg | && m_acs in ss.msgSent
                                                  && ValidQC(m_acs.justify)
                                                  && m_acs.justify.cType == MT_Prepare
                                               ::
                                                  m_acs.justify.viewNum <= m.justify.viewNum
                                                  ==>
                                                  extension(m.justify.block, m_acs.justify.block)
    {
        
    }
                                                  

}
