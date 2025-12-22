include "Type.dfy"
include "Auxilarily.dfy"
include "System.dfy"
include "Trace.dfy"
include "Replica.dfy"
include "Axioms.dfy"
include "common/sets.dfy"
include "Lemmas_Replica.dfy"
include "Lemmas_System.dfy"

module M_Lemma {
    import opened M_SpecTypes
    import opened M_AuxilarilyFunc
    import opened M_System
    import opened M_Trace
    import opened M_Replica
    import opened M_Axiom
    import opened M_Set
    import opened M_Lemmas_Replica
    import opened M_Lemmas_System

    /*>>>>>>>>>>>>>>>>>>>>>>> START : Lemmas For Message Transmisson  */

    /* If an honest replica send out a vote message,
       then this message should be found in its output buffer (msgSent).
       The reason we can conclude this is that we assume signatures cannot
       be forged by byzantine nodes 
       TODO: It would be more rational if we make a new axiom to describe
             signatures cannot be forged, and use it to prove this lemma.
       */
    lemma LemmaExistVoteMsgForSignature(ss : SystemState)
    requires Reachable(ss)
    ensures forall sig : Signature |  && sig.Signature?
                                      && sig.signer in ss.nodeStates.Keys
                                      && IsHonest(ss, sig.signer)
                                   :: exists m | m in ss.nodeStates[sig.signer].msgSent
                                              :: 
                                                && ValidVoteMsg(m)
                                                && corrVoteMsg(sig, m)

    lemma LemmaExistValidMsgHoldingValidQC(ss : SystemState, qc : Cert)
    requires Reachable(ss)
    requires ValidQC(qc)
    ensures (exists m | m in ss.msgSent
                    ::
                        && ValidMsg(m)
                        && m.justify == qc)

    /*<<<<<<<<<<<<<<<<<<<<<<< END : Lemmas For Message Transmisson */


    lemma LemmaExistVoteMsgIfCertificateFormed(ss : SystemState)
    requires Reachable(ss)
    ensures forall m : Msg | && m in ss.msgSent
                             && ValidQC(m.justify)
                          ::
                             && (forall s : Signature | && s in m.justify.signatures
                                                        && s.Signature?
                                                        && IsHonest(ss, s.signer)
                                                     ::
                                                        && (exists m1 : Msg | && m1 in ss.msgSent
                                                                          ::
                                                                             corrVoteMsg(s, m1)
                                                            )
                                )
    {
        forall m | && m in ss.msgSent
                   && ValidQC(m.justify)
        ensures (forall s : Signature | && s in m.justify.signatures
                                        && s.Signature?
                                        && IsHonest(ss, s.signer)
                                     ::
                                        && (exists m1 : Msg | && m1 in ss.msgSent
                                                            ::
                                                              corrVoteMsg(s, m1)
                                            )
                                ) 
        {
            forall s : Signature | && s in m.justify.signatures
                                   && s.Signature?
                                   && IsHonest(ss, s.signer)
            ensures (exists m1 : Msg | && m1 in ss.msgSent
                                    ::
                                      corrVoteMsg(s, m1)
                    )
            {
                LemmaReachableStateIsValid(ss);
                LemmaExistVoteMsgForSignature(ss);
            }
        }
    }


    lemma LemmaMsgReceivedByReplicaIsSubsetOfAllMsgSentBySystem(ss : SystemState)
    requires Reachable(ss)
    ensures forall r, msgs | && IsHonest(ss, r)
                             && msgs == ss.nodeStates[r].msgReceived
                          ::
                             && msgs <= ss.msgSent
    {
        LemmaReachableStateIsValid(ss);
    }


    lemma LemmaExistValidPrepareQCForEveryValidPrecommitQC(ss : SystemState)
    requires Reachable(ss)
    ensures forall m : Msg | && m in ss.msgSent
                             && ValidQC(m.justify)
                             && m.justify.cType == MT_PreCommit
                          ::
                             && (exists m2 : Msg :: && m2 in ss.msgSent
                                                 && ValidQC(m2.justify)
                                                 && m2.justify.cType == MT_Prepare
                                                 && correspondingQC(m.justify, m2.justify)
                            )
    {
        forall m : Msg | && m in ss.msgSent
                                && ValidQC(m.justify)
                                && m.justify.cType == MT_PreCommit
        ensures (exists m2 : Msg :: && m2 in ss.msgSent
                                    && ValidQC(m2.justify)
                                    && m2.justify.cType == MT_Prepare
                                    && correspondingQC(m.justify, m2.justify)
                            )
        {
            var sgns := m.justify.signatures;
            var signers := set sig | sig in sgns :: sig.signer;
            LemmaExistHonestSignerInValidQC(ss, m.justify);
            LemmaReachableStateIsValid(ss);
            var sign_honest :| && sign_honest in sgns
                              && IsHonest(ss, sign_honest.signer);
            LemmaExistVoteMsgForSignature(ss);
            var corrVote :| && corrVote in ss.nodeStates[sign_honest.signer].msgSent
                            && ValidVoteMsg(corrVote)
                            && corrVoteMsg(sign_honest, corrVote);
            assert ValidPrecommitVote(corrVote);
            HonestReplicaVotePrecommitOnlyWhenItReceivePrepareQC(ss, sign_honest.signer);
        }
    }

    lemma LemmaExistValidPrecommitQCForEveryValidCommitQC(ss : SystemState)
    requires Reachable(ss)
    ensures forall m : Msg | && m in ss.msgSent
                             && ValidQC(m.justify)
                             && m.justify.cType == MT_Commit
                          ::
                             && (exists m2 : Msg :: && m2 in ss.msgSent
                                                    && ValidQC(m2.justify)
                                                    && m2.justify.cType == MT_PreCommit
                                                    && correspondingQC(m.justify, m2.justify)
                            )
    {
        forall m : Msg | && m in ss.msgSent
                                && ValidQC(m.justify)
                                && m.justify.cType == MT_Commit
        ensures (exists m2 : Msg :: && m2 in ss.msgSent
                                    && ValidQC(m2.justify)
                                    && m2.justify.cType == MT_PreCommit
                                    && correspondingQC(m.justify, m2.justify)
                            )
        {
            var sgns := m.justify.signatures;
            var signers := set sig | sig in sgns :: sig.signer;
            LemmaExistHonestSignerInValidQC(ss, m.justify);
            LemmaReachableStateIsValid(ss);
            var sign_honest :| && sign_honest in sgns
                              && IsHonest(ss, sign_honest.signer);
            LemmaExistVoteMsgForSignature(ss);
            var corrVote :| && corrVote in ss.nodeStates[sign_honest.signer].msgSent
                            && ValidVoteMsg(corrVote)
                            && corrVoteMsg(sign_honest, corrVote);
            assert ValidCommitVote(corrVote);
            HonestReplicaVoteCommitOnlyWhenItReceivePrecommitQC(ss, sign_honest.signer);
        }
    }


    lemma LemmaExistValidPrepareQCForEveryValidCommitQC(ss : SystemState)
    requires Reachable(ss)
    ensures forall m : Msg | && m in ss.msgSent
                             && ValidQC(m.justify)
                             && m.justify.cType == MT_Commit
                          ::
                             && (exists m2 : Msg :: && m2 in ss.msgSent
                                                    && ValidQC(m2.justify)
                                                    && m2.justify.cType == MT_Prepare
                                                    && correspondingQC(m.justify, m2.justify))
    {
        LemmaExistValidPrecommitQCForEveryValidCommitQC(ss);
        LemmaExistValidPrepareQCForEveryValidPrecommitQC(ss);
    }

    lemma LemmaHonestNodeWontVoteConflictInPrepare(
        ss : SystemState,
        r : Address,
        qc1_commit : Cert,
        qc2_prepare : Cert)
    requires Reachable(ss)
    requires IsHonest(ss, r)
    requires ValidQC(qc1_commit) && qc1_commit.cType.MT_Commit?
    requires ValidQC(qc2_prepare) && qc2_prepare.cType.MT_Prepare?
    requires predNodeInTwoQC(qc1_commit, qc2_prepare, r)
    requires qc2_prepare.viewNum >= qc1_commit.viewNum
    ensures extension(qc2_prepare.block, qc1_commit.block)
    {
        var rState := ss.nodeStates[r];
        LemmaReachableStateIsValid(ss);
        LemmaExistVoteMsgForSignature(ss);
        if qc2_prepare.viewNum == qc1_commit.viewNum {
            LemmaExistValidMsgHoldingValidQC(ss, qc1_commit);
            var m : Msg :| && m in ss.msgSent
                           && m.justify == qc1_commit;
            LemmaExistValidPrepareQCForEveryValidCommitQC(ss);
            LemmaSameValidQCInSameView(ss);
            assert qc2_prepare.block == qc1_commit.block;
        }
        else {
            // var vote1_cmt :| && vote1_cmt in rState.msgSent
            //                  && ValidCommitVote(vote1_cmt)
            //                  && vote1_cmt.viewNum == qc1_commit.viewNum
            //                  && vote1_cmt.block == qc1_commit.block;
            // var m2 :| && m2 in rState.msgReceived
            //           && ValidCommitRequest(m2)
            //           && corrVoteMsgAndToVotedMsg(vote1_cmt, m2);
            
            // At v1, r lock at qc1_commit.block
            // var lockedQC := m2.justify;
            // assert lockedQC.viewNum == qc1_commit.viewNum;
            // assert lockedQC.block == qc1_commit.block;
            // assert r in getMajoritySignerInValidQC(qc2_prepare);

            var vote2_pre :| && vote2_pre in rState.msgSent
                            && ValidPrepareVote(vote2_pre)
                            && vote2_pre.block == qc2_prepare.block;
            

            var proposal :| && proposal in rState.msgReceived
                            && ValidProposal(proposal)
                            && extension(proposal.block, proposal.justify.block)
                            && safeNode(proposal.block, proposal.justify, vote2_pre.lockedQC)
                            && extension(proposal.block, vote2_pre.lockedQC.block)
                            && proposal.block == vote2_pre.block;
            
            
            var vote1_cmt :| && vote1_cmt in rState.msgSent
                             && ValidCommitVote(vote1_cmt)
                             && vote1_cmt.viewNum == qc1_commit.viewNum
                             && vote1_cmt.block == qc1_commit.block;
            var m2 :| && m2 in rState.msgReceived
                      && ValidCommitRequest(m2)
                      && corrVoteMsgAndToVotedMsg(vote1_cmt, m2);
            
            assert qc2_prepare.viewNum > qc1_commit.viewNum;
            assert proposal.viewNum == qc2_prepare.viewNum;
            assert qc1_commit.viewNum == vote1_cmt.viewNum;
            assert vote1_cmt.viewNum == m2.viewNum;
            assert m2.justify.block == vote1_cmt.block;

            assert proposal.viewNum > m2.viewNum;
            assert extension(proposal.block, m2.justify.block);

            // assert || extension(proposal.block, vote2_pre.lockedQC.block)
            //         || proposal.justify.viewNum > vote2_pre.lockedQC.viewNum;


            // if extension(proposal.block, vote2_pre.lockedQC.block) {

            // }
            // else {
            //     assert proposal.justify.viewNum > vote2_pre.lockedQC.viewNum;
            //     assume extension(qc2_prepare.block, qc1_commit.block);
            // }
            // assert proposal.viewNum == qc2_prepare.viewNum;

            // assert extension(proposal.block, vote2_pre.lockedQC.block);
        }

    }


    lemma LemmaReachableStateIsValid(ss : SystemState)
    requires Reachable(ss)
    ensures ValidSystemState(ss)
    {
        if !SystemInit(ss) {
            var run : seq<SystemState> :|
                                            && |run| > 1
                                            && SystemInit(run[0])
                                            && run[|run|-1] == ss
                                            && (forall i | 0 <= i < |run|-1
                                                        :: 
                                                           && ValidSystemState(run[i])
                                                           && SystemNext(run[i], run[i+1]));
            forall i | 0 < i <= |run|-1
            ensures ValidSystemState(run[i]) {
                LemmaSystemTransitionHoldsValidity(run[i-1], run[i]);
            }
        } else {

        }
    }

    lemma LemmaPrepareVoteOnlyExistInPreparePhase(
        r : ReplicaState,
        inMsg : set<Msg>,
        r' : ReplicaState,
        outMsg : set<Msg>
    )
    requires ValidReplicaState(r)
    requires ReplicaNextSubStep(r, r', outMsg)
    ensures forall m | && m in outMsg 
                    ::
                       && m.partialSig.Signature?
                       && m.mType == MT_Prepare
                       ==>
                       UponPrepare(r, r', outMsg)
    {

    }

    lemma HonestReplicaVoteCommitOnlyWhenItReceivePrecommitQC(ss : SystemState, r : Address)
    requires Reachable(ss)
    requires IsHonest(ss, r)
    ensures forall m | && m in ss.nodeStates[r].msgSent
                       && ValidCommitVote(m)
                    :: 
                    //    && m.partialSig.mType.MT_Commit?
                    //    && m.partialSig.Signature?
                    //    ==>
                       exists m2 | m2 in ss.nodeStates[r].msgReceived
                                ::
                                   && ValidCommitRequest(m2)
                                   && corrVoteMsgAndToVotedMsg(m, m2)
    {
        LemmaReachableStateIsValid(ss);
    }

    lemma HonestReplicaVotePrecommitOnlyWhenItReceivePrepareQC(ss : SystemState, r : Address)
    requires Reachable(ss)
    requires IsHonest(ss, r)
    ensures forall m | && m in ss.nodeStates[r].msgSent
                       && ValidPrecommitVote(m)
                    :: 
                       exists m2 | m2 in ss.nodeStates[r].msgReceived
                                ::
                                   && ValidPrecommitRequest(m2)
                                   && corrVoteMsgAndToVotedMsg(m, m2)
    {
        LemmaReachableStateIsValid(ss);
    }

    lemma LemmaCommitQCVoteOnlyExistCorrespondingPrecommitQC(
        r : ReplicaState,
        inMsg : set<Msg>,
        r' : ReplicaState,
        outMsg : set<Msg>
    )
    requires ValidReplicaState(r)
    requires ReplicaNext(r, inMsg, r', outMsg)
    ensures forall m | && m in outMsg
                       && ValidCommitVote(m)
                    :: 
                       exists m2 | m2 in r'.msgReceived
                                :: 
                                   && ValidQC(m2.justify)
                                   && m2.justify.cType.MT_PreCommit?
                                   && m2.justify.block == m.partialSig.block
                                   && m2.justify.viewNum == m.partialSig.viewNum
    {
        forall m | && m in outMsg
                   && ValidCommitVote(m)
        ensures exists m2 | m2 in r'.msgReceived
                         :: 
                            && ValidQC(m2.justify)
                            && m2.justify.cType.MT_PreCommit?
                            && m2.justify.block == m.partialSig.block
                            && m2.justify.viewNum == m.partialSig.viewNum
        {
            // var allMsgReceived := r.msgReceived + inMsg;
            var replicaWithNewMsgReceived := r.(
                msgReceived := r.msgReceived + inMsg
            );
            var s : seq<ReplicaState>, o : seq<set<Msg>> :|
                && |s| > 2
                && |o| == |s| - 1
                && s[0] == replicaWithNewMsgReceived
                && s[|s|-1] == r'
                && (forall i | 0 <= i < |s| - 1 ::
                    && ValidReplicaState(s[i])
                    && ReplicaNextSubStep(s[i], s[i+1], o[i])
                )
                && outMsg == setUnionOnSeq(o);
            assert exists i | 0 <= i < |o| :: m in o[i] by {
                LemmaElementInSetUnionOnSeqMustExistInOneOfTheSets(m, o);
            }
            var i :| 0 <= i < |o| && m in o[i];
            assert  && UponCommit(s[i], s[i+1], o[i])
                    && (exists m3 | m3 in r'.msgReceived
                                :: 
                                && ValidQC(m3.justify)
                                && m3.justify.cType.MT_PreCommit?
                                && m3.justify.block == m.partialSig.block
                                && m3.justify.viewNum == m.partialSig.viewNum) by {
                assert ValidReplicaState(s[i]);
                assert ReplicaNextSubStep(s[i], s[i+1], o[i]);
                LemmaReplicaVoteCommitOnlyWhenReceiveValidPrecommitQC(s[i], s[i+1], o[i]);
                assert r'.msgReceived == s[i+1].msgReceived by {
                    assert r' == s[|s|-1];
                    LemmaReplicaMsgReceiveStableInNextSubSeq(s, o);
                }
            }
            
        }
    }

    /**
        Lemmas for Quorum Certificate
     */
    lemma LemmaExistHonestSignerInValidQC(ss : SystemState, qc : Cert)
    requires Reachable(ss)
    requires ValidQC(qc)
    ensures exists sig | sig in qc.signatures
                       ::
                         IsHonest(ss, sig.signer)
    {
        var sgns := qc.signatures;
        assert |sgns| >= quorum(|M_SpecTypes.All_Nodes|);
        var signers := set sig | sig in sgns :: sig.signer;
        NumVoters(sgns);
        assert |signers| >= quorum(|M_SpecTypes.All_Nodes|);
        Axiom_Common_Constraints();
        Axiom_Byz_Constraints();
        LemmaHonestInQuorum(M_SpecTypes.All_Nodes,
                            M_SpecTypes.Adversary_Nodes,
                            signers);
        var honest :| && honest in signers
                      && honest in M_SpecTypes.Honest_Nodes;
        assert All_Nodes == Honest_Nodes + Adversary_Nodes;
        assert Honest_Nodes * Adversary_Nodes == {};
        LemmaAdditiveOnSeparateSet(All_Nodes, Adversary_Nodes, Honest_Nodes);
        assert Honest_Nodes == All_Nodes - Adversary_Nodes;
        LemmaReachableStateIsValid(ss);
        assert IsHonest(ss, honest);
    }

    lemma LemmaExistSameHonestNodeInTwoValidQC(
        ss : SystemState,
        qc1 : Cert,
        qc2 : Cert
    )
    requires Reachable(ss)
    requires ValidQC(qc1) && ValidQC(qc2)
    ensures var signers1 := getMajoritySignerInValidQC(qc1);
            var signers2 := getMajoritySignerInValidQC(qc2);
            exists r | IsHonest(ss, r)
                    ::
                       && r in signers1
                       && r in signers2
    {
        var signers1 := getMajoritySignerInValidQC(qc1);
        var signers2 := getMajoritySignerInValidQC(qc2);
        LemmaReachableStateIsValid(ss);
        LemmaTwoQuorumIntersection(All_Nodes, Adversary_Nodes, signers1, signers2);
    }

    lemma LemmaHonestNodeOnlyVoteOnceInOneView(
        ss : SystemState,
        r : Address
    )
    requires Reachable(ss)
    requires IsHonest(ss, r)
    ensures forall v1, v2 | && v1 in ss.nodeStates[r].msgSent
                            && v2 in ss.nodeStates[r].msgSent
                            && ValidVoteMsg(v1)
                            && ValidVoteMsg(v2)
                          ::
                            && v1.mType == v2.mType
                            && v1.viewNum == v2.viewNum
                            ==>
                            v1 == v2

    lemma LemmaSameValidQCInSameView(ss : SystemState)
    requires Reachable(ss)
    ensures forall cert1, cert2 | && ValidQC(cert1)
                                    && ValidQC(cert2)
                                    && cert1.cType == cert2.cType
                                    && cert1.viewNum == cert2.viewNum
                                ::
                                    cert1.block == cert2.block
    {

        forall cert1, cert2 | && ValidQC(cert1)
                                    && ValidQC(cert2)
                                    && cert1.cType == cert2.cType
                                    && cert1.viewNum == cert2.viewNum
        ensures cert1.block == cert2.block
        {
            LemmaReachableStateIsValid(ss);
            LemmaExistSameHonestNodeInTwoValidQC(ss, cert1, cert2);
            var signers1 := getMajoritySignerInValidQC(cert1);
            var signers2 := getMajoritySignerInValidQC(cert2);
            var replica :| IsHonest(ss, replica) && replica in signers1 * signers2;
            var rState := ss.nodeStates[replica];

            LemmaExistVoteMsgForSignature(ss);
            var sign1 :| && sign1 in cert1.signatures
                         && sign1.signer == replica;
            var sign2 :| && sign2 in cert2.signatures
                         && sign2.signer == replica;
            var v1 :| && v1 in rState.msgSent
                      && ValidVoteMsg(v1)
                      && corrVoteMsg(sign1, v1);
            var v2 :| && v2 in rState.msgSent
                      && ValidVoteMsg(v2)
                      && corrVoteMsg(sign2, v2);

            LemmaHonestNodeOnlyVoteOnceInOneView(ss, replica);
            assert v1.block == v2.block;
        }
    }

    lemma LemmaQCAtView0(
        ss : SystemState,
        qc : Cert)
    requires Reachable(ss)
    requires ValidQC(qc) && qc.viewNum == 0
    ensures qc.block == Genesis_Block

}
