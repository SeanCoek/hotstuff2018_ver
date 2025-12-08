include "Type.dfy"
include "Auxilarily.dfy"
include "System.dfy"
include "Trace.dfy"
include "Replica.dfy"
include "Axioms.dfy"
include "common/sets.dfy"

module M_Lemma {
    import opened M_SpecTypes
    import opened M_AuxilarilyFunc
    import opened M_System
    import opened M_Trace
    import opened M_Replica
    import opened M_Axiom
    import opened M_Set

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
    
    lemma LemmaPrepareQCExtensionIfExistCommitQC(ss : SystemState)
    requires Reachable(ss)
    ensures forall m1, m2 | && m1 in ss.msgSent
                            && m2 in ss.msgSent
                            && msgWithValidQC(m1, MT_Prepare)
                            && msgWithValidQC(m2, MT_Prepare)
                            && m1.justify.viewNum <= m2.justify.viewNum
                            && (
                                exists m1_commit, m2_commit |
                                                              && m1_commit in ss.msgSent
                                                              && m2_commit in ss.msgSent
                                                              && msgWithValidQC(m1_commit, MT_Commit)
                                                              && msgWithValidQC(m2_commit, MT_Commit)
                                                            ::
                                                              && correspondingQC(m1.justify, m1_commit.justify)
                                                              && correspondingQC(m2.justify, m2_commit.justify)
                            )
                         :: 
                            extension(m2.justify.block, m1.justify.block)
    {
        // if SystemInit(ss) {
        //     // assert ss.msgSent == {};
        // }
        // else {
        //     forall m1, m2 | && m1 in ss.msgSent
        //                     && m2 in ss.msgSent
        //                     && msgWithValidQC(m1, MT_Prepare)
        //                     && msgWithValidQC(m2, MT_Prepare)
        //                     && m1.justify.viewNum <= m2.justify.viewNum
        //                     && (
        //                         exists m1_commit, m2_commit |
        //                                                       && m1_commit in ss.msgSent
        //                                                       && m2_commit in ss.msgSent
        //                                                       && msgWithValidQC(m1_commit, MT_Commit)
        //                                                       && msgWithValidQC(m2_commit, MT_Commit)
        //                                                     ::
        //                                                       && correspondingQC(m1.justify, m1_commit.justify)
        //                                                       && correspondingQC(m2.justify, m2_commit.justify)
        //                     )
        //     ensures extension(m2.justify.block, m1.justify.block)
        //     {
        //     }
        // }
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
                // if run[i-1] == run[i] {}
                // else {
                //     assert (exists replica, msgReceivedByNodes, msgSentByNodes
                //                     | msgReceivedByNodes <= run[i-1].msgSent
                //                     :: SystemNextByOneReplica(run[i-1], run[i], replica, msgReceivedByNodes, msgSentByNodes));
                //     LemmaSystemTransitionHoldsValidity(run[i-1], run[i]);
                // }
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



}
