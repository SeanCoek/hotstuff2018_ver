include "Type.dfy"
include "Auxilarily.dfy"
include "Axioms.dfy"
include "common/proofs.dfy"
include "Invariants.dfy"

module M_Replica {
    import opened M_SpecTypes
    import opened M_AuxilarilyFunc
    import opened M_Axiom
    import opened M_ProofTactic
    import opened M_Invariants

    /**
     *  Bookeeping variables for a replica
     *  id : identifier
     *  bc : local blockchain
     *  c  : configuration about nodes and genesis block
     *  viewNum : view number
     *  prepareQC : Quorum Certificate for prepare message
     *  commitQC : Qurum Certificate for pre-commit message, also refers to "lockQC" at the HotStuff paper
     *  msgReceived : all the messages recieved
     *  highestExecutedBlock : executed block with the highest view number
     */
    datatype ReplicaState = ReplicaState(
        id : Address,
        bc : Blockchain,
        // c : Configuration
        viewNum : nat,
        prepareQC : Cert,
        commitQC : Cert,
        msgReceived : set<Msg>,
        msgSent : set<Msg>
    )

    /**
     *  Replica Initialization
     */
    ghost predicate ReplicaInit(r : ReplicaState, id : Address)
    {
        && r.id == id
        && r.bc == [M_SpecTypes.Genesis_Block]
        && r.viewNum == 1
        && r.prepareQC == getInitialQC(MT_Prepare)
        && r.commitQC == getInitialQC(MT_PreCommit)
        && r.msgReceived == {getInitialMsg(id)}
        && r.msgSent == {getInitialMsg(id)}
    }

    ghost predicate ValidReplicaNextSubSeq(s : seq<ReplicaState>, o : seq<set<Msg>>)
    {
        && |s| > 2
        && |o| == |s| - 1
        // && s[0] == replicaWithNewMsgReceived
        // && s[|s|-1] == r'
        && (forall i | 0 <= i < |s| - 1 ::
            && ValidReplicaState(s[i])
            && ReplicaNextSubStep(s[i], s[i+1], o[i])
        )
        // && outMsg == setUnionOnSeq(o)
    }


    /**
     * Consider this as a big step of state transition.
     * A current state (@param:r) receives many messages (@param:inMsg), 
     * and then transfer to another state (@param:r') by many single actions defined in @Func:ReplicaNextSubStep,
     * sending out messages (@param:outMsg) during those transition path.
     */
    ghost predicate ReplicaNext(
        r : ReplicaState,
        inMsg : set<Msg>,
        r' : ReplicaState,
        // outMsg : set<MsgWithRecipient>
        outMsg : set<Msg>
        )
    requires ValidReplicaState(r)
    {
        var allMsgReceived := r.msgReceived + inMsg;
        var replicaWithNewMsgReceived := r.(
            msgReceived := allMsgReceived
        );
        assert ValidReplicaState(replicaWithNewMsgReceived);
        exists s : seq<ReplicaState>, o : seq<set<Msg>> ::
                && |s| > 2
                && |o| == |s| - 1
                && s[0] == replicaWithNewMsgReceived
                && s[|s|-1] == r'
                && (forall i | 0 <= i < |s| - 1 ::
                    && ValidReplicaState(s[i])
                    && ReplicaNextSubStep(s[i], s[i+1], o[i])
                )
                && outMsg == setUnionOnSeq(o)

    }

    /**
     *  All different state transition actions.
     *  Current state (@param:r) could transfer to the next state (@param:r'),
     *  together with sending out messages (@param:outMsg)
     */
    ghost predicate ReplicaNextSubStep(
        r : ReplicaState, 
        r' : ReplicaState, 
        outMsg : set<Msg>
        )
    requires ValidReplicaState(r)
    {
        || UponNextView(r, r', outMsg)
        || UponPrepare(r, r', outMsg)
        || UponPreCommit(r, r', outMsg)
        || UponCommit(r, r', outMsg)
        || UponDecide(r, r', outMsg)
        || UponTimeOut(r, r', outMsg)
    }


    // Refactor for outMsg (28/11/2025)
    predicate UponPrepare(r : ReplicaState, r' : ReplicaState, outMsg: set<Msg>)
    requires ValidReplicaState(r)
    {
        var leader := leader(r.viewNum);
        if leader == r.id // Leader
        then
            // assume r.viewNum > 0;
            var matchProposals := getMatchProposalMsg(r.msgReceived, r.viewNum);
            var votes := getVotesForSafeProposals(matchProposals, r.commitQC, r.id);
            var filteredVotes := proposalVoteFilter(votes);
            var matchMsgs := getMatchMsg(r.msgReceived, MT_NewView, r.viewNum-1);
            if |matchMsgs| > 0
            then
                var highQC := getHighQC(matchMsgs);
                assert ValidQC(highQC);
                var proposal := getNewBlock(highQC.block);
                var proposeMsg := Msg(r.id, MT_Prepare, r.viewNum, proposal, highQC, SigNone);
                // var matchProposals := getMatchProposalMsg(r.msgReceived + {proposeMsg}, r.viewNum);
                && outMsg == filteredVotes + {proposeMsg}
                && r' == r.(msgSent := r.msgSent + filteredVotes + {proposeMsg})
            else
                && outMsg == filteredVotes
                && r' == r.(msgSent := r.msgSent + filteredVotes)
        else
            var matchProposals := getMatchProposalMsg(r.msgReceived, r.viewNum);
            // NoOuterClient();
            var votes := getVotesForSafeProposals(matchProposals, r.commitQC, r.id);
            var filteredVotes := proposalVoteFilter(votes);
            && outMsg == filteredVotes
            && r' == r.(msgSent := r.msgSent + outMsg)
    }

    ghost predicate UponPreCommit(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    {
        var leader := leader(r.viewNum);
        assert r.prepareQC.Cert? ==> ValidQC(r.prepareQC);
        if leader == r.id // Leader
        then
            // Leader doing leader and replica's work
            var matchQCs := getMatchQC(r.msgReceived, MT_PreCommit, MT_Prepare, r.viewNum);
            if |matchQCs| > 0 
            then 
                var m_qc :| m_qc in matchQCs;
                var vote := buildVoteMsg(r.id, MT_PreCommit, m_qc.block, CertNone, r.viewNum, r.id);
                var matchMsgs := getMatchVoteMsg(r.msgReceived, MT_Prepare, r.viewNum);
                // What if these message contain different voted blocks?
                // Split thess message by responding block, and get the group with the most elements.
                var splitSets := splitMsgByBlocks(matchMsgs);
                var maxSet := getMaxLengthSet(splitSets);
                if |maxSet| >= quorum(|M_SpecTypes.All_Nodes|)
                then
                    Axiom_Common_Constraints();
                    var m :| m in maxSet;
                    // assert forall v1, v2 | v1 in maxSet && v2 in maxSet
                    //       :: 
                    //          v1 != v2
                    //          ==>
                    //          v1.partialSig.signer != v2.partialSig.signer;
                    var sgns := ExtractSignatrues(maxSet);
                    var prepareQC := Cert(MT_Prepare, m.viewNum, m.block, sgns);
                    assert ValidQC(prepareQC);
                    var precommitMsg := Msg(r.id, MT_PreCommit, r.viewNum, EmptyBlock, prepareQC, SigNone);
                    assert ValidQC(m_qc);
                    assert ValidPrecommitVote(vote);
                    assert ValidPrecommitRequest(precommitMsg);
                    && outMsg == {vote, precommitMsg}
                    && r' == r.(prepareQC := m_qc,
                                msgSent := r.msgSent + {vote, precommitMsg})
                else
                    assert ValidQC(m_qc);
                    && outMsg == {vote}
                    && r' == r.(prepareQC := m_qc,
                                msgSent := r.msgSent + {vote})
            else    // Only doing leader's work
                var matchMsgs := getMatchVoteMsg(r.msgReceived, MT_Prepare, r.viewNum);
                var splitSets := splitMsgByBlocks(matchMsgs);
                var maxSet := getMaxLengthSet(splitSets);
                assert r.prepareQC.Cert? ==> ValidQC(r.prepareQC);
                if |maxSet| >= quorum(|M_SpecTypes.All_Nodes|) && |maxSet| > 0
                then
                    var m :| m in maxSet;
                    var sgns := ExtractSignatrues(maxSet);
                    var prepareQC := Cert(MT_Prepare, m.viewNum, m.block, sgns);
                    // assert ValidQC(prepareQC);
                    var precommitMsg := Msg(r.id, MT_PreCommit, r.viewNum, EmptyBlock, prepareQC, SigNone);
                    assert ValidPrecommitRequest(precommitMsg);
                    && outMsg == {precommitMsg}
                    && r' == r.(msgSent := r.msgSent + {precommitMsg})
                else
                    assert r.prepareQC.Cert? ==> ValidQC(r.prepareQC);
                    && r' == r
                    && outMsg == {}
        else    // Only doing replica's work
            var matchQCs := getMatchQC(r.msgReceived, MT_PreCommit, MT_Prepare, r.viewNum);
            // What if these QCs contain different certificated block? 
            // Impossible in theory, but have to prove it
            if |matchQCs| > 0 
            then 
                var m_qc :| m_qc in matchQCs;
                assert exists m | m in r.msgReceived
                                ::
                                  && ValidMsg(m)
                                  && m.justify == m_qc;
                                
                var vote := buildVoteMsg(r.id, MT_PreCommit, m_qc.block, CertNone, r.viewNum, r.id);
                NoOuterClient();
                assert ValidPrecommitVote(vote);
                && outMsg == {vote}
                && r' == r.(prepareQC := m_qc,
                            msgSent := r.msgSent + {vote})
                && ValidQC(r'.prepareQC)
            else 
                && outMsg == {}
                && r' == r
            
    }

    ghost predicate UponCommit(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    {
        var leader := leader(r.viewNum);
        var matchQCs := getMatchQC(r.msgReceived, MT_Commit, MT_PreCommit, r.viewNum);
        if leader == r.id // Leader
        then
            // Leader doing leader and replica's work
            var matchMsgs := getMatchVoteMsg(r.msgReceived, MT_PreCommit, r.viewNum);
            // What if these message contain different voted blocks?
            // Split thess message by responding block, and get the group with the most elements.
            var splitSets := splitMsgByBlocks(matchMsgs);
            var maxSet := getMaxLengthSet(splitSets);
            if |matchQCs| > 0 
            then 
                var m_qc :| m_qc in matchQCs;

                var vote := buildVoteMsg(r.id, MT_Commit, m_qc.block, CertNone, r.viewNum, r.id);
                if |maxSet| >= quorum(|M_SpecTypes.All_Nodes|)
                then
                    Axiom_Common_Constraints();
                    var m :| m in maxSet;
                    var sgns := ExtractSignatrues(maxSet);
                    var precommitQC := Cert(MT_PreCommit, m.viewNum, m.block, sgns);
                    var commitMsg := Msg(r.id, MT_Commit, r.viewNum, EmptyBlock, precommitQC, SigNone);
                    assert ValidQC(precommitQC);
                    assert ValidQC(m_qc);
                    assert ValidCommitVote(vote);
                    assert ValidCommitRequest(commitMsg);
                    && outMsg == {vote, commitMsg}
                    && r' == r.(commitQC := m_qc,
                                msgSent := r.msgSent + {vote, commitMsg})
                else
                    assert ValidQC(m_qc);
                    && outMsg == {vote}
                    && r' == r.(commitQC := m_qc,
                                msgSent := r.msgSent + {vote})
            else    // Only doing leader's work
                if |maxSet| >= quorum(|M_SpecTypes.All_Nodes|) && |maxSet| > 0
                then
                    var m :| m in maxSet;
                    var sgns := ExtractSignatrues(maxSet);
                    var precommitQC := Cert(MT_PreCommit, m.viewNum, m.block, sgns);
                    var commitMsg := Msg(r.id, MT_Commit, r.viewNum, EmptyBlock, precommitQC, SigNone);
                    // assert ValidQC(r'.prepareQC);
                    && outMsg == {commitMsg}
                    && r' == r.(msgSent := r.msgSent + {commitMsg})
                else
                    // assert r.prepareQC.Cert? ==> ValidQC(r.prepareQC);
                    && r' == r
                    && outMsg == {}
        else    // Only doing replica's work
            // var matchQCs := getMatchQC(r.msgReceived, MT_PreCommit, r.viewNum);
            // What if these QCs contain different certificated block? 
            // Impossible in theory, but have to prove it
            if |matchQCs| > 0 
            then 
                var m_qc :| m_qc in matchQCs;
                var vote := buildVoteMsg(r.id, MT_Commit, m_qc.block, CertNone, r.viewNum, r.id);
                && outMsg == {vote}
                && r' == r.(commitQC := m_qc,
                            msgSent := r.msgSent + {vote})
                // && ValidQC(r'.prepareQC)
            else 
                && outMsg == {}
                && r' == r
    }

    ghost predicate UponDecide(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    {
        var leader := leader(r.viewNum);
        var matchMsgs := getMatchVoteMsg(r.msgReceived, MT_Commit, r.viewNum);
        var splitSets := splitMsgByBlocks(matchMsgs);
        var maxSet := getMaxLengthSet(splitSets);

        var matchQCs := getMatchQC(r.msgReceived, MT_Decide, MT_Commit, r.viewNum);

        if leader == r.id
        then
            if |matchQCs| > 0
            then
                var m_qc :| m_qc in matchQCs;
                if |maxSet| >= quorum(|M_SpecTypes.All_Nodes|)
                then
                    Axiom_Common_Constraints();
                    var m :| m in maxSet;
                    var sgns := ExtractSignatrues(maxSet);
                    var commitQC := Cert(MT_Commit, m.viewNum, m.block, sgns);
                    var decideMsg := Msg(r.id, MT_Decide, r.viewNum, EmptyBlock, commitQC, SigNone);
                    assert ValidQC(commitQC);
                    && outMsg == {decideMsg}
                    && r' == r.(msgSent := r.msgSent + {decideMsg})
                    && var ancestors := getAncestors(m_qc.block);
                    && (
                        || (
                            && r.bc < ancestors
                            && r' == r.(bc := r.bc + ancestors[|r.bc|..])
                            )
                        || (
                            // && |ancestors| <= |r.bc|
                            && r' == r
                            )
                    )
                else
                    && var ancestors := getAncestors(m_qc.block);
                    && (
                        || (
                            && r.bc < ancestors
                            && r' == r.(bc := r.bc + ancestors[|r.bc|..])
                            )
                        || (
                            // && |ancestors| <= |r.bc|
                            && r' == r
                            )
                    )
                    && outMsg == {}
            else    // |matchQCs| <= 0
                if |maxSet| >= quorum(|M_SpecTypes.All_Nodes|)
                then
                    Axiom_Common_Constraints();
                    var m :| m in maxSet;
                    var sgns := ExtractSignatrues(maxSet);
                    var commitQC := Cert(MT_Commit, m.viewNum, m.block, sgns);
                    var decideMsg := Msg(r.id, MT_Decide, r.viewNum, EmptyBlock, commitQC, SigNone);
                    && r' == r.(msgSent := r.msgSent + {decideMsg})
                    && outMsg == {decideMsg}
                else
                    && r' == r
                    && outMsg == {}
        else    // Not a leader
            if |matchQCs| > 0
            then
                var m_qc :| m_qc in matchQCs;
                var ancestors := getAncestors(m_qc.block);
                && (
                    || (
                        && r.bc < ancestors
                        && r' == r.(bc := r.bc + ancestors[|r.bc|..])
                        )
                    || (
                        && r' == r
                        )
                )
                && outMsg == {}
            else
                && r' == r
                && outMsg == {}
    }

    predicate UponTimeOut(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    {
        UponNextView(r, r', outMsg)
    }

    predicate UponNextView(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    {
        var newViewMsg := Msg(r.id, MT_NewView, r.viewNum, EmptyBlock, r.prepareQC, SigNone);
        && r' == r.(viewNum := r.viewNum + 1,
                    msgSent := r.msgSent + {newViewMsg})
        && outMsg == {newViewMsg}
        
    } 

    ghost predicate ValidReplicaState(r : ReplicaState)
    // requires M_SpecTypes.All_Nodes != {}
    {
        // TODO: invarians about a replica state
        //
        // && Inv_Node_Constraint()
        // && r.id in M_SpecTypes.All_Nodes
        && r.viewNum > 0
        // If a replica accepted a Prepare certificate,
        // then it must received a PreCommit Message from the leader before, together with a valid Prepare certificate
        && ValidQC(r.prepareQC)
        && (r.prepareQC.Cert? ==>
                                && ValidQC(r.prepareQC)
                                && r.prepareQC.cType == MT_Prepare
                                && ( || (exists m | m in r.msgReceived
                                            ::
                                            // && m.mType.MT_PreCommit?
                                            && m.justify == r.prepareQC
                                            && ValidPrecommitRequest(m)
                                        )
                                     || isInitialQC(r.prepareQC)
                                )
            )
        // If a replica accepted a Precommit certificate (set it to its local variable `commitQC`),
        // then it must received a Commit Message from the leader before, together with a valid Precommit certificate
        && (r.commitQC.Cert? ==>
                                && ValidQC(r.commitQC)
                                && r.commitQC.cType == MT_PreCommit
                                && (|| (exists m | m in r.msgReceived
                                            ::
                                            // && m.mType.MT_Commit?
                                            && m.justify == r.commitQC
                                            && ValidCommitRequest(m))
                                    || isInitialQC(r.commitQC)
                                )
            )
        // If a replica received a Decide Message with a valid certificate,
        // then it should always update its local blockchain accordingly.
        && (|| r.bc == [M_SpecTypes.Genesis_Block]
            || (exists m | && m in r.msgReceived
                        //    && m.justify.Cert?
                        //    && m.justify.cType.MT_Commit?
                        //    && ValidQC(m.justify)
                           && ValidDecideMsg(m)
                        ::
                           r.bc <= getAncestors(m.justify.block)
            )
        )
        && |r.bc| > 0
        && r.bc[0] == M_SpecTypes.Genesis_Block
        // && InvReplicaVote(s)
        && (forall m | m in r.msgSent :: ValidMsg(m))
        && (forall m | && m in r.msgSent
                       && ValidCommitVote(m)
                    :: 
                       exists m2 | m2 in r.msgReceived
                                ::
                                   && ValidCommitRequest(m2)
                                   && corrVoteMsgAndToVotedMsg(m, m2))
        && (forall m | && m in r.msgSent
                       && ValidPrecommitVote(m)
                    :: 
                       exists m2 | m2 in r.msgReceived
                                ::
                                   && ValidPrecommitRequest(m2)
                                   && corrVoteMsgAndToVotedMsg(m, m2))
    }

    ghost predicate InvReplicaVote(r : ReplicaState)
    {
        forall m | && m in r.msgSent
                   && ValidMsg(m)
                :: 
                   && m.partialSig.Signature?
                   && m.partialSig.mType.MT_Commit?
                   ==> 
                   exists m2 | m2 in r.msgReceived
                            ::
                               && ValidMsg(m2)
                               && ValidQC(m2.justify)
                               && m2.justify.cType.MT_PreCommit?
                               && m2.justify.block == m.partialSig.block
    }

    /**
     * Invariant: All Blockchain should be consistent by its own. Consistency -> the former block should be parent of the later block.
     */
    ghost predicate Inv_Blockchain_Inner_Consistency(b : Blockchain)
    {
        forall i1, i2 | 
                        && 0 < i2 <= |b|-1
                        && i1 == i2-1
                      ::
                        && b[i1].Block?
                        && b[i2].Block?
                        && b[i2].parent.Block?
                        && b[i1] == b[i2].parent
    }

    function getMsgReceiveReplica(r : ReplicaState) : (m : set<Msg>)
    {
        r.msgReceived
    }

    function getMsgSentReplica(r : ReplicaState) : (m : set<Msg>)
    {
        r.msgSent
    }

    function getReplicaID(r : ReplicaState) : (id : Address)
    { 
        r. id
    }

}