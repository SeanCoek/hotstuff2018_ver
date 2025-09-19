include "Type.dfy"
include "Auxilarily.dfy"

module M_Replica {
    import opened M_SpecTypes
    import opened M_AuxilarilyFunc

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
        msgReceived : set<Msg>
    )

    /**
     *  Replica Initialization
     */
    ghost predicate ReplicaInit(r : ReplicaState, id : Address)
    {
        && r.id == id
        && r.bc == [M_SpecTypes.Genesis_Block]
        && r.viewNum == 1
        && r.prepareQC == CertNone
        && r.commitQC == CertNone
        && r.msgReceived == {}
    }

    lemma LemmaInitReplicaIsValid(r : ReplicaState)
    requires ReplicaInit(r, r.id)
    requires M_SpecTypes.All_Nodes != {}
    ensures ValidReplicaState(r)
    {
        
        assert Inv_Blockchain_Inner_Consistency(r.bc);
        assert r.commitQC.CertNone?;
        assert r.prepareQC.CertNone?;
        assert r.bc == [M_SpecTypes.Genesis_Block];
    }

    lemma LemmaReplicaNextSubIsValid(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires M_SpecTypes.All_Nodes != {}
    requires ValidReplicaState(r)
    requires ReplicaNextSubStep(r, r', outMsg)
    // ensures forall inMsg, outMsg | ReplicaNext(r, inMsg, r', outMsg)
    //                             :: ValidReplicaState(r')
    ensures ValidReplicaState(r')
    {
        
        if exists outMsg :: ReplicaNextSubStep(r, r', outMsg)
        {
            var outMsg :| ReplicaNextSubStep(r, r', outMsg);
            if UponPrepare(r, r', outMsg)
            {
                LemmaValidationHoldsInPreparePhase(r, r', outMsg);
            }
            else if UponPreCommit(r, r', outMsg)
            {
                LemmaValidationHoldsInPreCommitPhase(r, r', outMsg);
            }
            else if UponCommit(r, r', outMsg)
            {
                LemmaValidationHoldsInCommitPhase(r, r', outMsg);
            }
            else if UponDecide(r, r', outMsg)
            {
                LemmaValidationHoldsInDecidePhase(r, r', outMsg);
            }
            else
            {
                // UponNextView, UponTimeOut are proved automatically by Dafny
            }
        }
    }

    predicate Inv_Node_Constraint()
    {   
        && |M_SpecTypes.All_Nodes| > 0
        && |Adversary_Nodes| <= f(|All_Nodes|)
        && M_SpecTypes.Honest_Nodes * M_SpecTypes.Adversary_Nodes == {}
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
    {
        var allMsgReceived := r.msgReceived + inMsg;
        var replicaWithNewMsgReceived := r.(
            msgReceived := allMsgReceived
        );

        exists s : seq<ReplicaState>, o : seq<set<Msg>> ::
                && |s| > 2
                && |o| == |s| - 1
                && s[0] == replicaWithNewMsgReceived
                && s[|s|-1] == r'
                && (forall i | 0 <= i < |s| - 1 ::
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
    {
        || UponNextView(r, r', outMsg)
        || UponPrepare(r, r', outMsg)
        || UponPreCommit(r, r', outMsg)
        || UponCommit(r, r', outMsg)
        || UponDecide(r, r', outMsg)
        || UponTimeOut(r, r', outMsg)
    }

    predicate UponNextView(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    {
        var newViewMsg := Msg(MT_NewView, r.viewNum, EmptyBlock, r.prepareQC, SigNone);
        && r' == r.(
            viewNum := r.viewNum + 1
        )
        && outMsg == {newViewMsg}
        
    } 

    lemma LemmaTestValidationOfTransition(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    // requires UponNextView(r, r', outMsg)     Q.E.D
    // requires UponTimeOut(r, r', outMsg)      Q.E.D
    // requires UponPrepare(r, r', outMsg)      Q.E.D

    ensures ValidReplicaState(r')
    {
        // var leader := leader(r.viewNum);
        // if (leader == r.id){
        //     calc {
        //         r'.msgReceived;
        //         >=
        //         r.msgReceived;
        //     }
        // }
        // else {  // OBSERVE
        // }
    }

    lemma LemmaValidationHoldsInPreparePhase(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    // requires M_SpecTypes.All_Nodes != {}
    requires ValidReplicaState(r)
    requires UponPrepare(r, r', outMsg)
    ensures ValidReplicaState(r')
    {
    }

    lemma LemmaValidationHoldsInPreCommitPhase(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponPreCommit(r, r', outMsg)
    ensures ValidReplicaState(r')
    {
        var leader := leader(r.viewNum);
        assert r'.viewNum > 0;
        assert Inv_Blockchain_Inner_Consistency(r'.bc);
        assert (||(&& r'.commitQC.Cert?
               && r'.commitQC.block.Block?
               && r'.bc <= getAncestors(r'.commitQC.block)
               )
            ||(r'.commitQC.CertNone?)
            );
        assert && |r'.bc| > 0
               && r'.bc[0] == M_SpecTypes.Genesis_Block;
        
        assert (r'.prepareQC.Cert? ==>
                                && ValidQC(r'.prepareQC)
                                && r'.prepareQC.cType == MT_Prepare
                                && exists m | m in r'.msgReceived
                                            ::
                                            && m.mType.MT_PreCommit?
                                            && m.justify == r'.prepareQC
            ) by {
                if leader == r.id {
                    assert ValidQC(r'.prepareQC);
                    assert r'.prepareQC.cType == MT_Prepare;
                }
                else {
                    assert ValidQC(r'.prepareQC);
                }
        }
        
        assert (r'.commitQC.Cert? ==>
                                && ValidQC(r'.commitQC)
                                && r'.commitQC.cType == MT_PreCommit
                                && exists m | m in r'.msgReceived
                                            ::
                                            && m.mType.MT_Commit?
                                            && m.justify == r'.commitQC
            );

        assert (|| r'.bc == [M_SpecTypes.Genesis_Block]
                || (exists m | && m in r'.msgReceived
                            && m.mType.MT_Decide?
                            && m.justify.Cert?
                            && m.justify.cType.MT_Commit?
                            && ValidQC(m.justify)
                            && m.justify.block.Block?
                            ::
                            r'.bc <= getAncestors(m.justify.block)
                )
         );
    }

    lemma LemmaValidationHoldsInCommitPhase(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponCommit(r, r', outMsg)
    ensures ValidReplicaState(r')
    {

    }

    lemma LemmaValidationHoldsInDecidePhase(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponDecide(r, r', outMsg)
    ensures ValidReplicaState(r')
    {

    }


    predicate UponPrepare(r : ReplicaState, r' : ReplicaState, outMsg: set<Msg>)
    requires ValidReplicaState(r)
    {
        var leader := leader(r.viewNum);
        if leader == r.id // Leader
        then
            // assume r.viewNum > 0;
            var matchMsgs := getMatchMsg(r.msgReceived, MT_NewView, r.viewNum-1);
            var highQC := getHighQC(matchMsgs);
            var proposal := getNewBlock(highQC.block);
            var proposeMsg := Msg(MT_Prepare, r.viewNum, proposal, highQC, SigNone);

            var matchMsgs2 := getMatchMsg(r.msgReceived + {proposeMsg}, MT_Prepare, r.viewNum);
            && (forall m | m in matchMsgs2 ::
                    var sig := Signature(r.id, m.mType, m.viewNum, m.block);
                    var vote := Msg(MT_Prepare, r.viewNum, m.block, CertNone, sig);
                    
                    if  && m.block.Block?
                        && m.justify.Cert? 
                        && extension(m.block, m.justify.block) 
                        && r.commitQC.Cert?
                        && safeNode(m.block, m.justify, r.commitQC)
                    then
                        && outMsg == {vote, proposeMsg}
                    else
                        && outMsg == {proposeMsg}
                )
            && r' == r.(msgReceived := r.msgReceived + {proposeMsg})
        else
            var matchMsgs := getMatchMsg(r.msgReceived, MT_Prepare, r.viewNum);
            && (forall m | m in matchMsgs ::
                    var sig := Signature(r.id, m.mType, m.viewNum, m.block);
                    var vote := Msg(MT_Prepare, r.viewNum, m.block, CertNone, sig);
                    
                    if  && m.block.Block?
                        && m.justify.Cert? 
                        && extension(m.block, m.justify.block) 
                        && r.commitQC.Cert?
                        && safeNode(m.block, m.justify, r.commitQC)
                    then
                        && outMsg == {vote}
                    else
                        && outMsg == {}
                )
            && r' == r
    }

    ghost predicate UponPreCommit(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    {
        var leader := leader(r.viewNum);
        if leader == r.id // Leader
        then
            // Leader doing leader and replica's work
            var matchQCs := getMatchQC(r.msgReceived, MT_Prepare, r.viewNum);
            if |matchQCs| > 0 
            then 
                var m_qc :| m_qc in matchQCs;
                var sig := Signature(r.id, m_qc.cType, m_qc.viewNum, m_qc.block);
                var vote := Msg(MT_PreCommit, r.viewNum, m_qc.block, CertNone, sig);

                var matchMsgs := getMatchMsg(r.msgReceived, MT_Prepare, r.viewNum);
                // What if these message contain different voted blocks?
                // Split thess message by responding block, and get the group with the most elements.
                var splitSets := splitMsgByBlocks(matchMsgs);
                var maxSet :| && maxSet in splitSets
                              && (forall sset | sset in splitSets
                                        :: |maxSet| >= |sset|);
                if |maxSet| >= quorum(|M_SpecTypes.All_Nodes|)
                then
                    var m :| m in maxSet;
                    var sgns := ExtractSignatrues(maxSet);
                    var prepareQC := Cert(MT_Prepare, m.viewNum, m.block, sgns);
                    var precommitMsg := Msg(MT_PreCommit, r.viewNum, EmptyBlock, prepareQC, SigNone);
                    && r' == r.(msgReceived := r.msgReceived + {precommitMsg})
                    && r' == r.(prepareQC := m_qc)
                    && outMsg == {vote, precommitMsg}
                else
                    && r' == r.(prepareQC := m_qc)
                    && outMsg == {vote}
            else    // Only doing leader's work
                var matchMsgs := getMatchMsg(r.msgReceived, MT_Prepare, r.viewNum);
                var splitSets := splitMsgByBlocks(matchMsgs);
                var maxSet :| && maxSet in splitSets
                              && (forall sset | sset in splitSets
                                        :: |maxSet| >= |sset|);
                if |maxSet| >= quorum(|M_SpecTypes.All_Nodes|)
                then
                    var m :| m in maxSet;
                    var sgns := ExtractSignatrues(maxSet);
                    var prepareQC := Cert(MT_Prepare, m.viewNum, m.block, sgns);
                    var precommitMsg := Msg(MT_PreCommit, r.viewNum, EmptyBlock, prepareQC, SigNone);
                    && r' == r.(msgReceived := r.msgReceived + {precommitMsg})
                    && outMsg == {precommitMsg}
                else
                    && r' == r
                    && outMsg == {}
        else    // Only doing replica's work
            var matchQCs := getMatchQC(r.msgReceived, MT_Prepare, r.viewNum);
            // What if these QCs contain different certificated block? 
            // Impossible in theory, but have to prove it
            if |matchQCs| > 0 
            then 
                var m :| m in matchQCs;
                var sig := Signature(r.id, m.cType, m.viewNum, m.block);
                var vote := Msg(MT_PreCommit, r.viewNum, m.block, CertNone, sig);
                // var voteMsg := MsgWithRecipient(vote, leader);
                && r' == r.(prepareQC := m)
                && outMsg == {vote}
            
            else 
                && r' == r
                && outMsg == {}
    }

    ghost predicate UponCommit(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    // requires M_SpecTypes.All_Nodes != {}
    {
        var leader := leader(r.viewNum);
        if leader == r.id // Leader
        then
            var matchMsgs := getMatchMsg(r.msgReceived, MT_PreCommit, r.viewNum);
            if |matchMsgs| >= quorum(|M_SpecTypes.All_Nodes|)
            then
                var m :| m in matchMsgs;
                // forall m | m in matchMsgs
                //         ::
                var sgns := ExtractSignatrues(matchMsgs);
                var precommitQC := Cert(MT_PreCommit, m.viewNum, m.block, sgns);
                var commitMsg := Msg(MT_Commit, r.viewNum, EmptyBlock, precommitQC, SigNone);
                && r' == r.(msgReceived := r.msgReceived + {commitMsg})
                && outMsg == {commitMsg}
            else
                && r' == r
                && |outMsg| == 0
        else
            var matchQCs := getMatchQC(r.msgReceived, MT_PreCommit, r.viewNum);
            forall m | m in matchQCs ::
                var sig := Signature(r.id, m.cType, m.viewNum, m.block);
                var vote := Msg(MT_Commit, r.viewNum, m.block, CertNone, sig);
                // var voteMsg := MsgWithRecipient(vote, leader);
                && r' == r.(commitQC := m)
                && vote in outMsg
    }

    ghost predicate UponDecide(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires M_SpecTypes.All_Nodes != {}
    {
        var leader := leader(r.viewNum);
        if leader == r.id // Leader
        then
            var matchMsgs := getMatchMsg(r.msgReceived, MT_Commit, r.viewNum);
            if |matchMsgs| >= quorum(|M_SpecTypes.All_Nodes|)
            then
                var m :| m in matchMsgs;
                // forall m | m in matchMsgs
                //         ::
                var sgns := ExtractSignatrues(matchMsgs);
                var commitQC := Cert(MT_PreCommit, m.viewNum, m.block, sgns);
                var decideMsg := Msg(MT_Decide, r.viewNum, EmptyBlock, commitQC, SigNone);
                && r' == r.(msgReceived := r.msgReceived + {decideMsg})
                && outMsg == {decideMsg}
            else
                && r' == r
                && |outMsg| == 0
        else
            var matchQCs := getMatchQC(r.msgReceived, MT_Commit, r.viewNum);
            forall m | m in matchQCs ::
                && m.Cert?
                && m.block.Block?
                && var ancestors := getAncestors(m.block);
                && (
                    ||( && |ancestors| > |r.bc|
                        && r' == r.(
                                    bc := r.bc + ancestors[|r.bc|..])
                    )
                    || (&& |ancestors| <= |r.bc|
                        && r' == r)
                )
    }

    predicate UponTimeOut(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    {
        UponNextView(r, r', outMsg)
    }


    ghost predicate ValidReplicaState(s : ReplicaState)
    // requires M_SpecTypes.All_Nodes != {}
    {
        // TODO: invarians about a replica state
        //
        // && Inv_Node_Constraint()
        && s.viewNum > 0
        // The local blockchain should alwarys be consistent
        && Inv_Blockchain_Inner_Consistency(s.bc)
        // If a replica accepted a commit certificate, 
        // then the corresponding certified block should extend their local blockchain
        && (||(&& s.commitQC.Cert?
               && s.commitQC.block.Block?
               && s.bc <= getAncestors(s.commitQC.block)
               )
            ||(s.commitQC.CertNone?)
            )
        // If a replica accepted a Prepare certificate,
        // then it must received a PreCommit Message from the leader before, together with a valid Prepare certificate
        && (s.prepareQC.Cert? ==>
                                && ValidQC(s.prepareQC)
                                && s.prepareQC.cType == MT_Prepare
                                && exists m | m in s.msgReceived
                                            ::
                                            && m.mType.MT_PreCommit?
                                            && m.justify == s.prepareQC
            )
        // If a replica accepted a Precommit certificate (set it to its local variable `commitQC`),
        // then it must received a Commit Message from the leader before, together with a valid Precommit certificate
        && (s.commitQC.Cert? ==>
                                && ValidQC(s.commitQC)
                                && s.commitQC.cType == MT_PreCommit
                                && exists m | m in s.msgReceived
                                            ::
                                            && m.mType.MT_Commit?
                                            && m.justify == s.commitQC
            )
        // If a replica received a Decide Message with a valid certificate,
        // then it should always update its local blockchain accordingly.
        && (|| s.bc == [M_SpecTypes.Genesis_Block]
            || (exists m | && m in s.msgReceived
                           && m.mType.MT_Decide?
                           && m.justify.Cert?
                           && m.justify.cType.MT_Commit?
                           && ValidQC(m.justify)
                           && m.justify.block.Block?
                        ::
                           s.bc <= getAncestors(m.justify.block)
            )
        )
        && |s.bc| > 0
        && s.bc[0] == M_SpecTypes.Genesis_Block
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

}