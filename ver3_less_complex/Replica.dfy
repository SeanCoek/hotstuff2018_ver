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
     *  commitQC : Qurum Certificate for commit message, also refers to "lockQC" at the HotStuff paper
     *  msgRecieved : all the messages recieved
     *  highestExecutedBlock : executed block with the highest view number
     */
    datatype ReplicaState = ReplicaState(
        id : Address,
        bc : Blockchain,
        c : Configuration,
        viewNum : nat,
        prepareQC : Cert,
        commitQC : Cert,
        msgRecieved : set<Msg>,
        highestExecutedBlock : Block
    )

    /**
     *  Replica Initialization
     */
    predicate ReplicaInit(r : ReplicaState, id : Address, c : Configuration) 
    {
        && r.id == id
        && r.bc == [c.genesisBlock]
        && r.c == c
        && r.viewNum == 1
        && r.prepareQC == CertNone
        && r.commitQC == CertNone
        && r.msgRecieved == {}
        && r.highestExecutedBlock == EmptyBlock
    }


    /**
     * Consider this as a big step of state transition.
     * A current state (@param:r) recieves many messages (@param:inMsg), 
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
        var allMsgReceived := r.msgRecieved + inMsg;
        var replicaWithNewMsgReceived := r.(
            msgRecieved := allMsgReceived
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
        // outMsg : set<MsgWithRecipient>
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
    {
        var newLeader := leader(r.viewNum+1, r.c);
        // var newViewMsg := MsgWithRecipient(Msg(MT_NewView, r.viewNum, EmptyBlock, r.prepareQC, SigNone), newLeader);
        var newViewMsg := Msg(MT_NewView, r.viewNum, EmptyBlock, r.prepareQC, SigNone);
        && r' == r.(
            viewNum := r.viewNum + 1
        )
        && outMsg == {newViewMsg}
    }

    predicate UponPrepare(r : ReplicaState, r' : ReplicaState, outMsg: set<Msg>)
    {
        var leader := leader(r.viewNum, r.c);
        if leader == r.id // Leader
        then
            assume r.viewNum > 0;
            var matchMsgs := getMatchMsg(r.msgRecieved, MT_NewView, r.viewNum-1);
            var highQC := getHighQC(matchMsgs);
            var proposal := getNewBlock(highQC.block);
            var proposeMsg := Msg(MT_Prepare, r.viewNum, proposal, highQC, SigNone);

            && r' == r.(msgRecieved := r.msgRecieved + {proposeMsg})
            // && outMsg == Multicast(proposeMsg, r.c.nodes)
            && outMsg == {proposeMsg}

        else
            var matchMsgs := getMatchMsg(r.msgRecieved, MT_Prepare, r.viewNum);
            forall m | m in matchMsgs ::
                var sig := Signature(r.id, m.mType, m.viewNum, m.block);
                var vote := Msg(MT_Prepare, r.viewNum, m.block, CertNone, sig);
                // var voteMsg := MsgWithRecipient(vote, leader);
                
                if && m.block.Block?
                   && m.justify.Cert? 
                   && extension(m.block, m.justify.block) 
                   && r.commitQC.Cert?
                   && safeNode(m.block, m.justify, r.commitQC)
                then
                    // vote in outMsg
                    outMsg == {vote}
                else
                    !(vote in outMsg)
                    // outMsg == {}
    }

    ghost predicate UponPreCommit(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    {
        var leader := leader(r.viewNum, r.c);
        if leader == r.id // Leader
        then
            var matchMsgs := getMatchMsg(r.msgRecieved, MT_Prepare, r.viewNum);
            if |matchMsgs| >= quorum(|r.c.nodes|)
            then
                // var m :| m in matchMsgs;
                // forall m | m in matchMsgs
                //         ::
                var m :| m in matchMsgs;
                var sgns := ExtractSignatrues(matchMsgs);
                var prepareQC := Cert(MT_Prepare, m.viewNum, m.block, sgns);
                var precommitMsg := Msg(MT_PreCommit, r.viewNum, EmptyBlock, prepareQC, SigNone);
                && r' == r.(msgRecieved := r.msgRecieved + {precommitMsg})
                // && outMsg == Multicast(precommitMsg, r.c.nodes)
                && outMsg == {precommitMsg}
            else
                && r' == r
                && |outMsg| == 0
        else
            var matchQCs := getMatchQC(r.msgRecieved, MT_Prepare, r.viewNum);
            forall m | m in matchQCs ::
                var sig := Signature(r.id, m.cType, m.viewNum, m.block);
                var vote := Msg(MT_PreCommit, r.viewNum, m.block, CertNone, sig);
                // var voteMsg := MsgWithRecipient(vote, leader);
                && r' == r.(prepareQC := m)
                && vote in outMsg
                
    }

    ghost predicate UponCommit(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    {
        var leader := leader(r.viewNum, r.c);
        if leader == r.id // Leader
        then
            var matchMsgs := getMatchMsg(r.msgRecieved, MT_PreCommit, r.viewNum);
            if |matchMsgs| >= quorum(|r.c.nodes|)
            then
                var m :| m in matchMsgs;
                // forall m | m in matchMsgs
                //         ::
                var sgns := ExtractSignatrues(matchMsgs);
                var precommitQC := Cert(MT_PreCommit, m.viewNum, m.block, sgns);
                var commitMsg := Msg(MT_Commit, r.viewNum, EmptyBlock, precommitQC, SigNone);
                && r' == r.(msgRecieved := r.msgRecieved + {commitMsg})
                && outMsg == {commitMsg}
            else
                && r' == r
                && |outMsg| == 0
        else
            var matchQCs := getMatchQC(r.msgRecieved, MT_PreCommit, r.viewNum);
            forall m | m in matchQCs ::
                var sig := Signature(r.id, m.cType, m.viewNum, m.block);
                var vote := Msg(MT_Commit, r.viewNum, m.block, CertNone, sig);
                // var voteMsg := MsgWithRecipient(vote, leader);
                && r' == r.(commitQC := m)
                && vote in outMsg
    }

    ghost predicate UponDecide(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    {
        var leader := leader(r.viewNum, r.c);
        if leader == r.id // Leader
        then
            var matchMsgs := getMatchMsg(r.msgRecieved, MT_Commit, r.viewNum);
            if |matchMsgs| >= quorum(|r.c.nodes|)
            then
                var m :| m in matchMsgs;
                // forall m | m in matchMsgs
                //         ::
                var sgns := ExtractSignatrues(matchMsgs);
                var commitQC := Cert(MT_PreCommit, m.viewNum, m.block, sgns);
                var decideMsg := Msg(MT_Decide, r.viewNum, EmptyBlock, commitQC, SigNone);
                && r' == r.(msgRecieved := r.msgRecieved + {decideMsg})
                && outMsg == {decideMsg}
            else
                && r' == r
                && |outMsg| == 0
        else
            var matchQCs := getMatchQC(r.msgRecieved, MT_Commit, r.viewNum);
            forall m | m in matchQCs ::
                && r' == r.(
                    bc := r.bc + [m.block]
                )
    }

    predicate UponTimeOut(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    {
        UponNextView(r, r', outMsg)
    }


    predicate ValidReplicaState(s : ReplicaState)
    {
        // TODO: invarians about a replica state
        true
    }

}