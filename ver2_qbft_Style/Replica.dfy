include "Type.dfy"
include "Auxilarily.dfy"

module M_Replica {
    import opened M_SpecTypes
    import opened M_AuxilarilyFunc

    /**
     *  Bookeeping variables for a node
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
     *  All different transition states.
     *  Current state (r) could transfer to the next state (r'), together with sending out some messages (outMsg)
     */
    predicate ReplicaNext(r : ReplicaState, r' : ReplicaState, outMsg : set<MsgWithRecipient>)
    {
        || UponNextView(r, r', outMsg)
        || UponPrepare(r, r', outMsg)
        || UponPreCommit(r, r', outMsg)
        || UponCommit(r, r', outMsg)
        || UponDecide(r, r', outMsg)
        || UponTimeOut(r, r', outMsg)
    }

    predicate UponNextView(r : ReplicaState, r' : ReplicaState, outMsg : set<MsgWithRecipient>)
    {
        var newLeader := leader(r.viewNum+1, r.c);
        var newViewMsg := MsgWithRecipient(Msg(MT_NewView, r.viewNum, EmptyBlock, r.prepareQC, SigNone), newLeader);
        && r' == r.(
            viewNum := r.viewNum + 1
        )
        && outMsg == {newViewMsg}
    }

    predicate UponPrepare(r : ReplicaState, r' : ReplicaState, outMsg: set<MsgWithRecipient>)
    {
        var leader := leader(r.viewNum, r.c);
        if leader == r.id // Leader
        then
            var matchMsgs := getMatchMsg(r.msgRecieved, MT_NewView, r.viewNum-1);
            var highQC := getHighQC(matchMsgs);
            var proposal := getNewBlock(highQC.node);
            var proposeMsg := Msg(MT_Prepare, r.viewNum, proposal, highQC, SigNone);

            && r' == r.(msgRecieved := r.msgRecieved + {proposeMsg})
            && outMsg == Multicast(proposeMsg, r.c.nodes)

        else
            var matchMsgs := getMatchMsg(r.msgRecieved, MT_Prepare, r.viewNum);
            forall m | m in matchMsgs ::
                var sig := Signature(r.id, m.mType, m.viewNum, m.node);
                var vote := Msg(MT_Prepare, r.viewNum, m.node, CertNone, sig);
                var voteMsg := MsgWithRecipient(vote, leader);
                if extension(m.node, m.justify.node)
                    && safeNode(m.node, m.justify, r.commitQC)
                then
                    voteMsg in outMsg
                else
                    !(voteMsg in outMsg)
    }  

    predicate UponPreCommit(r : ReplicaState, r' : ReplicaState, outMsg : set<MsgWithRecipient>)
    {
        var leader := leader(r.viewNum, r.c);
        if leader == r.id // Leader
        then
            var matchMsgs := getMatchMsg(r.msgRecieved, MT_Prepare, r.viewNum);
            if |matchMsgs| >= quorum(|r.c.nodes|)
            then
                var m :| m in matchMsgs;
                var sgns := ExtractSignatrues(matchMsgs);
                // var signatures := m.partialSig;
                var prepareQC := Cert(MT_Prepare, m.viewNum, m.node, sgns);
                var precommitMsg := Msg(MT_PreCommit, r.viewNum, EmptyBlock, prepareQC, SigNone);
                && r' == r.(msgRecieved := r.msgRecieved + {precommitMsg})
                && outMsg == Multicast(precommitMsg, r.c.nodes)
            else
                && r' == r
                && |outMsg| == 0
        else
            var matchQCs := getMatchQC(r.msgRecieved, MT_Prepare, r.viewNum);
            forall m | m in matchQCs ::
                var sig := Signature(r.id, m.cType, m.viewNum, m.node);
                var vote := Msg(MT_PreCommit, r.viewNum, m.node, CertNone, sig);
                var voteMsg := MsgWithRecipient(vote, leader);
                && r' == r.(prepareQC := m)
                && voteMsg in outMsg
                
    }

    predicate UponCommit(r : ReplicaState, r' : ReplicaState, outMsg : set<MsgWithRecipient>)
    {
        var leader := leader(r.viewNum, r.c);
        if leader == r.id // Leader
        then
            var matchMsgs := getMatchMsg(r.msgRecieved, MT_PreCommit, r.viewNum);
            if |matchMsgs| >= quorum(|r.c.nodes|)
            then
                var m :| m in matchMsgs;
                var sgns := ExtractSignatrues(matchMsgs);
                var precommitQC := Cert(MT_PreCommit, m.viewNum, m.node, sgns);
                var commitMsg := Msg(MT_Commit, r.viewNum, EmptyBlock, precommitQC, SigNone);
                && r' == r.(msgRecieved := r.msgRecieved + {commitMsg})
                && outMsg == Multicast(commitMsg, r.c.nodes)
            else
                && r' == r
                && |outMsg| == 0
        else
            var matchQCs := getMatchQC(r.msgRecieved, MT_PreCommit, r.viewNum);
            forall m | m in matchQCs ::
                var sig := Signature(r.id, m.cType, m.viewNum, m.node);
                var vote := Msg(MT_Commit, r.viewNum, m.node, CertNone, sig);
                var voteMsg := MsgWithRecipient(vote, leader);
                && r' == r.(commitQC := m)
                && voteMsg in outMsg
    }

    predicate UponDecide(r : ReplicaState, r' : ReplicaState, outMsg : set<MsgWithRecipient>)
    {
        var leader := leader(r.viewNum, r.c);
        if leader == r.id // Leader
        then
            var matchMsgs := getMatchMsg(r.msgRecieved, MT_Commit, r.viewNum);
            if |matchMsgs| >= quorum(|r.c.nodes|)
            then
                var m :| m in matchMsgs;
                var sgns := ExtractSignatrues(matchMsgs);
                var commitQC := Cert(MT_PreCommit, m.viewNum, m.node, sgns);
                var decideMsg := Msg(MT_Decide, r.viewNum, EmptyBlock, commitQC, SigNone);
                && r' == r.(msgRecieved := r.msgRecieved + {decideMsg})
                && outMsg == Multicast(decideMsg, r.c.nodes)
            else
                && r' == r
                && |outMsg| == 0
        else
            var matchQCs := getMatchQC(r.msgRecieved, MT_Commit, r.viewNum);
            forall m | m in matchQCs ::
                && r' == r.(
                    bc := r.bc + [m.node]
                )
    }

    predicate UponTimeOut(r : ReplicaState, r' : ReplicaState, outMsg : set<MsgWithRecipient>)
    {
        UponNextView(r, r', outMsg)
    }


    predicate ValidReplicaState(s : ReplicaState)
    {
        // TODO: invarians about a node state
        true
    }

}