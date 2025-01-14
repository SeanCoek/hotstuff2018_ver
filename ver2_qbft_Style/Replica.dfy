include "Type.dfy"
include "Auxilarily.dfy"

module M_Replica {
    import opened M_SpecTypes
    import opened M_AuxilarilyFunc

    datatype ReplicaState = ReplicaState(
        id : Address,
        bc : Blockchain,
        c : Configuration,
        viewNum : nat,
        prepareQC : Cert,
        commitQC : Cert,
        msgRecieved : set<Msg>
    )

    predicate ReplicaInit(r : ReplicaState, id : Address, c : Configuration) 
    {
        && r.c == c
        && r.round == 0
        && r.bc == [c.genesisBlock]
        && r.id == id
        && r.prepareQC == None
        && r.commitQC == None
    }

    predicate ReplicaNext(r : ReplicaState, r' : ReplicaState, outMsg : set<MsgWithRecipient>)
    {
        || UponNextView(r, r')
        || UponPrepare(r, r')
        || UponPreCommit(r, r')
        || UponCommit(r, r')
        || UponDecide(r, r')
        || UponTimeOut(r, r')
    }

    predicate UponNextView(r : ReplicaState, r' : ReplicaState, outMsg : set<MsgWithRecipient>)
    {
        var newLeader := leader(r.viewNum+1, r.c);
        var newViewMsg := MsgWithRecipient(Msg(MT_NewView, None, r.prepareQC), leader);
        && r' == r.(
            viewNum := viewNum + 1
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
            var proposeMsg := Msg(MT_Prepare, r.viewNum, proposal, highQC);

            && r' == r.(msgRecieved := r.msgRecieved + {proposeMsg})
            && outMsg == Multicast(proposeMsg, r.c.nodes)

        else
            var matchMsgs := getMatchMsg(r.msgRecieved, MT_Prepare, r.viewNum);
            forall m | m in matchMsgs ::
                var sig := Signature(r.Address, m.mType, m.viewNum, m.node);
                var vote := Msg(MT_Prepare, r.viewNum, m.node, None, sig);
                var voteMsg := MsgWithRecipient(vote, leader);
                if extension(m.node, m.justify.node)
                    && safeNode(m.node, m.justify, r.lockedQC)
                then
                    vote in outMsg
                else
                    !(vote in outMsg)
    }  

    predicate UponPreCommit(r : ReplicaState, r' : ReplicaState, outMsg : set<MsgWithRecipient>)
    {
        var leader := leader(r.viewNum, r.c);
        if leader == r.id // Leader
        then
            var matchMsgs := getMatchMsg(r.msgRecieved, MT_Prepare, r.viewNum);
            if |matchMsgs| >= quorum(|r.c.nodes|)
            then
                var signatures := v.partialSig | v in matchMsgs;
                var prepareQc := Cert(MT_Prepare, matchMsgs[0].viewNum, matchMsgs[0].node, signatures);
                var precommitMsg := Msg(MT_PreCommit, r.viewNum, None, prepareQC);
                && r' == r.(msgRecieved := r.msgRecieved + {precommitMsg})
                && outMsg == Multicast(precommitMsg, r.c.nodes)
            else
                && r' == r
                && |outMsg| == 0
        else
            var matchQCs := getMatchQC(r.msgRecieved, MT_Prepare, r.viewNum);
            forall m | m in matchQCs ::
                var sig := Signature(r.Address, m.mType, m.viewNum, m.node);
                var vote := Msg(MT_PreCommit, r.viewNum, m.node, None, sig);
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
                var signatures := v.partialSig | v in matchMsgs;
                var precommitQC := Cert(MT_PreCommit, matchMsgs[0].viewNum, matchMsgs[0].node, signatures);
                var commitMsg := Msg(MT_Commit, r.viewNum, None, precommitQC);
                && r' == r.(msgRecieved := r.msgRecieved + {commitMsg})
                && outMsg == Multicast(commitMsg, r.c.nodes)
            else
                && r' == r
                && |outMsg| == 0
        else
            var matchQCs := getMatchQC(r.msgRecieved, MT_PreCommit, r.viewNum);
            forall m | m in matchQCs ::
                var sig := Signature(r.Address, m.mType, m.viewNum, m.node);
                var vote := Msg(MT_Commit, r.viewNum, m.node, None, sig);
                var voteMsg := MsgWithRecipient(vote, leader);
                && r' == r.(lockedQC := m)
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
                var signatures := v.partialSig | v in matchMsgs;
                var commitQC := Cert(MT_PreCommit, matchMsgs[0].viewNum, matchMsgs[0].node, signatures);
                var decideMsg := Msg(MT_Decide, r.viewNum, None, commitQC);
                && r' == r.(msgRecieved := r.msgRecieved + {decideMsg})
                && outMsg == Multicast(decideMsg, r.c.nodes)
            else
                && r' == r
                && |outMsg| == 0
        else
            var matchQCs := getMatchQC(r.msgRecieved, MT_Commit, r.viewNum);
            forall m | m in matchQCs ::
                && r' == r.(
                    bc := r.bc + m.node
                )
    }

    predicate UponTimeOut(r : ReplicaState, r' : ReplicaState, outMsg : set<MsgWithRecipient>)
    {
        UponNextView(r, r', outMsg)
    }
}