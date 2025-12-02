include "Type.dfy"
include "Auxilarily.dfy"
include "Replica.dfy"

module M_Lemma_Test {
    import opened M_SpecTypes
    import opened M_Replica
    import opened M_AuxilarilyFunc


    lemma LemmaPreparePhaseSendOutPrepareVote(r : ReplicaState,
                                              r' : ReplicaState,
                                              outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponPrepare(r, r', outMsg)
    ensures forall vote | vote in outMsg
                        :: 
                          vote.partialSig.Signature?
                          ==>
                          vote.partialSig.mType.MT_Prepare?
    {
    }

    lemma LemmaValidMsgTest(m : Msg, id : nat)
    requires id > 0
    requires ValidMsg(m)
    ensures m.mType.MT_NewView? ==> ValidQC(m.justify) && m.justify.cType.MT_Prepare?
    {
        if m.mType.MT_NewView? && ValidQC(m.justify) {
            assert m.viewNum != id - 1;
        }
    }

}