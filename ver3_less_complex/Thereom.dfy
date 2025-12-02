include "Type.dfy"
include "System.dfy"
include "Trace.dfy"
include "Invariants.dfy"
include "Replica.dfy"
include "Auxilarily.dfy"
include "Lemmas.dfy"
include "common/sets.dfy"

module M_Thereom {
    import opened M_SpecTypes
    import opened M_System
    import opened M_Trace
    import opened M_Invariants
    import opened M_Replica
    import opened M_AuxilarilyFunc
    import opened M_Lemma
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

    /**
     * In every reachable system state, 
     * any honest replica should hold a consistent local blockchain.
     * 
    */
    lemma LemmaReachableSystemStateIsConsistent(ss : SystemState)
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
                // assert false;
                assert exists m1 | && m1 in s1.msgReceived
                                    // && m1.mType.MT_Decide?
                                    && m1.justify.Cert?
                                    && m1.justify.cType == MT_Commit
                                    && ValidQC(m1.justify)
                                    && m1.justify.block.Block?
                                ::
                                    s1.bc <= getAncestors(m1.justify.block);
                var m1 :| && m1 in s1.msgReceived
                                    // && m1.mType.MT_Decide?
                                    && m1.justify.Cert?
                                    && m1.justify.cType == MT_Commit
                                    && ValidQC(m1.justify)
                                    && m1.justify.block.Block?
                                    && s1.bc <= getAncestors(m1.justify.block);

                assert exists m2 | && m2 in s2.msgReceived
                                //    && m2.mType.MT_Decide?
                                   && m2.justify.Cert?
                                   && m2.justify.cType.MT_Commit?
                                   && ValidQC(m2.justify)
                                   && m2.justify.block.Block?
                                ::
                                   s2.bc <= getAncestors(m2.justify.block);
                var m2 :| && m2 in s2.msgReceived
                                //    && m2.mType.MT_Decide?
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
                                            // && m1_p.mType == MT_Prepare
                                            && ValidQC(m1_p.justify)
                                            && m1_p.justify.cType == MT_Prepare
                                            && m1_p.justify.block == m1.justify.block
                                            && m1_p.justify.viewNum == m1.justify.viewNum by {
                    LemmaExistValidPrepareQCForEveryValidCommitQC(ss);
                }

                assert exists m2_p : Msg :: && m2_p in ss.msgSent
                                            // && m2_p.mType == MT_Prepare
                                            && ValidQC(m2_p.justify)
                                            && m2_p.justify.cType == MT_Prepare
                                            && m2_p.justify.block == m2.justify.block
                                            && m2_p.justify.viewNum == m2.justify.viewNum by {
                    LemmaExistValidPrepareQCForEveryValidCommitQC(ss);
                }

                var m1_p :| && m1_p in ss.msgSent
                                            // && m1_p.mType == MT_Prepare
                                            && ValidQC(m1_p.justify)
                                            && m1_p.justify.cType == MT_Prepare
                                            && m1_p.justify.block == m1.justify.block
                                            && m1_p.justify.viewNum == m1.justify.viewNum;
                var m2_p :| && m2_p in ss.msgSent
                                            // && m2_p.mType == MT_Prepare
                                            && ValidQC(m2_p.justify)
                                            && m2_p.justify.cType == MT_Prepare
                                            && m2_p.justify.block == m2.justify.block
                                            && m2_p.justify.viewNum == m2.justify.viewNum;
                
                if m1_p.justify.viewNum <= m2_p.justify.viewNum {
                    assert extension(m2_p.justify.block, m1_p.justify.block) by {
                        LemmaPrepareQCExtensionIfExistCommitQC(ss);
                    }
                } else {
                    assert extension(m1_p.justify.block, m2_p.justify.block) by {
                        LemmaPrepareQCExtensionIfExistCommitQC(ss);
                    }
                }

                assert || extension(m1.justify.block, m2.justify.block)
                       || extension(m2.justify.block, m1.justify.block);
                
                var m1_acstr, m2_acstr := getAncestors(m1.justify.block), getAncestors(m2.justify.block); 

                assert s2.bc <= m2_acstr;
                assert s1.bc <= m1_acstr;
                assert m2_acstr <= m1_acstr || m1_acstr <= m2_acstr;
                assert s2.bc <= s1.bc || s1.bc <= s2.bc;
                
            }
            else {  // s1.bc == [M_SpecTypes.Genesis_Block] || s2.bc == [M_SpecTypes.Genesis_Block]
                // OBSERVE 
                // by the invariant that an honest replica always holds a local blockchain starting with Genesis_Block
            }
        }
    }
}