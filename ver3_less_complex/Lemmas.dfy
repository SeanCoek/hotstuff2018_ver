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

    lemma{:axiom} LemmaHonestNodeOnlyVotePrepareOnceInOneView(ss : SystemState)
    ensures forall s1 : Signature, s2 : Signature | 
                                                    && IsHonest(ss, s1.signer)
                                                    && IsHonest(ss, s2.signer)
                                                    && s1.signer == s2.signer
                                                    && s1.block == s2.block
                                                    && s1.mType == s2.mType
                                                  ::
                                                    s1.viewNum == s2.viewNum

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
        assert ss.nodeStates.Keys - ss.adversary.byz_nodes != {};
        var r1 :| IsHonest(ss, r1);
        var r2 :| IsHonest(ss, r2);
        var cert1 :| && cert1 == ss.nodeStates[r1].prepareQC;
        var cert2 :| && cert2 == ss.nodeStates[r2].prepareQC;

        // var r1, r2, cert1, cert2 :| && IsHonest(ss, r1)
        //                             && IsHonest(ss, r2)
        //                             && cert1 == ss.nodeStates[r1].prepareQC
        //                             && cert2 == ss.nodeStates[r2].prepareQC;
                                    // && cert1 == ss.nodeStates[r1].prepareQC && cert1.Cert? 
                                    // && cert2 == ss.nodeStates[r2].prepareQC && cert2.Cert?
                                    // && cert1.block.Block?
                                    // && cert2.block.Block?
                                    // && !NoConflict(cert1.block, cert2.block);
        assume cert1.Cert?;
        assume cert2.Cert?;
        assume cert1.block.Block?;
        assume cert2.block.Block?;
        assume !NoConflict(cert1.block, cert2.block);
        calc {
            !NoConflict(cert1.block, cert2.block);
            ==>
            cert1.block != cert2.block;
        }
        
        var signers1 := getMajoritySignerInValidQC(cert1);
        var signers2 := getMajoritySignerInValidQC(cert2);
        assert signers1 * signers2 * Honest_Nodes != {} by
        {
            Axiom_Byz_Constraints();
            LemmaTwoQuorumIntersection(All_Nodes, Adversary_Nodes, signers1, signers2);
        }
        var replica :| replica in signers1 * signers2 * Honest_Nodes;
        var sign1 :| && sign1 in cert1.signatures
                     && sign1.signer == replica;
        var sign2 :| && sign2 in cert2.signatures
                     && sign2.signer == replica;
        assert sign1 != sign2;
        calc {
            sign1 != sign2
            ==>
            cert1.viewNum != cert2.viewNum;
        }
    } 

    /**
     * Lemma: for 2 valid certificate, if they are not conflict, then their coressponding view number should be different
     */
    lemma LemmaViewDiffOnConflictCertificateCommit(ss : SystemState)
    // requires All_Nodes != {}
    requires ValidSystemState(ss)
    ensures forall r1, r2, cert1, cert2 | && IsHonest(ss, r1)
                                          && IsHonest(ss, r2)
                                          && cert1 == ss.nodeStates[r1].commitQC && cert1.Cert? 
                                          && cert2 == ss.nodeStates[r2].commitQC && cert2.Cert?
                                          && cert1.block.Block?
                                          && cert2.block.Block?
                                          && !NoConflict(cert1.block, cert2.block)
                                        ::
                                          cert1.viewNum != cert2.viewNum

}