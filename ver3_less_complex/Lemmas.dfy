include "Type.dfy"
include "Auxilarily.dfy"
include "System.dfy"

module M_Lemma {
    import opened M_SpecTypes
    import opened M_AuxilarilyFunc
    import opened M_System

    lemma{:axiom} Axiom_Byz_Constraints()
    ensures |Adversary_Nodes| <= f(|Honest_Nodes| + |Adversary_Nodes|)
    ensures Adversary_Nodes * Honest_Nodes == {}

    lemma{:axiom} Axiom_Common_Constraints()
    ensures All_Nodes != {}

    lemma{:axiom} NoOuterClient()
    ensures forall cert : Signature :: cert.signer in All_Nodes

    /**
     * Lemma: for 2 valid certificate, if they are not conflict, then their coressponding view number should be different
     */
    lemma LemmaViewDiffOnConflictCertificate(cert1 : Cert, cert2 : Cert)
    requires cert1.Cert? && cert2.Cert?
    requires cert1.cType == cert2.cType
    requires ValidQC(cert1) && ValidQC(cert2)
    requires cert1.block.Block? && cert2.block.Block?
    requires !NoConflict(cert1.block, cert2.block)
    ensures cert1.viewNum != cert2.viewNum
    {
        // var votesInCert1 := getVotesInValidQC(cert1);
        // var voterInCert1 := getMajoritySignerInValidQC(cert1);

        // var votesInCert2 := getVotesInValidQC(cert2);
        // var voterInCert2 := getMajoritySignerInValidQC(cert2);

        // assert voterInCert1 <= All_Nodes && voterInCert2 <= All_Nodes;

        // assert |Adversary_Nodes| <= f(|All_Nodes|);
        assert |All_Nodes| > 0 by {
            Axiom_Common_Constraints();
        }

        // assert voterInCert1 * voterInCert2 * Honest_Nodes != {} by {
        //     LemmaTwoQuorumIntersection(
        //         All_Nodes,
        //         Adversary_Nodes,
        //         voterInCert1,
        //         voterInCert2
        //     );
        // }
    }

    lemma LemmaViewDiffOnConflictCertificate2(ss : SystemState)
    requires ValidSystemState(ss)
    ensures forall r1, r2, cert1, cert2 | && r1 in ss.nodeStates.Keys
                                          && r2 in ss.nodeStates.Keys
                                          && IsHonest(ss, r1)
                                          && IsHonest(ss, r2)
                                          && cert1 == ss.nodeStates[r1].prepareQC && cert1.Cert? 
                                          && cert2 == ss.nodeStates[r2].prepareQC && cert2.Cert?
                                          && cert1.block.Block?
                                          && cert2.block.Block?
                                          && !NoConflict(cert1.block, cert2.block)
                                        ::cert1.viewNum != cert2.viewNum
    {
        
    }

}