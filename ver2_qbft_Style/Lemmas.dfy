include "Type.dfy"
include "Auxilarily.dfy"

module M_Lemma {
    import opened M_SpecTypes
    import opened M_AuxilarilyFunc

    /**
     * Lemma: for 2 valid certificate, if they are not conflict, then their coressponding view number should be different
     */
    lemma LemmaViewDiffOnConflictCertificate(cert1 : Cert, cert2 : Cert)
    requires cert1.Cert? && cert2.Cert?
    requires ValidQC(cert1) && ValidQC(cert2)
    requires !NoConflict(cert1.block, cert2.block)
    ensures cert1.viewNum != cert2.viewNum
    {

    }
}