include "Type.dfy"
include "System.dfy"
include "Trace.dfy"

module M_Thereom {
    import opened M_SpecTypes
    import opened M_System
    import opened M_Trace

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
                :: consistentBlockchains(t(i).nodes[r1].bc, t(i).nodes[r2].bc)
    }


    lemma LemmaBlockchainConsistency(t : Trace, c : Configuration)
    requires ValidTrace(t, c)
    ensures consistency(t)
    {
        
    }
}