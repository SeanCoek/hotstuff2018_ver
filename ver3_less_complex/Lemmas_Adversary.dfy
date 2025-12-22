include "Replica.dfy"
include "Adversary.dfy"
include "System.dfy"
include "Type.dfy"
include "Auxilarily.dfy"
include "Axioms.dfy"
include "common/proofs.dfy"

module M_Lemmas_Adversary {

    import opened M_Replica
    import opened M_Adversary
    import opened M_System
    import opened M_SpecTypes
    import opened M_AuxilarilyFunc
    import opened M_Axiom
    import opened M_ProofTactic

    // lemma LemmaStableIDInAdversaryNext(
    // ss : SystemState,
    // inMsg : set<Msg>,
    // ss' : SystemState,
    // outMsg : set<Msg>
    // )
    // requires AdversaryNext(ss.adversary, inMsg, ss'.adversary, outMsg)
    // ensures forall r | && r in ss.adversary.byz_nodes
    //                    && r in ss.nodeStates.Keys
    //                    && r in ss'.nodeStates.Keys
    //                 ::
    //                    ss.nodeStates[r].id == ss'.nodeStates[r].id
    // {
        
    // }
}