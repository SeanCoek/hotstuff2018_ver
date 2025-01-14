include "Type.dfy"
include "Auxilarily.dfy"

module M_Adversary {
    import opened M_SpecTypes
    import opened M_AuxilarilyFunc

    datatype Adversary = Adversary(
        nodes : set<Address>
    )

    predicate AdversaryInit(a : Adversary, nodes : set<Address>)
    {
        &&  a.nodes <= nodes
        && |a.nodes| <= f(|nodes|)
    }

    predicate AdversaryNext(a : Adversary, a' : Adversary)
    {
        // TODO: Here to define what a faulty node could do
        true
    }
}