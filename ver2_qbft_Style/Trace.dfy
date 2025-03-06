include "Type.dfy"
include "System.dfy"

module M_Trace {
    import opened M_SpecTypes
    import opened M_System

    type Trace = nat -> SystemState

    ghost predicate ValidTrace(t : Trace, c : Configuration)
    {
        && SystemInit(t(0), c)
        && (forall i : nat :: && ValidSystemState(t(i))
                              && SystemNext(t(i), t(i+1)))
    }
}