include "Type.dfy"
include "System.dfy"

module M_Trace {
    import opened M_SpecTypes
    import opened M_System

    type Trace = nat -> SystemState

    ghost predicate ValidTrace(t : Trace)
    {
        && SystemInit(t(0))
        && (forall i : nat :: && ValidSystemState(t(i))
                              && SystemNext(t(i), t(i+1)))
    }
}