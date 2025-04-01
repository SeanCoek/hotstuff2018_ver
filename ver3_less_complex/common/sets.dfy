

module M_Set {
    method SetToSeq<T>(s: set<T>) returns (sq: seq<T>)
    ensures |sq| == |s| // The length of the sequence equals the size of the set
    ensures forall i :: 0 <= i < |sq| ==> sq[i] in s // All elements in the sequence are from the set
    ensures forall i, j :: 0 <= i < j < |sq| ==> sq[i] != sq[j] // The sequence has no duplicates
    {
        sq := [];
        var remaining := s;
        while |remaining| > 0
            invariant |sq| + |remaining| == |s|
            invariant forall x :: x in sq ==> x in s
            invariant forall x :: x in sq ==> x !in remaining
            invariant forall i, j :: 0 <= i < j < |sq| ==> sq[i] != sq[j]
        {
            var x :| x in remaining;
            sq := sq + [x];
            remaining := remaining - {x};
        }
    }
}