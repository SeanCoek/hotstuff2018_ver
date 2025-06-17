

module M_Set {

    import opened Std.Collections.Set

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

    lemma LemmaProperSubsetCardinality<T>(x: set<T>, y:set<T>)
    requires x < y
    ensures |x| < |y|
    {
        // if (x != {}) {
        //     var e :| e in x;
        //     LemmaProperSubsetCardinality(x-{e}, y-{e});
        // }
        Set.LemmaSubsetSize(x, y);
    }

    lemma LemmaSubsetCardinality<T> (x: set<T>, y:set<T>)
    ensures x < y ==> |x| < |y| // Strangely Dafny can't prove this. HAVE TO prove it by our own
    ensures x <= y ==> |x| <= |y| 
    {
        // if (x < y) {
        //     LemmaProperSubsetCardinality(x, y);
        // }
        // if (x == y) {
        //     // OBSERVE
        // }
        Set.LemmaSubsetSize(x, y);
    }

    lemma LemmaAdditiveOnSeparateSet<T> (s: set<T>, x: set<T>, y: set<T>)
    requires x * y == {}
    requires s == x + y
    ensures s - x == y
    {
        if (x != {} && y != {})
        {
            forall e | e in s - x
            ensures e in y {

            }
            assert |s-x| == |y|;
            // LemmaSetEquivlent(s-x, y);
            Set.LemmaSubsetEquality(s-x, y);
            assert s - x == y;
        }
        else
        {
            //OBSERVE
        }
    }

    lemma LemmaSetEquivlent<T> (x: set<T>, y: set<T>)
    requires forall e | e in x :: e in y
    requires |x| == |y|
    ensures x == y
    {
        // if (x == {})
        // {
        //     //OBSERVE
        // }
        // else {
        //     var e :| e in x;
        //     LemmaSetEquivlent(x-{e}, y-{e});
        // }
        Set.LemmaSubsetEquality(x, y);
    }

    lemma LemmaTest<T> (x: set<T>, y: set<T>)
    requires x < y
    ensures |x| < |y|
    {
        Set.LemmaSubsetSize(x, y);
    }
}