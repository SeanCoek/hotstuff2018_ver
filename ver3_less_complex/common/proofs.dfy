module M_ProofTactic
{
    lemma LemmaSubsetTransitiveInSeq<T> (s : seq<set<T>>)
    requires |s| > 0
    requires forall i | 0 <= i < |s|-1 :: s[i] <= s[i+1]
    ensures forall i | 0 <= i <= |s|-1 :: s[0] <= s[i]
    {
        forall i | 0 <= i <= |s|-1
        ensures s[0] <= s[i] {
            if i == 0 {

            }
            else
            {
                LemmaSubsetTransitiveInSeq(s[1..]);
            }
        }
    }

}