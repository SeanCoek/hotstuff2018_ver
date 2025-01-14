datatype Hash = Hash

function hash<T>(s: T) : Hash

lemma{:axiom} HashLemma<T>()
ensures forall s1:T, s2:T :: hash(s1) == hash(s2) ==> s1 == s2



function encSym<Key, T>(pk: Key, plaint: T) : Hash
function decSym<Key, T>(pk: Key, puzzle: Hash) : T

lemma{:axiom} SymmetricLemma<Key, T>()
ensures forall k:Key, k':Key, plaint:T :: decSym(k', encSym(k, plaint)) == plaint ==> k == k'

function encAsym<Key, T>(prik: Key, plaint: T) : Hash
function decAsym<Key, T>(pk: Key, puzzle: Hash): T

lemma{:axiom} AsymmetricLemma<Key, T>()
ensures forall pk:Key, prik:Key, plaint:T :: decAsym(pk, encAsym(prik, plaint)) == plaint