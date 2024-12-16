type Rounds = x:int | x >= -1
datatype Block = Block
type Blocks = set<Block>

datatype Tree = Tree (
    existsBlocks : Blocks,
    gen : Block,
    round: map<Block, Rounds>,
    parent: map<Block, Block>
)

predicate TreeInit(t: Tree){
    && t.existsBlocks != {}
    && t.gen in t.existsBlocks
    && (forall b | b in t.existsBlocks :: b in t.round.Keys)
    && (forall b | b in t.existsBlocks :: b in t.parent.Keys)
    && (forall b | b in t.existsBlocks && b != t.gen :: t.round[b] == -1)
    && t.round[t.gen] == 0
    && (forall b | b in t.existsBlocks :: t.parent[b] == b)
}


function getAncestors(b: Block, t: Tree) : Blocks
requires b in t.parent.Keys
{
    match (b != t.parent[b]){
        case true => {b} + getAncestors(t.parent[b], t)
        case false => {b}
    }
}

predicate Ancestor(a: Block, b: Block, t:Tree)
requires b in t.parent.Keys
{
    a in getAncestors(b, t)
}

predicate chain(b: Block, c: Block, t: Tree)
requires b in t.parent && c in t.parent
requires b in t.round && c in t.round
requires t.parent[c] in t.parent
requires t.parent[c] in t.round
{
    && t.parent[t.parent[c]] == b
    && t.round[c] <= t.round[t.parent[c]] + 1
    && t.round[t.parent[c]] <= t.round[b] + 1
}