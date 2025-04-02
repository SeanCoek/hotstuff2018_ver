include "Auxilarily.dfy"

module M_SpecTypes {

    type {:extern "Address"} Address(==,!new)


    datatype Block = Block(parent : Block) | EmptyBlock

    type Blockchain = seq<Block>


    datatype Cert = Cert(
        cType : MsgType,
        viewNum : nat,
        block : Block,
        signatures : set<Signature>
    ) | CertNone
    
    datatype Signature = Signature(
        signer : Address,
        mType : MsgType,
        viewNum : nat,
        block : Block
    ) | SigNone

    datatype MsgType = MT_NewView | MT_Prepare | MT_PreCommit | MT_Commit | MT_Decide

    datatype Msg = Msg(
        mType : MsgType,
        viewNum : nat,
        block : Block,
        justify : Cert,
        partialSig : Signature
    )

    datatype MsgWithRecipient = MsgWithRecipient(
        msg : Msg,
        recipient : Address
    )
        
    
    datatype Configuration = Configuration(
        nodes : set<Address>,   // all the nodes, containing byzantine nodes
        genesisBlock : Block,
        honestNodes : set<Address> := Honest_Nodes,
        adversaryNodes : set<Address> := Adversary_Nodes
    )

    const Honest_Nodes : set<Address>

    const Adversary_Nodes : set<Address>

}