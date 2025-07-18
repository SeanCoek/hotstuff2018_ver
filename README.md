# HotStuff2018_ver
We present our work of formally verifying distributed consensus protocols in this repository.

We put the specification and proof of HotStuff2018 in the folder **<em>ver3_less_complex<em>**. It is constructed as follows.
- ### ver3_less_complex
  -  #### <em>commom</em> -> Common utililities like set, sequence
  -  #### <em>network</em> -> Modelling of network communication, currently empty cuase we haven't make any assumption on network.
  -  Adversary.dfy -> Definition of adversary (faulty) nodes.
  -  Auxilarily.dfy -> Useful auxilarily function like getting the size of a quorum.
  -  dfyconfig.toml -> Dafny config file.
  -  Invariants.dfy -> Definition of system invariants.
  -  Lemmas.dfy    -> Lemmas to prove safety or liveness thereom.
  -  Replica.dfy    -> Specification of replica (node).
  -  System.dfy     -> Specification of distributed system.
  -  Thereom.dfy    -> Thereom of safety or liveness.
  -  Trace.dfy      -> Modelling of a single run of systems, currently not used in our safety proof.
  -  Type.dfy       -> Definition of data type like Block, Certificate, Message, etc.
