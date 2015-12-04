theory Reversal
imports VCG
begin

datatype 'a Pointer = Nil|PAddress 'a

datatype 'a Node = Nil|Node 'a "'a Pointer"

datatype "'a Node" list = Nil|Cons "'a Node" "'a list"



end