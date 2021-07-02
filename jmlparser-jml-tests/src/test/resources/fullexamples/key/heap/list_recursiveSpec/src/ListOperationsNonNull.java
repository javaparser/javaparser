/* Operations on a list in a setting where null pointers are not allowed. 
  - The specification uses recursion which could not be handled automatically in previous versions of KeY. 
    These tests ensure that the automation is maintained. The automation requires automatic induction, 
    breath-first search strategy on query evaluation, and targeted query expansion in inductive proofs (proofs with the loop invariant rule instances of them).
  - These tests also detect applications of the rule QueryAxiom when this rule is deactivated.
  - The specification is written in standard JML but for a few exceptions. In particular sequences or the reach predicate are not needed.
  - This class contains a subset from an extended set of operations. A "Nullable" version of this class exists in analogy to this one.
  - NN is an abbreviation for NonNull.
  May 2012, Christoph Gladisch
*/

public class ListOperationsNonNull{


/*@ public normal_behavior
     requires (\forall ListNN u; u.next!=null) ;
     requires aCyclic(o);
     requires 0<i;
     ensures (\forall int j;0<=j ;( j<i ==> getNextContractNN(o,j)==\old(getNextContractNN(o,j))));
     ensures (\forall int k; 0<=k ; getNextContractNN(o,i+k+1)==\old(getNextContractNN(o,(i+k+1)+1)));
@*/
public void remove (ListNN o, int i){ //Here "o" denotes the beginning of the list. The element at position i+1 is removed.
    ListNN n=getNextContractNN(o,i);  //Notice that a contract is applied here. Hence, in the lemma we use i-1.
    lem_gNNNexpand2(o,i-1);  
    n.next=n.next.next;
 }

/*@ public normal_behavior
 requires  (\forall ListNN u; u.next!=null);
 assignable \strictly_nothing;
 accessible (\infinite_union ListNN n; n.next); //over approximation
 ensures \result == (\forall int i;0<=i; 
            (\forall int j;0<=j ;((getNextContractNN(o,i)==getNextContractNN(o,j) ==> i==j ))));
@*/
boolean aCyclic( ListNN o){ //Use the contract, not the implementation.
 boolean DUMMY_acyclic;
 return DUMMY_acyclic; //If this symbol occurrs in a proof, then something is wrong.
}
 

//Denotes a lemma that simulates finite query expansion from some node at position k (or k+1) in the list l.
/*@ public normal_behavior
     requires (\forall ListNN u; u.next!=null);
    requires k>=0;
    assignable \strictly_nothing;
    ensures getNextContractNN(l,k+1)==getNextContractNN(l,k).next && 
            getNextContractNN(l,k+2)==getNextContractNN(l,k+1).next && 
            getNextContractNN(l,k+3)==getNextContractNN(l,k+2).next;
@*/
public void lem_gNNNexpand2(ListNN l, int k){ } //Use the contract of this method, not the implementation.

/*@ public normal_behavior
 requires  n>=0 &&  (\forall ListNN l; l.next!=null);
 assignable getNextContractNN(o,n).value;
 accessible (\infinite_union ListNN n; n.next);
 ensures  getNextContractNN(o,n).value==val;
 diverges true;
@*/
 public void setValueAt_NN(ListNN o, int n, int val){
   int i=0;
   ListNN oldo; oldo = o;
    /*@ loop_invariant 0<=i && i<=n && 
     (o == getNextContractNN(oldo,i)) && o!=null ; 
     assignable \strictly_nothing;
      decreases n-i; 
    @*/
    while(o!=null &&  i<n){ 
      o = o.next;
      i++; 
    }
    o.value=val;
 }


/*@ public normal_behavior
 requires  o!=null && n>=0 &&  (\forall ListNN l; l.next!=null);
 assignable \strictly_nothing;
 ensures  (n==0 ==> \result == o) &&
          (n>0  ==> \result == getNextContractNN(o,n-1).next);
 diverges true;
@*/
 public  ListNN getNextNN(ListNN o, int n){
   int i=0;
   ListNN oldo; oldo = o;
    /*@ loop_invariant 0<=i && i<=n && 
     (o == getNextContractNN(oldo,i)) ; 
     assignable \strictly_nothing;
     decreases n-i; 
    @*/
    while(o!=null &&  i<n){ 
      o = o.next;
      i++;
    }
   return o;
 }

/*@ public normal_behavior
 requires  n>=0 && o!=null; 
 assignable \strictly_nothing;
 accessible (\infinite_union ListNN l; l.next);
 ensures  (n==0 ==> \result == o) &&
          (n>0  ==> \result == getNextContractNN(o,n-1).next);
 measured_by n;
@*/
 public ListNN getNextContractNN(ListNN o, int n){
    ListNN Dummy2;
   return Dummy2;
 }


}
