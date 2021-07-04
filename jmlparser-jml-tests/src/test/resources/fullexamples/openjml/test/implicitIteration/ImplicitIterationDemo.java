import java.util.stream.*;

//@ nullable_by_default
public class ImplicitIterationDemo {

	   boolean allTrue = true;
	   boolean noNulls = true;

	   //@ assignable noNulls;
	   //@ ensures noNulls == (\old(noNulls) && v!=null);
	   void check(Object v) { noNulls =  noNulls && (v!=null); }

	   //@ assignable allTrue;
	   //@ ensures allTrue == (\old(allTrue) && v);
	   void checkA(/*@ non_null*/Boolean v) { allTrue =  allTrue && v; }

   void test() {
     /*@ non_null */ Stream<Object> s = Stream.<Object>of(true,null,1);
     noNulls = true;

     //@ loop_invariant noNulls==(\forall int j; 0<=j && j <\count; s.values[j] != null);
     //@ loop_modifies noNulls;
     //@ inlined_loop;
     s.forEachOrdered(b->check(b));
     //@ assert noNulls==(\forall int j; 0<=j && j <s.count(); s.values[j] != null);
     //@ assert !noNulls;
   }
   
   // The (boolean) casts should not be needed; implicitIterationA tests without them
   void testA() {
     Stream<Boolean> s = Stream.<Boolean>of(true,false,true);
     //@ assert (\forall int j; 0<=j && j<s.count(); s.values[j] != null);
     allTrue = true;
     
     //@ loop_invariant (boolean)s.values[0] && !(boolean)s.values[1] && (boolean)s.values[2];
     //@ loop_invariant allTrue==(\forall int j; 0<=j && j <\count; (boolean)s.values[j]);
     //@ loop_modifies allTrue;
     //@ inlined_loop;
     s.forEachOrdered(b->checkA(b));
     //@ assert allTrue==(\forall int j; 0<=j && j <s.count(); (boolean)s.values[j]);
     //@ assert !allTrue;
   }
}
