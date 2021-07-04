import java.util.stream.*;

public class ImplicitIterationDemo {

   boolean allTrue = true;

   //@ assignable allTrue;
   //@ ensures allTrue == (\old(allTrue) && v);
   void check(boolean v) { allTrue =  allTrue && v; }

   void test() {
	  allTrue = true;
      Stream<Boolean> s = Stream.<Boolean>of(true, false, true);
      Stream<Boolean> ss = Stream.of(true, true, true, true);

      //@ loop_invariant allTrue==(\forall int j; 0<=j && j <\count; s.values[j]);
      //@ loop_modifies allTrue;
      //@ inlined_loop;
      s.forEachOrdered(b->check(b));
      //@ assert allTrue==(\forall int j; 0<=j && j <s.count(); s.values[j]);
      //@ assert !allTrue;

	  allTrue = true;
      //@ loop_invariant allTrue==(\forall int j; 0<=j && j <\count; ss.values[j]);
      //@ loop_modifies allTrue;
      //@ inlined_loop;
      ss.forEachOrdered(b->check(b));
      //@ assert allTrue==(\forall int j; 0<=j && j <ss.count(); ss.values[j]);
      //@ assert allTrue;

    }
}
