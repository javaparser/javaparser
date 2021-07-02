package object;

/**
 *
 * @author christoph
 */
public final class ObjectOrientation {
    int i;

    
    public ObjectOrientation(int i) {
        this.i = i;
    }

    
//--------------

    
    //@ determines \result \by \nothing \new_objects \result;
    public ObjectOrientation secure_object_creation() {
        return new ObjectOrientation(1);
    }

    //@ determines \result.i \by \nothing;
    public ObjectOrientation secure_object_creation_2() {
        return new ObjectOrientation(1);
    }
    
    //@ determines \result.i \by \nothing \new_objects \result;
    public ObjectOrientation secure_object_creation_3() {
        return new ObjectOrientation(1);
    }
    
   
//--------------
    
    
    public static ObjectOrientation o0, o1, o2;
    ObjectOrientation next;
    private static ObjectOrientation high_object;
    private static boolean high;
    
    //@ determines o0, o1, o2 \by \itself;
    //@ also
    //@ determines o0, o1, o2 \by \nothing \new_objects o0, o1, o2;
    public void insecure_object_assignment() {
        o0 = high_object;
    }

    /*@ normal_behavior
      @ determines o0, o1, o2 \by \nothing \new_objects o0, o1, o2;
      @ */
    public void secure_two_object_creation() {
        o0 = new ObjectOrientation(0);
        o1 = new ObjectOrientation(1);
        o2 = o0;
    }
    
    //@ determines o0, o1, o2 \by \nothing \new_objects o0, o1, o2;
    public void insecure_two_object_creation() {
        o0 = new ObjectOrientation(0);
        o1 = new ObjectOrientation(1);
        o2 = (high ? o0 : o1);
    }

    //@ determines o0, o1 \by \nothing \new_objects o0, o1;
    public void secure_if_two_object_creation() {
        if(high) {
            o0 = new ObjectOrientation(0);
            o1 = new ObjectOrientation(1);
        } else {
            o1 = new ObjectOrientation(1);
            o0 = new ObjectOrientation(0);
        }
    }

    //@ determines o0, o1 \by \nothing \new_objects o0, o1;
    //@ also
    // the following contract does not hold
    //@ determines o0, o1, o1.next \by \nothing \new_objects o0, o1, o1.next;
    public void if_two_object_creation_next() {
        if(high) {
            o0 = new ObjectOrientation(0);
            o1 = new ObjectOrientation(1);
            o1.next = o1;
        } else {
            o1 = new ObjectOrientation(1);
            o0 = new ObjectOrientation(0);
            o1.next = o0;
        }
    }


//--------------


    //@ determines o0, o1, o2 \by \itself;
    public void secure_method_call() {
        secure_two_object_creation();
        o2 = o1;
    }


//--------------

    //@ requires    \typeof(a) == \type(Object[]);
    //@ determines  (\seq_def int i; 0; a.length; a[i]) \by a.length;
    public void secure_while_i(Object[] a) {
        /*@ loop_invariant 0 <= i && i <= a.length;
            loop_invariant a != null && \typeof(a) == \type(Object[]);
            assignable a[*];
            decreases a.length - i;
            determines i, a.length, (\seq_def int j; 0; i; a[j])
                   \by \itself
                   \new_objects a[i-1];
          @*/
        for (int i = 0; i < a.length; i++) {
            a[i] = new Object();
        }
    }

}
