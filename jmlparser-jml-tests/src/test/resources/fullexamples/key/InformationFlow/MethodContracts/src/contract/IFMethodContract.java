package contract;

/**
 * Information flow examples.
 *
 * A collection of several examples showing the usage of information flow
 * method contracts.
 *
 * The information flow proof obligations of all secure examples can be proved
 * fully automatically using the macro "Full Information Flow Auto Pilot".
 *
 * @author Christoph Scheben
 */
public class IFMethodContract {
    public int low;
    private int high;

    
//--------

    
    //@ determines low \by \itself;
    void secure_sequential_n1_n2() {
        n1();
        n2();
    }
    
    //@ normal_behavior
    //@ determines low \by \itself;
    void n1() {
        low = 27;
    }
    
    //@ normal_behavior
    //@ determines low \by \itself;
    void n2() {
        low = low + 13;
    }
    
    
    //@ determines low \by \itself;
    void secure_assignments_n2() {
        low = 45;
        high = high * high;
        n2();
    }
    
    
    //@ determines low \by \itself;
    void insecure_assignment_n2() {
        low = high;
        n2();
    }


//--------

    
    //@ determines low \by \itself;
    void secure_sequential_n3_precond_n4() {
        n3();
        n4();
    }
    
    /*@ normal_behavior
      @ ensures high > 0;
      @ determines low \by \itself;
      @*/
    void n3() {
        high = 8;
    }
    
    /*@ normal_behavior
      @ requires high > 0;
      @ determines low \by \itself;
      @*/
    void n4() {
        if (high > 0) {
            low = 2;
        } else {
            low = high;
        }
    }
    
    
//--------

    
    //@ determines low \by \itself;
    void secure_n5() {
        low = n5(high);
    }

    
//--------

    
    //@ determines low \by \itself;
    void secure_if_high_n1() {
        if (high > 0) {
            high = 2 * high;
        } else {
            high = -2 * high;
        }
        n1();
    }
    
    
    //@ determines low \by \itself;
    void secure_if_high_n5_n1() {
        if (high > 0) {
            low = n5(high);
        } else {
            high = -high;
            low = n5(high + low);
        }
        n1();
    }
    
    //@ normal_behavior
    //@ determines low, \result \by low;
    int n5(int x) {
        high = 2 * x;
        return 15;
    }
    
    
    //@ determines low \by \itself;
    void insecure_if_high_n5_n1() {
        if (high > 0) {
            low = n5(high);
        } else {
            low = 7;
        }
        n1();
    }


//--------
    
    
    //@ determines low \by \itself;
    void secure_assignment_0_n9() {
        high = 0;
        n9();
    }
    
    
    /*@ normal_behavior
      @ ensures     low == high;
      @ modifies    low;
      @*/
    void n9() {
        low = high;
    }


//--------


    /*@ requires a.length > 0;
      @ requires 0 <= pos && pos < a.length;
      @ separates pos, (\seq_def int i; 0; a.length; a[i] == 0);
      @*/
    void secure_array_param(int[] a, int pos) {
        a[pos] = secure_array_param_helper();
    }


    /*@ normal_behavior
      @ ensures \result == 0;
      @ pure
      @*/
    int secure_array_param_helper() {
        return 0;
    }


//-------- Exceptions

    
    /*@ requires high != 0;
      @ determines low \by \itself;
      @*/
    void secure_n6() {
        n6();
    }
 
    /*@ normal_behavior
      @ requires high != 0;
      @ determines low \by \itself;
      @*/
    void n6() {
        high = low / high;
    }
    
    
//--------

    
    //@ determines low \by \itself;
    void secure_catch_exception() {
        try {
            n7();
        } catch (NullPointerException e) {
            low = 45;
        }
    }
    
//    /*@ determines low, \exception \by low;
//      @*/
    // final for sound method expansion
    final void n7() {
        throw new NullPointerException();
    }
    
    
//--------
    
    
//    /*@ requires        high != 0;
//      @ signals_only    NullPointerException;
//      @ separates        low, \exception;
//      @*/
    void n8() {
        high = low / high;
        throw new NullPointerException();
    }
    
    
//-------- Recursion
    
    
    /*@ normal_behavior
      @ requires    x >= 0;
      @ measured_by x;
      @ separates    low, x;
      @*/
    void secure_recursion(int x) {
        if (x > 0) {
            secure_recursion(x-1);
            low = low + 1;
        }
    }
    
    
    /*@ normal_behavior
      @ requires    x >= 0;
      @ measured_by x;
      @ separates    low, x, (\seq_def int i; 0; a.length; a[i]);
      @ assignable  low;
      @*/
    void secure_recursion_2(int[] a, int x) {
        if (x > 0 && x < a.length) {
            secure_recursion_2(a, x-1);
            low = a[x];
        }
    }
    
}
