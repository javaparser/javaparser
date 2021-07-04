
//@ non_null_by_default
    public class Test {
        
        //@ normal_behavior
        //@   requires (\let int c = cc; c != 0);
        //@ pure
        Test(int cc) {
            //@ assert cc != 0;
        }
        
        //@ normal_behavior
        //@   requires (\let int c = cc; c != 0);
        //@ pure
        //@ @org.jmlspecs.annotation.Options("-solver-seed=2000")
        void m(int cc) {
            //@ assert cc != 0;
        }
        
        //@ nullable
        int[] a;
        
        //@ normal_behavior
        //@   requires a != null && a.length == 10;
        //@   requires (\forall int i; 0 <= i < 5; a[i+i] == 0);
        //@ pure
        void m1(int cc) {
            //@ assert a[2]== 0; // OK // but fails
            //@ assert a[3]== 0; // ERROR
        }
        
        //@ normal_behavior
        //@   requires a != null && a.length == 10;
        //@   requires (\forall int i; 0 <= i < 5; (\let int ii = 2*i; a[ii] == 0));
        //@ pure
        void m2(int cc) {
            //@ assert a[2]== 0; // OK // forall does not work well with let
            //@ assert a[3]== 0; // ERROR
        }

        //@ normal_behavior
        //@   requires a != null && a.length == 10;
        //@   requires (\forall int i; 0 <= i < 5; (\let int ii = i; a[ii] == 0));
        //@ pure
        void m3(int cc) {
            //@ assert a[2]== 0; // OK
            //@ assert a[3]== 0; // OK
        }

        //@ normal_behavior
        //@   requires a != null && a.length == 10;
        //@   requires (\forall \bigint i; 0 <= i < 5; (\let \bigint ii = i; a[ii] == 0));
        //@ pure
        void m3b(int cc) {
            //@ assert a[2]== 0; // OK
            //@ assert a[3]== 0; // OK
        }

        //@ normal_behavior
        //@   requires a != null && a.length == 10;
        //@   requires (\forall int i; 0 <= i < 5; a[i] == 0);
        //@ pure
        void m4(int cc) {
            //@ assert a[2]== 0; // OK
            //@ assert a[3]== 0; // OK
        }
        
        void mm(int cc) {
            //@ assert (\let \bigint i = cc+1; i == i);
            //@ assert (\let \bigint i = cc+1; i-2 == cc-1);
            //@ assert (\forall \bigint i; \let \bigint ii = i+i; ii == ii);
        }
    }