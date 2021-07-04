public class trace {
    
    public int fxxx;
    static public int sf;
    public int[] a = { 1,2,3};
    
    public void mm(int k,boolean b) {};
    
    //@ ensures \result == 41;
    public int mmm(int k) { return 41;};
    
    //@ requires true;
    //@ ensures \result != 0;
    public int m(int k) {
        k = 7;
        k += 7;
        int j;
        fxxx = k + 9;
        j = fxxx + this.fxxx;
        fxxx += k + 9;
        this.fxxx = k + 9;
        this.fxxx += k + 9;
        mm(k+k,k==0);
        mmm(9);
        j = mmm(j+1) + mmm(10);
        synchronized (this) { 
            if (k == 14) {
                k += 0;
            } else {
                k += 10;
            }
        }
        int m = 2;
        switch (m) {
            case 1: m = 1; break;
            case 2: m = 2; break;
            default: m = 0;
        }
        m++;
        switch (m) {
            case 1: m = 1; break;
            case 2: m = 2; break;
            default: m = 0;
        }
        m = k == 14 ? (k += 2) : -k;
        { 
            int zz = 9;
            boolean b = zz == 9 || zz == 0;
            b = zz == 0 || zz == 9;
            b = zz == 0 && zz == 9;
            b = zz == 9 && zz == 0;
        }
        assert false == false: "asd";
        //@ assert k != 7;
        //@ assert (k == 7) ==> (k != 7);
        //@ assert !((k != 7) ==> (k == 7));
        //@ ghost int x = 9;
        //@ set x = x + 9;
        //@ debug x = 0;
        //@ set x = (\lbl AAA k+1);
        //-ESC@ set x = (\lbl BBB k+1);
        for (int z = 0; z<4; z = z + 1) {
            m = m + 1;
        }
        //@ assume a.length > 10;
        a[2] = 42;
        m = a[1+1] - a[2];
        a[1] = k + 1;
        a[1] += k + 1;
        sf = 4;
        trace.sf = 5;
        m = sf + trace.sf;
        try {
            m = 8;
            throw new Exception();
        } catch (RuntimeException e) {
            m = 9;
        } catch (Exception e) {
            m = 10;
        } finally {
            m = 11;
        }
        return 0;
    }
}