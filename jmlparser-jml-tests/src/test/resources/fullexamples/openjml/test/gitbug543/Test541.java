//@ non_null_by_default
public class Test541 implements I541 {
 
    public int[] buf = new int[10]; //@ in buffer;
    //@ public represents buffer = buf;
    
    // Inherited specs
    public void set(int[] src) { System.arraycopy(src, 0, buf, 0, buf.length); }

    // Inherited specs
    public void set(int[] src, int s, int d, int length) { 
        System.arraycopy(src, s, buf, d, length); 
        //@   assert (\forall int k; d<=k && k < d+length; buffer[k] == src[s-d+k]);
    }

    //@ requires length >= 0;
    //@ requires s >= 0;
    //@ requires s + length <= src.length;
    //@ requires d >= 0;
    //@ requires d + length <= buf.length;
    //@   assignable buf[d..d+length-1];
    //@   ensures (\forall int k; d<=k && k < d+length; buffer[k] == src[s-d+k]);
    // SMT has a hard time with the above formulation -- using equalArrays below works fine
    // Note the use of buffer in the specs and buf in the code
    //@ skipesc // FIXME - array quantification
    public void set1(int[] src, int s, int d, int length) { 
        System.arraycopy(src, s, buf, d, length); 
    }
    
    //@ requires length >= 0;
    //@ requires s >= 0;
    //@ requires s + length <= src.length;
    //@ requires d >= 0;
    //@ requires d + length <= buf.length;
    //@   assignable buf[d..d+length-1];
    //@   ensures java.util.Arrays.equalArrays(buffer,d,src,s,length);
    public void set1x(int[] src, int s, int d, int length) { 
        System.arraycopy(src, s, buf, d, length); 
    }
    
    //@ requires length >= 0;
    //@ requires s >= 0;
    //@ requires s + length <= src.length;
    //@ requires d >= 0;
    //@ requires d + length <= buf.length;
    //@   assignable buf[d..d+length-1];
    //@   ensures (\forall int k; s<=k && k < s+length; buffer[d-s+k] == src[k]);
    // SMT has a hard time with the above formulation -- using equalArrays above works fine
    // Note the use of buffer in the specs and buf in the code
    //@ skipesc // FIXME - array quantification
    public void set2(int[] src, int s, int d, int length) { 
        System.arraycopy(src, s, buf, d, length); 
    }
    
    //@ public normal_behavior
    //@   requires src.length >= buffer.length;
    //@   assignable buffer[*];
    //@   ensures (\forall int k; 0<=k && k<buffer.length; buf[k] == src[k]);
    public void m(int[] src) {
        set(src);
    }

    //@ public normal_behavior
    //@   requires src.length >= buffer.length;
    //@   assignable buffer[*];
    //@   ensures (\forall int k; 0<=k && k<buffer.length; buffer[k] == src[k]);
    public void m2(int[] src) {
        set(src);
    }
    
    //@ requires length >= 0;
    //@ requires s >= 0;
    //@ requires s + length <= src.length;
    //@ requires d >= 0;
    //@ requires d + length <= buf.length;
    //@ requires d == 0 && s == 0;
    //@   assignable \everything;
    public void kk(int[] src, int s, int d, int length) { 
        //@ assume  (\forall int k; 0<=k && k<length; buf[k] == src[k]);
        //@ assert  (\forall int k; 0<=k && k<length; buf[k] == src[k]);
    }

    //@ requires length >= 0;
    //@ requires s >= 0;
    //@ requires s + length <= src.length;
    //@ requires d >= 0;
    //@ requires d + length <= buf.length;
    //@   assignable \everything;
    public void kkk(int[] src, int s, int d, int length) { 
        //@ assume  (\forall int k; d<=k && k<d+length; buf[k] == src[s-d+k]);
        //@ assert  (\forall int k; d<=k && k<d+length; buf[k] == src[s-d+k]);
    }
    

    //@ requires length >= 0;
    //@ requires s >= 0;
    //@ requires s + length <= src.length;
    //@ requires d >= 0;
    //@ requires d + length <= buf.length;
    //@   assignable \everything;
    //@ skipesc // FIXME - This is equivalent to kkk() but Z3 at least does not prove it
    public void kkkbad(int[] src, int s, int d, int length) { 
        //@ assume  (\forall int k; 0<=k && k<length; buf[d+k] == src[s+k]);
        //@ assert  (\forall int k; 0<=k && k<length; buf[d+k] == src[s+k]);
    }

    
}

//@ non_null_by_default
interface I541 {
    
    //@ public instance model int[] buffer;
    
    //@ public normal_behavior
    //@   requires src.length >= buffer.length;
    //@   assignable buffer[*];
    //@   ensures (\forall int k; 0<=k && k<buffer.length; buffer[k] == src[k]);
    public void set(int[] src);
    
    //@ requires length >= 0;
    //@ requires s >= 0;
    //@ requires s + length <= src.length;
    //@ requires d >= 0;
    //@ requires d + length <= buffer.length;
    //@   assignable buffer[d..d+length-1];
    //@   ensures (\forall int k; d<=k && k < d+length; buffer[k] == src[s-d+k]);
   public void set(int[] src, int s, int d, int length) ;

}