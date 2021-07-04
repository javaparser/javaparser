public class Test542 {

    /*@ spec_public @*/
    private int[] vals= new int[10];
    
    /*@
      public model int countVals;
      represents countVals = (\sum int i; 0<=i && i<vals.length; vals[i]);
      @*/
    
    //@requires countVals > 0;
    public void m() {       
    }
    
    public static void main(String[] args) {
        Test542 t = new Test542();
        t.m();
        System.out.println("DONE");
    }
}