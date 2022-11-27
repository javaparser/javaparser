public class ResolutionTest {
    public int i,j;
    /*@
    forall int x, int j;
    ensures i > 2;
    ensures x > 2;
    ensures j > 2;
    ensures (\let int x = 0; x>0);
    signals (Exception e) e != null;
    */
    public void foo() {

    }

}

/*
class JML  {
    public <T> T \old(T obj);
}*/