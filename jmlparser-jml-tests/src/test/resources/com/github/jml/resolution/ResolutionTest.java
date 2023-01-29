public class ResolutionTest {
    public int i, j;

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


//? name: e@(line 9,col 27) to e@(line 9,col 14)
//? name: i@(line 5,col 13) to i@(line 2,col 5)
//? name: j@(line 7,col 13) to j@(line 4,col 19)
//? name: x@(line 6,col 13) to x@(line 4,col 12)
//? name: x@(line 8,col 30) to x@(line 8,col 19)
//? type: e@(line 9,col 27)
//? type: i@(line 5,col 13)
//? type: j@(line 7,col 13)
//? type: x@(line 6,col 13)
//? type: x@(line 8,col 30)