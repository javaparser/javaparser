public class EverythingWrong {
    public void foo(int x) {
        //@ghost int x = 0;
    }

    /*@ ensures \result>0; */
    public void bar(int x) {
    }

    /*@ requires \result>0; */
    public int bar(int x) {
        return 0;
    }

    /*@ requires x++; ensures x=2; */
    public int baf(int x) {
        return 0;
    }

    public void bar(int x) {
        /*@ ensures true; requires true; */
        while (true) ;
    }

    public final int x;

    /*@ assignable x; */
    public void bear() {
    }
}