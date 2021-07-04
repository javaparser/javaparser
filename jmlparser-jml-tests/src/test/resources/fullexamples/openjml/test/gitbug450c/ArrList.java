// This test case corresponds to Git issue #450
// Produces different results with -minQuant and -no-minQuant
import java.util.ArrayList;

public class ArrList {
    public ArrayList<Integer> theList;

    //@ ensures theList != null;
    //@ ensures theList.size() == 1;
    // @ ensures theList.indexOf(a) == 0; // FIXME - at this time, the spec of ArrayList (and List) is not adequate to prove this assertion
    //@ pure // constructor
    public ArrList(int a) {
        theList = new ArrayList<Integer>();
        theList.add(a);
    }

    //@ assignable System.out.outputText;
    public static void main(String[] args) {
        ArrList al = new ArrList(1);
        System.out.println(al.theList.get(0));
    }
}