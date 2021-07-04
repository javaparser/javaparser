// This test case is a different case of Git issue #450; has an NPE with -minQuant

import java.util.ArrayList;

public class ArrList {
    public ArrayList<Integer> theList;

    // Use default assignable, else use assignable theList, theList.*;
//    //@ ensures theList != null;
    //@ ensures theList.indexOf(a) == 0;
    public ArrList(int a) {
        theList = new ArrayList<Integer>();
//        theList.add(a);
    }

=======
// This test case corresponds to Git issue #450

import java.util.ArrayList;

public class ArrList {
    public ArrayList<Integer> theList;

    // Use default assignable, else use assignable theList, theList.*;
    //@ ensures theList != null;
    //@ ensures theList.size() == 1;
    // @ ensures theList.indexOf(a) == 0; // FIXME - at this time, the spec of ArrayList (and List) is not adequate to prove this assertion
    public ArrList(int a) {
        theList = new ArrayList<Integer>();
        theList.add(a);
    }

    //@ assignable \nothing;
    public static void main(String[] args) {
        ArrList al = new ArrList(1);
        // @ assert al.theList.content.owner == al.theList; // FIXME - with -minQuant, this assertion cannot be proved, though it can with -no-minQuant
        System.out.println(al.theList.get(0));
    }
}