// This test case corresponds to Git issue #450
// This version has a type chekcing error
import java.util.ArrayList;

public class ArrList {

    public ArrayList<String> theList;

    // Use default assignable, else use assignable theList, theList.*;
    //@ ensures theList != null;
    //@ ensures theList.size() == 1;
    // @ ensures theList.indexOf(a) == 0; // FIXME - at this time, the spec of ArrayList (and List) is not adequate to prove this assertion
    public ArrList(int a) {
        theList = new ArrayList<String>();
        theList.add(a);
    }

    //@ assignable \nothing;
    public static void main(String[] args) {
        ArrList al = new ArrList(1);
        // @ assert al.theList.content.owner == al.theList; // FIXME - with -minQuant, this assertion cannot be proved, though it can with -no-minQuant
        //System.out.println(al.theList.get(0));
    }
}