import java.util.ArrayList;

public class ListTest {

    private final /*@ spec_public  @*/ ArrayList<String> mylist;

    //@ ensures \result == mylist;
    public /*@ pure @*/ ArrayList<String> getMylist() {
        return mylist;
    }

    public ListTest() {
        mylist = new ArrayList<String>();}

    //@ requires getMylist().size() < Integer.MAX_VALUE;
    //@ ensures  \old(getMylist().size()) + 1 == getMylist().size()  ; 
    public void addStringInList(String a){
        this.mylist.add(a);
    }

}