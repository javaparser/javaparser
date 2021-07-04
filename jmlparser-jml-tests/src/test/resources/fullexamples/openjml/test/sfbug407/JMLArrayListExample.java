import java.util.ArrayList;
public class JMLArrayListExample {
public ArrayList<String> elements;

public JMLArrayListExample () {
    elements = new ArrayList<String>();
}

//@ assignable elements.objectState;
//@ ensures (elements.contains(s));
public void add(String s){
    //@ reachable;
    elements.add(s);
    //@ reachable;
}

public static void main (String[] args){
    System.out.println("wait");
    JMLArrayListExample jale = new JMLArrayListExample();
    jale.add("hello");

}

}