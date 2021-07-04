import java.util.ArrayList;
public class JMLArrayListExample {
public ArrayList elements;

public JMLArrayListExample () {
    elements = new ArrayList<String>();
}

//@ ensures (elements.contains(s));
public void add(String s){
    elements.add(s);

}


public static void main (String[] args){
    System.out.println("wait");
    JMLArrayListExample jale = new JMLArrayListExample();
    jale.add("hello");


}

}