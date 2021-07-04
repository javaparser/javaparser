import java.util.ArrayList;
public class MapToAlClient {
    public static void main(String [] argv) {
        Pair<Integer> myp = new Pair<Integer>(5,4);
        //@ assert myp.getFirst() == 5 && myp.getSecond() == 4;
        PMax pm = new PMax();
        ArrayList<Integer> r = myp.mapToAl(pm);
        //@ assert pm.getMax() == 5 && r.get(1) == 4;
        System.out.println("max is " + pm.getMax());
    }
}

