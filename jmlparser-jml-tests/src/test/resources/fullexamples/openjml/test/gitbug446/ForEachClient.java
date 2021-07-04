public class ForEachClient {
    public static void main(String [] argv) {
        Integer[] mya = new Integer[2];
        mya[0] = 5; mya[1] = 4;
        APMax pm = new APMax();
        ArrOps<Integer> ao = new ArrOps<Integer>();
        ao.forEach(mya, pm);
        //@ assert pm.getMax() == 5;
        System.out.println("max is " + pm.getMax());
    }
}

