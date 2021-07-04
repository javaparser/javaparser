public class StaticMethod {
    //@ public invariant data.length > 0;
    public int[] data;

    //@ requires d.length > 0;
    public StaticMethod(int[] d) {
        data = d;
    }

    //@ requires src.length > 0;
    public static void a(int[] src) {
    }

    public void b() {
        a(data);   
    }
}
