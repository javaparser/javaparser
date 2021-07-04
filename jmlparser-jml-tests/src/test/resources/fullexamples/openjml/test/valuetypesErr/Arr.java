public class Arr {

    int array;

public void m(String ... args) {

//@ ghost array<Short> arx = args.array; // ERROR
Integer[] a = new Integer[10];
//@ ghost array<Integer> ar = a.array; // OK
//@ ghost int kk = this.array;

int k = this.array;
boolean b = a.array;
}
}
