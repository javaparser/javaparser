public class T {

private /*@ spec_public @*/ int a = 2;
private /*@ spec_public @*/ int b = 1;
private /*@ spec_public @*/ int c;

//@ ensures \result == (a * c)/(0.06 * b);
public double m() {
    return a/b;
}

public static void main(String ... args) {
  (new T()).m();
}
}

