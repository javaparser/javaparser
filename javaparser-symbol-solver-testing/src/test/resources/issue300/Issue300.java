public class Issue300 {

    class A {
        int i;
    }

    class B {
        B() {
            new A().i = 0;
        }
    }
}
