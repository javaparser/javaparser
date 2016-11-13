Scenario: Compare CUs containing lambdas should not crash awfully

Given the first class:
public class ArrayListGenericDemo {

    public static void main(String[] argsList) {
        ArrayList<String> data = new ArrayList();
        data.forEach( s -> System.out.println(s));
    }
}
Given the second class:
public class ArrayListGenericDemo {

    public static void main(String[] argsList) {
        ArrayList<String> data = new ArrayList();
        data.forEach( s -> System.out.println(s));
    }
}
Then they are equals
