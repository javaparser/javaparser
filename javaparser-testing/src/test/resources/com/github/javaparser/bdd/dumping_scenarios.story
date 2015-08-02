Scenario: When printing the instantiation we should use the right amount of spaces

Given the class:
public class A {
    Object foo = new Object();
	Runnable runnable = ()-> System.out.println("running");
    Consumer<Integer> counter = i->{ i+=1; System.out.println(i);};
}
When the class is parsed by the Java parser
Then it is dumped to:
public class A {

    Object foo = new Object();

    Runnable runnable = () -> System.out.println("running");

    Consumer<Integer> counter =  i -> {
        i += 1;
        System.out.println(i);
    };
}
