Scenario: When printing the instantiation we should use the right amount of spaces

Given the class:
public class A {
    Object foo = new Object();
}
When the class is parsed by the Java parser
Then it is dumped to:
public class A {

    Object foo = new Object();
}


Scenario: When printing the lambda expression we should use the right indentation

Given the class:
public class B {
	Runnable runnable = ()-> System.out.println("running");
    Consumer<Integer> consumer = i->{ i+=1; System.out.println(i);};
}
When the class is parsed by the Java parser
Then it is dumped to:
public class B {

    Runnable runnable = () -> System.out.println("running");

    Consumer<Integer> consumer =  i -> {
        i += 1;
        System.out.println(i);
    };
}


Scenario: Dumping orphan comments in empty method
Given the class:
class A {
    public void helloWorld(String greeting, String name) {
        //sdfsdfsdf
            //sdfds
        /*
                            dgfdgfdgfdgfdgfd
         */
    }
}
When the class is parsed by the Java parser
Then it is dumped to:
class A {

    public void helloWorld(String greeting, String name) {
    //sdfsdfsdf
    //sdfds
    /*
                            dgfdgfdgfdgfdgfd
         */
    }
}