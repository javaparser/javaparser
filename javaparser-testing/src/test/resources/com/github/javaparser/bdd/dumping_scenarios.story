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



Scenario: Dumping orphan comments in empty method (issue 192)
Given the class:
public class StepImplementation {
    @Step("A step")
    public void contextStep() {
        // Foo bar
    }
}
When the class is parsed by the Java parser
Then it is dumped to:
public class StepImplementation {

    @Step("A step")
    public void contextStep() {
    // Foo bar
    }
}


Scenario: Dumping orphan comments in for loop (issue 192)
Given the class:
public class StepImplementation {
    public void contextStep() {
        for (int i = 0; i < 5; i++) {
            // foo bar
        }
    }
}
When the class is parsed by the Java parser
Then it is dumped to:
public class StepImplementation {

    public void contextStep() {
        for (int i = 0; i < 5; i++) {
        // foo bar
        }
    }
}


Scenario: Dumping orphan and attributed comments in for loop (issue 192)
Given the class:
public class StepImplementation {
public void contextStep() {
        for (int i = 0; i < 5; i++) {
            // foo bar
            System.out.println();
            // another foo bar
        }
    }
}
When the class is parsed by the Java parser
Then it is dumped to:
public class StepImplementation {

    public void contextStep() {
        for (int i = 0; i < 5; i++) {
            // foo bar
            System.out.println();
        // another foo bar
        }
    }
}


Scenario: An empty Enum is dumped correctly
Given the compilation unit:
package test; enum XYZ {}
When the class is parsed by the Java parser
Then it is dumped to:
package test;

enum XYZ {

}


Scenario: Strings with escaped newlines are parsed correctly
Given the class:
class A {
    public void helloWorld(String greeting, String name) {
        return "hello\nworld";
    }
}
When the class is parsed by the Java parser
Then it is dumped to:
class A {

    public void helloWorld(String greeting, String name) {
        return "hello\nworld";
    }
}
