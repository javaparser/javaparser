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

Scenario: An enum without fields has no () on its members
Given the compilation unit:
package test; enum XYZ {A,B,C}
When the class is parsed by the Java parser
Then it is dumped to:
package test;

enum XYZ {

    A, B, C
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

Scenario: A multi-catch is printed correctly
Given the class:
class A {
    public void a() {
        try {
        } catch (IndexOutOfBoundException | IOException e) { 
        } 
    }
}
When the class is parsed by the Java parser
Then it is dumped to:
class A {

    public void a() {
        try {
        } catch (IndexOutOfBoundException | IOException e) {
        }
    }
}

Scenario: An empty import does not fail
Given the class:
package a.b.c;

;
When the class is parsed by the Java parser
Then it is dumped to:
package a.b.c;

;

Scenario: we can parse blocks
Given the block:
{
    a=2;
    b=3;
}
When the block is parsed by the Java parser
Then it is dumped to:
{
    a = 2;
    b = 3;
}

Scenario: we can parse statements
Given the statement:
while (true) {
}
When the statement is parsed by the Java parser
Then it is dumped to:
while (true) {
}

Scenario: we can parse imports
Given the import:
import static a.b.c.Abc.*;
When the import is parsed by the Java parser
Then it is dumped to:
import static a.b.c.Abc.*;

Scenario: we can parse annotations
Given the annotation:
@Abc
When the annotation is parsed by the Java parser
Then it is dumped to:
@Abc

Scenario: we can parse body declarations
Given the body:
private static final int x = 20;
When the body declaration is parsed by the Java parser
Then it is dumped to:
private static final int x = 20;

Scenario: we can parse class body declarations
Given the body:
public int xyz() {}
When the class body declaration is parsed by the Java parser
Then it is dumped to:
public int xyz() {
}

Scenario: we can parse interface body declarations
Given the body:
int xyz();
When the interface body declaration is parsed by the Java parser
Then it is dumped to:
int xyz();

Scenario: It doesn't throw NPE when using a modifierVisitorAdapter
Given the class:
public class Example {
  private String mString;
  public Example(String arg) {
    mString = arg;
  }
}
When the class is parsed by the Java parser
When the class is visited by an empty ModifierVisitorAdapter
Then it is dumped to:
public class Example {

    private String mString;

    public Example(String arg) {
        mString = arg;
    }
}