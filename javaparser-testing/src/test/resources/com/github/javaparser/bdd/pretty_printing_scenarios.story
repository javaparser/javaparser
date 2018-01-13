Scenario: When printing the instantiation we should use the right amount of spaces

Given the class:
public class A {
    Object foo = new Object();
}
When the class is parsed by the Java parser
Then it is printed as:
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
Then it is printed as:
public class B {

    Runnable runnable = () -> System.out.println("running");

    Consumer<Integer> consumer = i -> {
        i += 1;
        System.out.println(i);
    };
}


Scenario: Printing orphan comments in empty method
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
Then it is printed as:
class A {

    public void helloWorld(String greeting, String name) {
    // sdfsdfsdf
    // sdfds
    /*
                            dgfdgfdgfdgfdgfd
         */
    }
}



Scenario: Printing orphan comments in empty method (issue 192)
Given the class:
public class StepImplementation {
    @Step("A step")
    public void contextStep() {
        // Foo bar
    }
}
When the class is parsed by the Java parser
Then it is printed as:
public class StepImplementation {

    @Step("A step")
    public void contextStep() {
    // Foo bar
    }
}


Scenario: Printing orphan comments in for loop (issue 192)
Given the class:
public class StepImplementation {
    public void contextStep() {
        for (int i = 0; i < 5; i++) {
            // foo bar
        }
    }
}
When the class is parsed by the Java parser
Then it is printed as:
public class StepImplementation {

    public void contextStep() {
        for (int i = 0; i < 5; i++) {
        // foo bar
        }
    }
}


Scenario: Printing orphan and attributed comments in for loop (issue 192)
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
Then it is printed as:
public class StepImplementation {

    public void contextStep() {
        for (int i = 0; i < 5; i++) {
            // foo bar
            System.out.println();
        // another foo bar
        }
    }
}


Scenario: An empty Enum is printed correctly
Given the compilation unit:
package test; enum XYZ {}
When the class is parsed by the Java parser
Then it is printed as:
package test;

enum XYZ {
}

Scenario: An enum without fields has no () on its members
Given the compilation unit:
package test; enum XYZ {A,B,C}
When the class is parsed by the Java parser
Then it is printed as:
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
Then it is printed as:
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
Then it is printed as:
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
Then it is printed as:
package a.b.c;

Scenario: we can parse blocks
Given the block:
{
    a=2;
    b=3;
}
When the block is parsed by the Java parser
Then it is printed as:
{
    a = 2;
    b = 3;
}

Scenario: we can parse statements
Given the statement:
while (true) {
}
When the statement is parsed by the Java parser
Then it is printed as:
while (true) {
}

Scenario: we can parse static on demand imports
Given the import:
import static a.b.c.Abc.*;
When the import is parsed by the Java parser
Then it is printed as:
import static a.b.c.Abc.*;

Scenario: we can parse static type imports
Given the import:
import static a.b.c.Abc;
When the import is parsed by the Java parser
Then it is printed as:
import static a.b.c.Abc;

Scenario: we can parse on demand imports
Given the import:
import a.b.c.*;
When the import is parsed by the Java parser
Then it is printed as:
import a.b.c.*;

Scenario: we can parse type imports
Given the import:
import a.b.c.Abc;
When the import is parsed by the Java parser
Then it is printed as:
import a.b.c.Abc;

Scenario: we can parse annotations
Given the annotation:
@Abc
When the annotation is parsed by the Java parser
Then it is printed as:
@Abc

Scenario: we can parse body declarations
Given the body:
String author();
When the annotation body declaration is parsed by the Java parser
Then it is printed as:
String author();

Scenario: we can parse class body declarations
Given the body:
public int xyz() {}
When the class body declaration is parsed by the Java parser
Then it is printed as:
public int xyz() {
}

Scenario: we can parse interface body declarations
Given the body:
int xyz();
When the interface body declaration is parsed by the Java parser
Then it is printed as:
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
Then it is printed as:
public class Example {

    private String mString;

    public Example(String arg) {
        mString = arg;
    }
}

Scenario: JavaDoc OR comment is printed, not both.
Given the class:
public class Foo {
    /** This line gets duplicated */
    public void foo() {
    }
}
When the class is parsed by the Java parser
Then it is printed as:
public class Foo {

    /**
     * This line gets duplicated
     */
    public void foo() {
    }
}

Scenario: various lamba casts (issue 418)
Given the class:
public class TestLambda {
    void okMethod() {
        return (ITF) () -> {
            return true;
        };
    }
    void faliingMethod() {
        testThis(check ? null : (ITF) () -> {
            return true;
        });
    }
}
When the class body declaration is parsed by the Java parser
Then it is printed as:
public class TestLambda {

    void okMethod() {
        return (ITF) () -> {
            return true;
        };
    }

    void faliingMethod() {
        testThis(check ? null : (ITF) () -> {
            return true;
        });
    }
}

Scenario: Duplicate methods are not a parsing error (#416)
Given the class:
public class Foo {
    public void foo() {
    }
    public void foo() {
    }
    public void foo() {
    }
}
When the class is parsed by the Java parser
Then it is printed as:
public class Foo {

    public void foo() {
    }

    public void foo() {
    }

    public void foo() {
    }
}

Scenario: Both array syntaxes are supported (#416)
Given the class:
public class Foo {
    public void m1(boolean[] boolArray) {}
    public void m1(boolean boolArray[]) {}
    public void m1(boolean[] boolArray[]) {}
}
When the class is parsed by the Java parser
Then it is printed as:
public class Foo {

    public void m1(boolean[] boolArray) {
    }

    public void m1(boolean[] boolArray) {
    }

    public void m1(boolean[][] boolArray) {
    }
}


Scenario: Array parts can be annotated
Given the class:
class Foo {
    void m1(@Boo boolean @Index1 [] @ Index2 [] boolArray) {}
}
When the class is parsed by the Java parser
Then it is printed as:
class Foo {

    void m1(@Boo boolean @Index1 [] @Index2 [] boolArray) {
    }
}

Scenario: Annotations are supported on annotations
Given the class:
@C @interface D {
}
When the class is parsed by the Java parser
Then it is printed as:
@C
@interface D {
}

Scenario: Annotations are supported on interfaces
Given the class:
@C interface Abc {
}
When the class is parsed by the Java parser
Then it is printed as:
@C
interface Abc {
}

Scenario: Annotations are supported on enums
Given the class:
@C enum Abc {
}
When the class is parsed by the Java parser
Then it is printed as:
@C
enum Abc {
}

Scenario: Annotations are supported on classes (issue 436 is the commented part)
Given the compilation unit:
@C
public class Abc<@C A, @C X extends @C String & @C Serializable> {

	@C int @C[] @C []f;

	@C
	public Abc(@C int p, List<@C ? extends Object> aa){
		@C int b;
	}
	public @C void a(@C int o) {
/*		try {
			throw new IOException();
		} catch (@C NullPointerException | @C IOException e) {
		}
*/	}
}
When the compilation unit is parsed by the Java parser
Then it is printed as:
@C
public class Abc<@C A, @C X extends @C String & @C Serializable> {

    @C
    int @C [] @C [] f;

    @C
    public Abc(@C int p, List<@C ? extends Object> aa) {
        @C int b;
    }

    @C
    public void a(@C int o) {
    /*		try {
			throw new IOException();
		} catch (@C NullPointerException | @C IOException e) {
		}
*/
    }
}


Scenario: Annotations are supported inside catch (issue 436)
Given the compilation unit:
public class Abc {
	public void a() {
		try {
		} catch (@C NullPointerException | @C IOException e) {
		}
	}
}
When the compilation unit is parsed by the Java parser
Then it is printed as:
public class Abc {

    public void a() {
        try {
        } catch (@C NullPointerException | @C IOException e) {
        }
    }
}

Scenario: Inner class notation does not confuse annotations (#107)
Given the class:
class A extends @Ann1 B.@Ann2 C {
}
When the class is parsed by the Java parser
Then it is printed as:
class A extends @Ann1 B.@Ann2 C {
}

Scenario: Make sure interface extends can be annotated
Given the class:
interface A extends @X B, @Y C, @Z D {
}
When the class is parsed by the Java parser
Then it is printed as:
interface A extends @X B, @Y C, @Z D {
}

Scenario: default modifier isn't printed twice
Given the class:
interface X {default String author(){}}
When the annotation body declaration is parsed by the Java parser
Then it is printed as:
interface X {

    default String author() {
    }
}
