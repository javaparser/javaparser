Scenario: Test declaration as String for constructor on parsed class

Given a CompilationUnit
When the following source is parsed:
class ClassWithAConstructor {
    protected ClassWithAConstructor(int a, String b) throws This, AndThat, AndWhatElse {
    }
}
Then constructor 1 in class 1 declaration as a String is "protected ClassWithAConstructor(int a, String b) throws This, AndThat, AndWhatElse"
Then all nodes refer to their parent


Scenario: Test declaration as String exclusing modifiers and throws for constructor on parsed class

Given a CompilationUnit
When the following source is parsed:
class ClassWithAConstructor {
    protected ClassWithAConstructor(int a, String b) throws This, AndThat, AndWhatElse {
    }
}
Then constructor 1 in class 1 declaration short form as a String is "ClassWithAConstructor(int a, String b)"
Then all nodes refer to their parent


Scenario: Test declaration as String exclusing modifiers and throws for method on parsed class

Given a CompilationUnit
When the following source is parsed:
class ClassWithAMethod {
    /*comment1*/
    final protected /*comment2*/ native List<String> /*comment2*/ aMethod(int a, String b) throws /*comment3*/ This, AndThat, AndWhatElse {

    }
}
Then method 1 in class 1 declaration as a String is "protected final native List<String> aMethod(int a, String b) throws This, AndThat, AndWhatElse"
Then all nodes refer to their parent


Scenario: Test declaration as String exclusing modifiers and throws for method on parsed class

Given a CompilationUnit
When the following source is parsed:
class ClassWithAMethod {
    /*comment1*/
    final protected /*comment2*/ native List<String> /*comment2*/ aMethod(int a, String b) throws /*comment3*/ This, AndThat, AndWhatElse {

    }
}
Then method 1 in class 1 declaration as a String short form is "List<String> aMethod(int a, String b)"
Then all nodes refer to their parent


Scenario: The same class source is parsed by two different compilation units and should therefore be equal

Given a CompilationUnit
Given a second CompilationUnit
When the following source is parsed:
package japa.parser.comments;
public class ClassEquality {

    public void aMethod(){
        // first comment
        int a=0; // second comment
    }
}
When the following sources is parsed by the second CompilationUnit:
package japa.parser.comments;
public class ClassEquality {

    public void aMethod(){
        // first comment
        int a=0; // second comment
    }
}
Then the CompilationUnit is equal to the second CompilationUnit
Then the CompilationUnit has the same hashcode to the second CompilationUnit
Then all nodes refer to their parent
Then all nodes of the second compilation unit refer to their parent


Scenario: Two different class sources are parsed by two different compilation units and should not be equal

Given a CompilationUnit
Given a second CompilationUnit
When the following source is parsed:
package japa.parser.comments;
public class ClassEquality {

    public void aMethod(){
        // first comment
        int a=0; // second comment
    }
}
When the following sources is parsed by the second CompilationUnit:
package japa.parser.comments;
public class DifferentClass {

    public void aMethod(){
        // first comment
        int a=0; // second comment
    }
}
Then the CompilationUnit is not equal to the second CompilationUnit
Then the CompilationUnit has a different hashcode to the second CompilationUnit
Then all nodes refer to their parent
Then all nodes of the second compilation unit refer to their parent


Scenario: Classes that only differ by comments should not be equal or have the same hashcode

Given a CompilationUnit
Given a second CompilationUnit
When the following source is parsed:
package japa.parser.comments;
public class ClassEquality {

    public void aMethod(){
        // first comment
        int a=0; // second comment
    }
}
When the following sources is parsed by the second CompilationUnit:
package japa.parser.comments;
public class ClassEquality {

    public void aMethod(){
        // first comment
        int a=0;
    }
}
Then the CompilationUnit is not equal to the second CompilationUnit
Then the CompilationUnit has a different hashcode to the second CompilationUnit
Then all nodes refer to their parent
Then all nodes of the second compilation unit refer to their parent


Scenario: A class with a colon in the annoation value is parsed by the Java Parser

Given a CompilationUnit
When the following source is parsed:
package japa.parser.ast;
import org.junit.Test;
public class Issue37 {
    public static @interface SomeAnnotation {
        String value();
    }
    // Parser bug: the type of this field
    @SomeAnnotation("http://someURL.org/")
    protected Test test;
}
Then field 1 in class 1 contains annotation 1 value is ""http://someURL.org/""
Then all nodes refer to their parent


Scenario: A class with a Lambdas is parsed by the Java Parser

Given a CompilationUnit
When the following source is parsed:
package bdd.samples;
import java.util.stream.Stream;
public class Lambdas {

    public static void main(String[] args) {
        // Lambda Runnable
        Runnable r1 = () -> System.out.println("Hello world!");
        Runnable r2 = () -> {};
        Runnable r3 = () -> { System.out.println("Hello world two!"); };

        Stream<CharSequence> stream = Stream.generate((Supplier<CharSequence>) () -> "foo");
    }
}
Then lambda in statement 1 in method 1 in class 1 is called r1
Then lambda in statement 2 in method 1 in class 1 is called r2
Then lambda in statement 3 in method 1 in class 1 is called r3
Then lambda in statement 1 in method 1 in class 1 body is "System.out.println("Hello world!");"
Then lambda in statement 2 in method 1 in class 1 block statement is null
Then lambda in statement 3 in method 1 in class 1 block statement is "System.out.println("Hello world two!");"
Then lambda in statement 1 in method 1 in class 1 is parent of contained body
Then lambda in statement 3 in method 1 in class 1 is parent of contained body
Then all nodes refer to their parent
Then lambda in method call in statement 4 in method 1 in class 1 body is ""foo";"


Scenario: A class with parameterized Lambdas is parsed by the Java Parser

Given a CompilationUnit
When the following source is parsed:
package com.github.javapasrser.bdd.parsing;
import java.util.function.Function;
public class ParameterizedLambdas {
    public static void main(String[] args) {
        Function<Integer,String> f1 = (Integer i) -> String.valueOf(i);
        Function<Integer,String> f2 = (i) -> String.valueOf(i);
        Function<Integer,String> f3 = i -> String.valueOf(i);
    }
}
Then lambda in statement 1 in method 1 in class 1 is parent of contained parameter
Then lambda in statement 2 in method 1 in class 1 is parent of contained parameter
Then lambda in statement 3 in method 1 in class 1 is parent of contained parameter
Then lambda in statement 1 in method 1 in class 1 is parent of contained body
Then lambda in statement 2 in method 1 in class 1 is parent of contained body
Then lambda in statement 3 in method 1 in class 1 is parent of contained body
Then lambda in statement 1 in method 1 in class 1 has parameters with non-null type
Then lambda in statement 2 in method 1 in class 1 has parameters with non-null type
Then lambda in statement 3 in method 1 in class 1 has parameters with non-null type


Scenario: A class with multi-parameters Lambdas is parsed by the Java Parser

Given a CompilationUnit
When the following source is parsed:
package com.github.javapasrser.bdd.parsing;
import java.util.function.Function;
public class MultiParameterizedLambdas {
    public static void main(String[] args) {
        BiFunction<Integer, Integer, String> f = (a, b) -> String.valueOf(a) + String.valueOf(b);
    }
}
Then lambda in statement 1 in method 1 in class 1 has parameters with non-null type


Scenario: A class with a method reference is parsed by the Java Parser

Given a CompilationUnit
When the following source is parsed:
public class Person {

    String name;
    LocalDate birthday;

    public void sortByAge(Person[] people){
        Arrays.sort(people, Person::compareByAge);
    }

    public static int compareByAge(Person a, Person b) {
        return a.birthday.compareTo(b.birthday);
    }
}
Then method reference in statement 1 in method 1 in class 1 scope is Person
Then method reference in statement 1 in method 1 in class 1 identifier is compareByAge
Then all nodes refer to their parent


Scenario: An interface with a default method is parsed by the Java Parser

Given a CompilationUnit
When the following source is parsed:
interface MyInterface {
    default String doSomething(){
        return "implementation in an interface!";
    }

    String doSomethingElse();
}
Then method 1 class 1 is a default method
Then method 2 class 1 is not a default method
Then all nodes refer to their parent


Scenario: simple cast on lambda expression can be parsed

Given a CompilationUnit
When the following source is parsed:
class A {
    static final Comparator<ChronoLocalDate> DATE_ORDER =
        (Comparator<ChronoLocalDate>) (date1, date2) -> {
            return Long.compare(date1.toEpochDay(), date2.toEpochDay());
        };
}
Then all nodes refer to their parent

Scenario: a combined cast on lambda expression can be parsed

Given a CompilationUnit
When the following source is parsed:
class A {
    static final Comparator<ChronoLocalDate> DATE_ORDER =
        (Comparator<ChronoLocalDate> & Serializable) (date1, date2) -> {
            return Long.compare(date1.toEpochDay(), date2.toEpochDay());
        };
}
Then all nodes refer to their parent

Scenario: a combined cast on a literal can be parsed

Given a CompilationUnit
When the following source is parsed:
class A {
    static int a = (Comparator<ChronoLocalDate> & Serializable) 1;
}
Then all nodes refer to their parent

