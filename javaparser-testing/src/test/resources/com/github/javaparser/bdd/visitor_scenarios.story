Scenario: A class that is replicated using a CloneVisitor should be equal to the source

Given a CompilationUnit
Given a second CompilationUnit
When the following source is parsed:
package japa.parser;
public class ClassEquality {

    public void aMethod(){
        int a=0; // second comment
    }
}
When the CompilationUnit is cloned to the second CompilationUnit
Then the CompilationUnit is equal to the second CompilationUnit
Then the CompilationUnit has the same hashcode to the second CompilationUnit


Scenario: A classes variable name is changed to uppercase VoidVisitorAdapter

Given a CompilationUnit
Given a VoidVisitorAdapter with a visit method that changes variable names to uppercase
When the following source is parsed:
package japa.parser;
public class ToUpperClass {
    private int zero = 0;
}
When the CompilationUnit is visited by the to uppercase visitor
Then the expected source should be:
package japa.parser;
public class ToUpperClass {
    private int ZERO = 0;
}

Scenario: A class with a try statement is visited using by a VoidVisitorAdapter

Given a CompilationUnit
Given a VoidVisitorAdapter with a visit method and collects the variable names
When the following source is parsed:
package japa.parser;
public class ToUpperClass {
    public void aMethod(){
        try {
            int zero = 0;
        }catch (Exception exception) {
        }
    }
}
When the CompilationUnit is visited by the variable name collector visitor
Then the collected variable name is "exception;zero;"


Scenario: A class with a try statement is visited using by a GenericVisitorAdapter

Given a CompilationUnit
Given a GenericVisitorAdapter with a visit method that returns variable names
When the following source is parsed:
package japa.parser;
public class ToUpperClass {
    public void aMethod(){
        try {
            int zero = 0;
        }catch (Exception exception) {
        }
    }
}
When the CompilationUnit is visited by the visitor that returns variable names
Then the return variable name is "zero"
