Scenario: A Node can only ever be equal to a class that extends Node

Given a CompilationUnit
Then is not equal to null
Then is not equal to "Some String Value"


Scenario: A BlockStmt can be created by a provided String

Given a BlockStmt
When is the String "{return x+y;}" is parsed by the JavaParser using parseBlock
Then Statement 1 in BlockStmt toString is "return x + y;"


Scenario: A Statement can be created by a provided String

Given a Statement
When is the String "x = x+y;" is parsed by the JavaParser using parseStatement
Then Statement toString is "x = x + y;"


Scenario: Adding declarations to a TryStmt it is set as the parent of all provided declarations

Given a TryStmt
Given a List of VariableDeclarations
When the List of VariableDeclarations are set as the resources on TryStmt
Then all the VariableDeclarations parent is the TryStmt


Scenario: Creating a complete CompilationUnit

Given a CompilationUnit
When the package declaration is set to "japa.parser.ast.manipulation"
When a public class called "CreateClass" is added to the CompilationUnit
When a public static method called "main" returning void is added to class 1 in the compilation unit
When String varargs called "args" are added to method 1 in class 1
When a BlockStmt is added to method 1 in class 1
When System.out.println("Hello World!"); is added to the body of method 1 in class 1
Then the expected source should be:
package japa.parser.ast.manipulation;

public class CreateClass {

    public static void main(String... args) {
        System.out.println("Hello World!");
    }
}


Scenario: Change the name of a method to be uppercase

Given a CompilationUnit
When the following source is parsed:
package japa.parser.ast.manipulation;

public class UpdateMethod {

    public void changeToUpperCase(){}

    public void anotherMethodToChange(){}
}
When method 1 in class 1 has it's name converted to uppercase
Then method 1 in class 1 has the name "CHANGETOUPPERCASE"


Scenario: Change the name of all methods to be uppercase using a visitor

Given a CompilationUnit
When the following source is parsed:
package japa.parser.ast.manipulation;

public class UpdateMethod {

    public void changeToUpperCase(){}

    public void anotherMethodToChange(){}
}
Given a ChangeNameToUpperCaseVisitor
When the ChangeNameToUpperCaseVisitor visits to compilation unit
Then method 1 in class 1 has the name "CHANGETOUPPERCASE"
Then method 2 in class 1 has the name "ANOTHERMETHODTOCHANGE"


Scenario: Add int arguments to a method

Given a CompilationUnit
When the following source is parsed:
package japa.parser.ast.manipulation;

public class UpdateMethod {

    public void changeToUpperCase(String parameter){}

    public void anotherMethodToChange(){}
}
When method 2 in class 1 has an int parameter called "value" added
Then method 1 in class 1 has 1 parameters
Then method 2 in class 1 has 1 parameter
Then method 2 in class 1 parameter 1 is type int called "value"


Scenario: Add int arguments to all methods using a visitor

Given a CompilationUnit
When the following source is parsed:
package japa.parser.ast.manipulation;

public class UpdateMethod {

    public void changeToUpperCase(String parameter){}

    public void anotherMethodToChange(){}
}
Given a AddNewIntParameterCalledValueVisitor
When the AddNewIntParameterCalledValueVisitor visits to compilation unit
Then method 1 in class 1 has 2 parameters
Then method 2 in class 1 has 1 parameter
Then method 1 in class 1 parameter 2 is type int called "value"
Then method 2 in class 1 parameter 1 is type int called "value"


Scenario: Clone a compilation unit

Given a CompilationUnit
When the following source is parsed:
package japa.parser.ast.manipulation;

public class UpdateMethod {

    public void changeToUpperCase(String parameter){}

    public void anotherMethodToChange(){}
}
When the compilation unit is cloned
Then method 1 in class 1 has the name "changeToUpperCase"
Then method 1 in class 1 has 1 parameters
Then method 2 in class 1 has 0 parameter