Scenario: A class that is replicated using a CloneVisitor should be equal to the source

Given a CompilationUnit
Given a second CompilationUnit
When the following source is parsed:
package japa.parser.comments;
public class ClassEquality {

    public void aMethod(){
        int a=0; // second comment
    }
}
When the CompilationUnit is cloned to the second CompilationUnit
Then the CompilationUnit is equal to the second CompilationUnit
Then the CompilationUnit has the same hashcode to the second CompilationUnit