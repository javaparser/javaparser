Scenario: A Class With Line Comments is processed by the Java Parser

Given the class:
package japa.parser.comments;

public class ClassWithLineComments {

    public void aMethod(){
        // first comment
        int a=0; // second comment
        // third comment
        // fourth comment
    }
}
When the class is parsed by the Java parser
Then the compilation unit is not commented
Then the compilation unit has 0 orphan comments
Then class 1 has 4 total contained comments
Then method 1 in class 1 has 4 total contained comments
Then method 1 in class 1 has 0 orphan comments
Then block statement in method 1 in class 1 has 4 total contained comments
Then block statement in method 1 in class 1 has 3 orphan comments



Scenario: A Class With Line Comments is processed by the Java Parser

Given the class:
package japa.parser.comments;

/**Javadoc associated with the class*/
public class ClassWithOrphanComments {
    //a first comment floating in the class

    //comment associated to the method
    void foo(){
        /*comment floating inside the method*/
    }

    //a second comment floating in the class
}

//Orphan comment inside the CompilationUnit
When the class is parsed by the Java parser
Then the compilation unit is not commented
Then the compilation unit has 6 contained comments
Then the compilation unit orphan comment 1 is "Orphan comment inside the CompilationUnit"
Then class 1 orphan comment 1 is "a first comment floating in the class"
Then class 1 orphan comment 2 is "a second comment floating in the class"
Then class 1 is commented "Javadoc associated with the class"
Then class 1 has 4 total contained comments
Then method 1 in class 1 has 0 orphan comments
Then method 1 in class 1 is commented "comment associated to the method"
Then comment 1 in method 1 in class 1 is "comment floating inside the method"
Then block statement in method 1 in class 1 orphan comment 1 is "comment floating inside the method"


Scenario: A Class With Orphan Comment in Class Declaration is parsed by the Java Parser

Given the class:
class /*Comment1*/ A {
    //comment2
    // comment3
    int a;
    /**comment4
    *
    * */
    //comment5
}
When the class is parsed by the Java parser
Then class 1 is not commented
Then class 1 orphan comment 1 is "Comment1"


Scenario: A Class With Line Comments in Multiple Methods is parsed by the Java Parser

Given the class:
package japa.parser.comments;

public class ClassWithLineCommentsInMultipleMethods {

    public void aMethod() {
        // first comment
        int a = 0; //second comment
        // third comment
        // fourth comment
    }

    public void anotherMethod() {
        // a unique comment
        // first comment
        int a = 0; //second comment
        // third comment
        // fourth comment
    }
}
When the class is parsed by the Java parser
Then the compilation unit has 9 contained comments
Then the compilation unit has 0 orphan comments
Then class 1 is not commented
Then class 1 has 9 total contained comments
Then method 1 in class 1 has 4 total contained comments
Then method 1 in class 1 has 0 orphan comments
Then block statement in method 1 in class 1 has 4 total contained comments
Then block statement in method 1 in class 1 has 3 orphan comments
Then method 2 in class 1 has 5 total contained comments
Then method 2 in class 1 has 0 orphan comments
Then block statement in method 2 in class 1 has 5 total contained comments
Then block statement in method 2 in class 1 has 4 orphan comments



Scenario: A Class With Line Comments in Multiple Methods is parsed by the Java Parser

Given the class:
package japa.parser.comments;

public class ClassWithLineCommentInsideBlockComment {

    /* comment to a method */
    void foo(){}

    /*// Line Comment put immediately after block comment

    //// Comment debauchery

    another orphan.
    It spans over more lines */
}
When the class is parsed by the Java parser
Then method 1 in class 1 is commented " comment to a method "
Then class 1 orphan comment 1 is "// Line Comment put immediately after block comment

                                  //// Comment debauchery

                                  another orphan.
                                  It spans over more lines "



Scenario: A Class With Line Comments on Fields is parsed by the Java Parser

Given the class:
package japa.parser.comments;

public class Issue43 {
    //Case 1
    private String field1 = null; //field1

    //Case 2
    private String field2
            = null; //field2

}
When the class is parsed by the Java parser
Then the compilation unit has 4 contained comments
Then class 1 has 4 total contained comments
Then class 1 has 1 orphan comment
Then class 1 orphan comment 1 is "Case 1"
Then field 1 in class 1 contains 0 comments
!--Then field 2 in class 1 contains 0 comments
Then field 1 in class 1 is commented "field1"
Then field 2 in class 1 is commented "Case 2"
Then variable 1 value of field 2 in class 1 is commented "field2"


Scenario: Another Class With Line Comments on Fields is parsed by the Java Parser

Given the class:
package japa.parser.comments;

public class Issue43variant {
    private String field1 = null; //field1

    private String field2
            = null; //field2

}
When the class is parsed by the Java parser
Then the compilation unit has 2 contained comments
Then class 1 has 2 total contained comments
Then field 1 in class 1 contains 0 comments
!--Then field 2 in class 1 contains 0 comments
Then field 1 in class 1 is commented "field1"
Then variable 1 value of field 2 in class 1 is commented "field2"


Scenario: A Class With Mixed Comments on Fields is parsed by the Java Parser

Given the class:
package japa.parser.javacc;
public class Teste {
    //line comment1
    int a = 0; //line comment2
    int b = 0; //line comment3
    int c = 0; /* multi-line
                * comment
                */
    int d = 0; /** multi-line
                * javadoc */
    int e = 0;
}
//final comment
When the class is parsed by the Java parser
Then the compilation unit has 6 contained comments
Then class 1 has 5 total contained comments
Then class 1 orphan comment 1 is "line comment1"
Then field 1 in class 1 is commented "line comment2"
Then field 2 in class 1 is commented "line comment3"
Then field 3 in class 1 is not commented



Scenario: Comment with a preceding line space is an orphan

Given the class:
//comment

class A {}
When the class is parsed by the Java parser
Then the compilation unit orphan comment 1 is "comment"


Scenario: Comment without a preceding line space is associated to class

Given the class:
//comment
class A {}
When the class is parsed by the Java parser
Then class 1 is commented "comment"


Scenario: Comments after Javadoc are attributed to the method if flag is active

Given the class:
class Issue40{
    @GET
    @Path("original")
    /**
    * Return the original user.
    */
    public User getOriginalUser(String userName) {
        return userService.getOriginalUser(userName);
    }
}
When the do not consider annotations as node start for code attribution is true on the Java parser
When the class is parsed by the Java parser
Then the compilation unit has 1 contained comments
Then comment 1 in compilation unit is not an orphan
Then method 1 in class 1 is commented "* Return the original user."



Scenario: Comments after Javadoc are attributed to the method if flag is not active

Given the class:
class Issue40{
    @GET
    @Path("original")
    /**
    * Return the original user.
    */
    public User getOriginalUser(String userName) {
        return userService.getOriginalUser(userName);
    }
}
When the do not consider annotations as node start for code attribution is false on the Java parser
When the class is parsed by the Java parser
Then the compilation unit has 1 contained comments
Then comment 1 in compilation unit is not an orphan
Then type of method 1 in class 1 is commented "* Return the original user."