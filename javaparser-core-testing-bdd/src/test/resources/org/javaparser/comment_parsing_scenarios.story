Scenario: A Class With Line Comments is processed by the Comments Parser

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
When the class is parsed by the comment parser
Then the total number of comments is 4
Then line comment 1 is " first comment"
Then line comment 2 is " second comment"
Then line comment 3 is " third comment"
Then line comment 4 is " fourth comment"
Then the line comments have the following positions:
|beginLine|beginColumn|endLine|endColumn|
|6|9|6|24|
|7|18|7|34|
|8|9|8|24|
|9|9|9|25|

Scenario: A Class With Block Comments is processed by the Comments Parser

Given the class:
package japa.parser.comments;

/* comment which is not attributed to the class, it floats around as an orphan */
/* comment to a class */
public class ClassWithBlockComments {

    /* comment to a method */
    void foo(){};

    /* comment put randomly in class:

    another orphan.
    It spans over more lines */

}

/* a comment lost inside a compilation unit. It is orphan, I am sure you got this one */
When the class is parsed by the comment parser
Then the total number of comments is 5
Then block comment 1 is " comment which is not attributed to the class, it floats around as an orphan "
Then block comment 2 is " comment to a class "
Then block comment 3 is " comment to a method "
Then block comment 4 is " comment put randomly in class:    another orphan.    It spans over more lines "
Then block comment 5 is " a comment lost inside a compilation unit. It is orphan, I am sure you got this one  "
Then the block comments have the following positions:
|beginLine|beginColumn|endLine|endColumn|
|3|1|3|81|
|4|1|4|24|
|7|5|7|29|
|10|5|13|31|
|17|1|17|88|


Scenario: A Class With Javadoc Comments is processed by the Comments Parser

Given the class:
package japa.parser.comments;

/** a proper javadoc comment */
public class ClassWithJavadocComments {

    void foo(){};


}
/** a floating javadoc comment */
When the class is parsed by the comment parser
Then the total number of comments is 2
Then Javadoc comment 1 is " a proper javadoc comment "
Then Javadoc comment 2 is " a floating javadoc comment "
Then the Javadoc comments have the following positions:
|beginLine|beginColumn|endLine|endColumn|
|3|1|3|31|
|10|1|10|33|



Scenario: A Class With Orphan Comments is processed by the Comments Parser

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
When the class is parsed by the comment parser
Then the total number of comments is 6
Then line comment 1 is "a first comment floating in the class"
Then line comment 2 is "comment associated to the method"
Then line comment 3 is "a second comment floating in the class"
Then block comment 1 is "comment floating inside the method"
Then Javadoc comment 1 is "Javadoc associated with the class"


Scenario: A Class With Orphan Comments is processed by the Comments Parser

Given the class:
/*CompilationUnitComment*/
package japa.parser.comments;

public class ClassWithMixedStyleComments {
    // line comment
    int a = 0;
    // another line comment
    int b = 0;
    // line comment
    int c = 0;
    /* multi-line
       comment
    */
    int d = 0;
    /**
     * multi-line
     */
    int e = 0;
    // final comment
}
When the class is parsed by the comment parser
Then the total number of comments is 7
Then the line comments have the following positions:
|beginLine|beginColumn|endLine|endColumn|
|5|5|5|19|
|7|5|7|27|
|9|5|9|19|
|19|5|19|20|
Then the block comments have the following positions:
|beginLine|beginColumn|endLine|endColumn|
|1|1|1|26|
|11|5|13|6|
Then the Javadoc comments have the following positions:
|beginLine|beginColumn|endLine|endColumn|
|15|5|17|7|

Scenario: A method containing two consecutive line comments is parsed correctly

Given the class:
class A {
  void aMethod(){
     // foo
     // bar
     int a;
  }
}
When the class is parsed by the comment parser
Then the total number of comments is 2
Then line comment 1 is " foo"
Then line comment 2 is " bar"

Scenario: Comments from a file with an non-UTF-8 encoding are parsed correctly

When read sample "ClassInLatin1" using encoding "ISO-8859-1"
Then the total number of comments is 3
Then line comment 2 is " A l'émej in piasì che sent dësgust."

Scenario: Should not recognize /*/ as a comment

Given the class:
/*/
class Foo {}
When the class is parsed by the comment parser
Then the total number of comments is 0

Given the class:
/*/
class Foo {}
Then the Java parser cannot parse it because of an error

Scenario: Should recognize /*/ inside a block comment

Given the class:
/* Foo /*/
When the class is parsed by the comment parser
Then the total number of comments is 1
Then block comment 1 is " Foo /"

Scenario: A Class With Character Literal is processed by the Comments Parser
Given the class:
class A {
    /** comment1 */
    private char c = '"';
    /** comment2 */
    private String d;
}
When the class is parsed by the comment parser
Then the total number of comments is 2
Then Javadoc comment 1 is "comment1"
Then Javadoc comment 2 is "comment2"

Scenario: Double slash in string does not mess up comments parsing
Given the class:
public class b {

    public void m1() {
        String s = "\\";
    }

    /**
     * Comment
    */
    public void m2() {
        return;
    }
}
When the class is parsed by the comment parser
Then the total number of comments is 1

Scenario: Triple slash in string does not mess up comments parsing
Given the class:
public class b {

    public void m1() {
        String s = "\\\" // still in string";
    }

    /**
     * Comment
    */
    public void m2() {
        return;
    }
}
When the class is parsed by the comment parser
Then the total number of comments is 1

Scenario: Four slashes in string does not mess up comments parsing
Given the class:
public class b {

    public void m1() {
        String s = "\\\\" // out of the string";
        ;
    }

    /**
     * Comment
    */
    public void m2() {
        return;
    }
}
When the class is parsed by the comment parser
Then the total number of comments is 2

Scenario: Five slashes in string does not mess up comments parsing
Given the class:
public class b {

    public void m1() {
        String s = "\\\\\" // still in string";
        ;
    }

    /**
     * Comment
    */
    public void m2() {
        return;
    }
}
When the class is parsed by the comment parser
Then the total number of comments is 1
