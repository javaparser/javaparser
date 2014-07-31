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
Then the total number of line comments is 4
Then line comment 1 is " first comment"
Then line comment 2 is " second comment"
Then line comment 3 is " third comment"
Then line comment 4 is " fourth comment"
Then the line comments have the following positions:
|beginLine|beginColumn|endLine|endColumn|
|6|9|6|25|
|7|18|7|35|
|8|9|8|25|
|9|9|9|26|

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
Then the total number of line comments is 5
Then block comment 1 is " comment which is not attributed to the class, it floats around as an orphan "
Then block comment 2 is " comment to a class "
Then block comment 3 is " comment to a method "
Then block comment 4 is " comment put randomly in class:    another orphan.    It spans over more lines "
Then block comment 5 is " a comment lost inside a compilation unit. It is orphan, I am sure you got this one  "
Then the block comments have the following positions:
|beginLine|beginColumn|endLine|endColumn|
|3|1|3|82|
|4|1|4|25|
|7|5|7|30|
|10|5|13|32|
|17|1|17|89|
