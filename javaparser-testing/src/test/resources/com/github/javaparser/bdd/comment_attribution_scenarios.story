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
Then class 1 orphan comment 1 is "Comment2"


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


Scenario: A Class With Line Comments is processed by the Java Parser

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
When the class is parsed by the Java parser
Then the compilation is commented "CompilationUnitComment"
Then class 1 is not commented
Then class 1 has 6 total contained comments
Then class 1 orphan comment 1 is " final comment"
Then field 1 in class 1 is commented " line comment"
Then field 1 in class 1 contains 0 comments
Then field 2 in class 1 is commented " another line comment"
Then field 2 in class 1 contains 0 comments
Then field 3 in class 1 is commented " line comment"
Then field 3 in class 1 contains 0 comments
Then field 4 in class 1 is commented " multi-line comment"
Then field 4 in class 1 contains 0 comments
Then field 5 in class 1 is commented " * multi-line"
Then field 5 in class 1 contains 0 comments


Scenario: A class with only an orphan comment is processed by the Java Parser

Given the class:
class A {
    // orphan comment"
}
When the class is parsed by the Java parser
Then the compilation unit has 1 contained comments
Then comment 1 in compilation unit is an orphan
Then comment 1 in compilation unit parent is ClassOrInterfaceDeclaration



Scenario: A class with only a class comment is processed by the Java Parser

Given the class:
/* Comment of the class */
class A {
}
When the class is parsed by the Java parser
Then the compilation unit has 1 contained comments
Then comment 1 in compilation unit is not an orphan
Then comment 1 in compilation unit commented node is ClassOrInterfaceDeclaration



Scenario: A Class With two comments at class level is processed by the Java Parser

Given the class:
/* Orphan comment */
/* Comment of the class */
class A {
}
When the class is parsed by the Java parser
Then the compilation unit has 2 contained comments
Then comment 1 in compilation unit is an orphan
Then the compilation unit orphan comment 1 is "Orphan comment"
Then comment 2 in compilation unit is not an orphan
Then comment 2 in compilation unit commented node is ClassOrInterfaceDeclaration


Scenario: A Class has a comment associated to a field when processed by the Java Parser

Given the class:
class A {
    int a = 0; // comment associated to the field
}
When the class is parsed by the Java parser
Then the compilation unit has 1 contained comments
Then comment 1 in compilation unit is not an orphan
Then comment 1 in compilation unit commented node is FieldDeclaration


Scenario: A Class has a comment associated to a the literal when processed by the Java Parser

Given the class:
class A {
    int a
        = 0; // comment associated to the field
}
When the class is parsed by the Java parser
Then the compilation unit has 1 contained comments
Then comment 1 in compilation unit is not an orphan
Then comment 1 in compilation unit commented node is IntegerLiteralExpr



Scenario: A Class with two line comment within a method when processed by the Java Parser

Given the class:
class A {
    void foo() {
        // a comment
        int b; // another comment
    }
}
When the class is parsed by the Java parser
Then the compilation unit has 2 contained comments
Then comment 1 in compilation unit is an orphan
Then comment 1 in compilation unit is "a comment"
Then comment 2 in compilation unit is not an orphan
Then comment 2 in compilation unit is "another comment"
Then comment 2 in compilation unit commented node is ExpressionStmt


Scenario: A Class with an inline comment inside a block comment is parsed by the Java Parser

Given the class:
class A {
    /* A block comment that
    // Contains a line comment
    */
    public static void main(String args[]) {
    }
}
When the class is parsed by the Java parser
Then the compilation unit has 1 contained comments
Then comment 1 in compilation unit is "A block comment that // Contains a line comment"


Scenario: A Class with an inline comment inbetween annotation a method declaration is parsed Java Parser

Given the class:
class A {
    @Override
    // Returns number of vowels in a name
    public int countVowels(String name) {
    }
}
When the class is parsed by the Java parser
Then the compilation unit has 1 contained comments
Then comment 1 in compilation unit commented node is PrimitiveType

Scenario: We print correctly two consecutive line-comments in a class
 
Given the class:
class A {
  // foo
  // bar
  void aMethod(){}
}
When the class is parsed by the Java parser
Then it is printed as:
class A {

    // foo
    // bar
    void aMethod() {
    }
}

Scenario: We print correctly two consecutive line-comments in a method

Given the class:
class A {
  void aMethod(){
     // foo
     // bar
     int a;
  }
}
When the class is parsed by the Java parser
Then it is printed as:
class A {

    void aMethod() {
        // foo
        // bar
        int a;
    }
}

Scenario: We print correctly orphan comments in a for loop
Given the class:
class A {
    public static List calcularResultadoFinal(List avaliacoes) throws SQLException, ClassNotFoundException{
        for(Avaliacao avaliacao: avaliacoes){
            // if(avaliacao.obterAprovacao()){
            // avaliacao.setResultadoFinal("Aprovado");
            // }else{
            // avaliacao.setResultadoFinal("Reprovado");
            // }
            avaliacao.setEmAberto(false);
            avaliacao.editar();
        }
        return avaliacoes;
    }
}
When the class is parsed by the Java parser
Then it is printed as:
class A {

    public static List calcularResultadoFinal(List avaliacoes) throws SQLException, ClassNotFoundException {
        for (Avaliacao avaliacao : avaliacoes) {
            // if(avaliacao.obterAprovacao()){
            // avaliacao.setResultadoFinal("Aprovado");
            // }else{
            // avaliacao.setResultadoFinal("Reprovado");
            // }
            avaliacao.setEmAberto(false);
            avaliacao.editar();
        }
        return avaliacoes;
    }
}
