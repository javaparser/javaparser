Scenario: Test declaration as String for constructor on parsed class

Given a CompilationUnit
When the following source is parsed:
class ClassWithAConstructor {
    protected ClassWithAConstructor(int a, String b) throws This, AndThat, AndWhatElse {
    }
}
Then constructor 1 in class 1 declaration as a String is "protected ClassWithAConstructor(int a, String b) throws This, AndThat, AndWhatElse"


Scenario: Test declaration as String exclusing modifiers and throws for constructor on parsed class

Given a CompilationUnit
When the following source is parsed:
class ClassWithAConstructor {
    protected ClassWithAConstructor(int a, String b) throws This, AndThat, AndWhatElse {
    }
}
Then constructor 1 in class 1 declaration short form as a String is "ClassWithAConstructor(int a, String b)"


Scenario: Test declaration as String exclusing modifiers and throws for method on parsed class

Given a CompilationUnit
When the following source is parsed:
class ClassWithAMethod {
    /*comment1*/
    final protected /*comment2*/ native List<String> /*comment2*/ aMethod(int a, String b) throws /*comment3*/ This, AndThat, AndWhatElse {

    }
}
Then method 1 in class 1 declaration as a String is "protected final native List<String> aMethod(int a, String b) throws This, AndThat, AndWhatElse"

Scenario: Test declaration as String exclusing modifiers and throws for method on parsed class

Given a CompilationUnit
When the following source is parsed:
class ClassWithAMethod {
    /*comment1*/
    final protected /*comment2*/ native List<String> /*comment2*/ aMethod(int a, String b) throws /*comment3*/ This, AndThat, AndWhatElse {

    }
}
Then method 1 in class 1 declaration as a String short form is "List<String> aMethod(int a, String b)"