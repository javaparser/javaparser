public class A {
    private int x;
    void bar() {}
}

class B {
    void foo() {
        method-frame(result->a, source=bar()@A, this=self) : {
            this.x = 0;
        }
    }
}

//? name: self@(line 8,col 54) refers to self@(line 8,col 54) in A.java
//? name: this.x@(line 9,col 13) refers to x@(line 2,col 5) in A.java
//? type: self@(line 8,col 54) refers to ReferenceType{A, typeParametersMap=TypeParametersMap{nameToValue={}}}
//? type: this.x@(line 9,col 13) refers to PrimitiveTypeUsage{name='int'}