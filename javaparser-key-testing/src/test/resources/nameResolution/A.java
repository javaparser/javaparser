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

//? e name: self@(line 8,col 54)
//? name: this.x@(line 9,col 13) to x@(line 2,col 5)
//? type: this.x@(line 9,col 13)
