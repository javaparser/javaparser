
public class A4<T> {
    public int h() {
        int prime = 14747;
        int result = prime + this.hashCode();
        result = prime * result + this.hashCode();
        //@ reachable;
        return prime * result + this.hashCode();
    }

}

// Singleton reported that the basic block form has an
// undeclared use of a temp variable