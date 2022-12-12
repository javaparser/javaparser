import com.github.javaparser.quality.NotNull;
import com.github.javaparser.quality.Preconditions;

class A {

    public A(String a) {
    }
}

class B {

    public B(@NotNull String c) {
        super("ok");
        Preconditions.checkNotNull(c, "Parameter c can't be null.");
    }
}
