package qq;

import java.util.function.Supplier;

public class Outer {

    public String qualifiedByType() {
        return Mid.ping();
    }

    public String qualifiedByInstance() {
        return new Mid().ping();
    }

    public Supplier<String> methodReference() {
        return Mid::ping;
    }

    public String instanceMethodOfTheDeclaringType() {
        return new Sink().inst();
    }

    public String staticMethodOfTheDeclaringType() {
        return Sink.ping();
    }
}
