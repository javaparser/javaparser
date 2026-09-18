package qq;

public class Generic {

    public <T extends Mid> String throughTheBound(T t) {
        return t.ping();
    }

    public <U extends Sink> String instanceThroughTheBound(U u) {
        return u.inst();
    }

    public <V extends Sink> String staticThroughTheBound(V v) {
        return v.ping();
    }
}
