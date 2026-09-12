package qq;

public class Outer {
    public String a() {
        return Mid.ping();
    }

    public String b() {
        return new Mid().ping();
    }

    public String c() {
        return new Sink().inst();
    }

    public String d() {
        return MidSub.ping();
    }

    public String e() {
        return Deep.ping();
    }
}
