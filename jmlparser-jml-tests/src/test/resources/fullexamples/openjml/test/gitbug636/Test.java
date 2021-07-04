import java.nio.charset.StandardCharsets;
public class Test {
    //@ public normal_behavior
    //@   requires new String(s, cs) != null;
    public void m(String s, StandardCharsets cs) {
    }
}