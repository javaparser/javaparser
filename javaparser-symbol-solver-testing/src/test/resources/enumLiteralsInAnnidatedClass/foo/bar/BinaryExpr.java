package foo.bar;

public interface BinaryExpr {

    enum Operator {
        OR("||"),
        AND("&&");

        Operator(String codeRepresentation) { }
    }
}
