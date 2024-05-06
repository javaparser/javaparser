package com.github.javaparser.ast.expr;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.nodeTypes.modifiers.NodeWithFinalModifier;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.regex.Pattern;

/**
 * <h1>Record Patterns</h1>
 * Record patterns were officially added in Java 21 to allow the deconstruction of
 * record values and provide convenient access to inner fields through pattern matching.
 * <br>
 * <br>
 * <h3>JDK 21 Grammar</h3>
 * <pre><code>Pattern
 *     TypePattern
 *     RecordPattern
 *
 * RecordPattern:
 *     ReferenceType ( [PatternList] )
 *
 * PatternList
 *     Pattern {, Pattern }
 * </code></pre>
 *
 * <h3>Example</h3>
 * Example taken from <a href="https://openjdk.org/jeps/440">JEP440: RecordPatterns</a>
 * <pre><code>
 *  record Pair(Object x, Object y) {}
 *
 * Pair p = new Pair(42, 42);
 *
 * if (p instanceof Pair(String s, String t)) {
 *     System.out.println(s + ", " + t);
 * } else {
 *     System.out.println("Not a pair of strings");
 * }
 * </code></pre>
 *
 * @see com.github.javaparser.ast.expr.PatternExpr
 * @see com.github.javaparser.ast.expr.TypePatternExpr
 * @see <a href="https://openjdk.org/jeps/440">JEP 440: Record Patterns</a>
 */
public class RecordPatternExpr extends PatternExpr implements NodeWithFinalModifier<RecordPatternExpr> {

    private NodeList<Modifier> modifiers;

    private NodeList<PatternExpr> patternList;

    @AllFieldsConstructor
    public RecordPatternExpr(final NodeList<Modifier> modifiers, final ReferenceType type, final NodeList<PatternExpr> patternList) {
        super(type);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return null;
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {

    }

    @Override
    public NodeList<Modifier> getModifiers() {
        return null;
    }

    @Override
    public RecordPatternExpr setModifiers(NodeList<Modifier> modifiers) {
        return null;
    }
}
