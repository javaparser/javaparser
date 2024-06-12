package com.github.javaparser.ast.expr;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.nodeTypes.modifiers.NodeWithFinalModifier;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.RecordPatternExprMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.Generated;

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

    public RecordPatternExpr() {
        this(new NodeList<>(), new ClassOrInterfaceType(), new NodeList<>());
    }
    @AllFieldsConstructor
    public RecordPatternExpr(final NodeList<Modifier> modifiers, final ReferenceType type, final NodeList<PatternExpr> patternList) {
        this(null, modifiers, type, patternList);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Modifier> getModifiers() {
        return modifiers;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public RecordPatternExpr setModifiers(final NodeList<Modifier> modifiers) {
        assertNotNull(modifiers);
        if (modifiers == this.modifiers) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.MODIFIERS, this.modifiers, modifiers);
        if (this.modifiers != null)
            this.modifiers.setParentNode(null);
        this.modifiers = modifiers;
        setAsParentNodeOf(modifiers);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isRecordPatternExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public RecordPatternExpr asRecordPatternExpr() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<RecordPatternExpr> toRecordPatternExpr() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifRecordPatternExpr(Consumer<RecordPatternExpr> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<PatternExpr> getPatternList() {
        return patternList;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public RecordPatternExpr setPatternList(final NodeList<PatternExpr> patternList) {
        assertNotNull(patternList);
        if (patternList == this.patternList) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.PATTERN_LIST, this.patternList, patternList);
        if (this.patternList != null)
            this.patternList.setParentNode(null);
        this.patternList = patternList;
        setAsParentNodeOf(patternList);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < modifiers.size(); i++) {
            if (modifiers.get(i) == node) {
                modifiers.remove(i);
                return true;
            }
        }
        for (int i = 0; i < patternList.size(); i++) {
            if (patternList.get(i) == node) {
                patternList.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < modifiers.size(); i++) {
            if (modifiers.get(i) == node) {
                modifiers.set(i, (Modifier) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < patternList.size(); i++) {
            if (patternList.get(i) == node) {
                patternList.set(i, (PatternExpr) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public RecordPatternExpr clone() {
        return (RecordPatternExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public RecordPatternExprMetaModel getMetaModel() {
        return JavaParserMetaModel.recordPatternExprMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public RecordPatternExpr(TokenRange tokenRange, NodeList<Modifier> modifiers, ReferenceType type, NodeList<PatternExpr> patternList) {
        super(tokenRange, type);
        setModifiers(modifiers);
        setPatternList(patternList);
        customInitialization();
    }
}
