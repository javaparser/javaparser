package com.github.javaparser.ast.expr;

import static com.github.javaparser.StaticJavaParser.parseExpression;
import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.comments.*;
import com.github.javaparser.ast.key.*;
import com.github.javaparser.ast.key.sv.*;
import java.util.function.Consumer;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

/**
 * This class exists to test the generated methods for the various Pattern expression
 * types. Actual pattern functionality is tested in the context of instanceof expressions
 * or switch entries.
 */
public class PatternExprTest {

    private static final ParserConfiguration.LanguageLevel storedLanguageLevel =
            StaticJavaParser.getParserConfiguration().getLanguageLevel();

    @BeforeAll
    public static void setLanguageLevel() {
        StaticJavaParser.getParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.BLEEDING_EDGE);
    }

    @AfterAll
    public static void resetLanguageLevel() {
        StaticJavaParser.getParserConfiguration().setLanguageLevel(storedLanguageLevel);
    }

    class TestConsumer<T> implements Consumer<T> {
        public boolean isConsumed = false;

        @Override
        public void accept(T t) {
            isConsumed = true;
        }
    }

    @Test
    public void patternGeneratedMethodsShouldWork() {
        Expression expr = parseExpression("x instanceof Foo f");

        assertTrue(expr.isInstanceOfExpr());

        InstanceOfExpr instanceOfExpr = expr.asInstanceOfExpr();

        assertTrue(instanceOfExpr.getPattern().isPresent());
        PatternExpr pattern = instanceOfExpr.getPattern().get();
        assertTrue(pattern.isComponentPatternExpr());
        assertTrue(pattern.isPatternExpr());
        assertTrue(pattern.isTypePatternExpr());
        assertInstanceOf(ComponentPatternExpr.class, pattern.asComponentPatternExpr());
        assertInstanceOf(PatternExpr.class, pattern.asComponentPatternExpr());
        assertInstanceOf(TypePatternExpr.class, pattern.asTypePatternExpr());

        assertFalse(instanceOfExpr.isComponentPatternExpr());
        assertFalse(instanceOfExpr.isTypePatternExpr());

        assertThrows(IllegalStateException.class, () -> instanceOfExpr.asComponentPatternExpr());
        assertThrows(IllegalStateException.class, () -> instanceOfExpr.asTypePatternExpr());

        TestConsumer<ComponentPatternExpr> validPattern = new TestConsumer<>();
        pattern.ifComponentPatternExpr(validPattern);
        assertTrue(validPattern.isConsumed);

        TestConsumer<TypePatternExpr> validTypePattern = new TestConsumer<>();
        pattern.ifTypePatternExpr(validTypePattern);
        assertTrue(validTypePattern.isConsumed);

        TestConsumer<ComponentPatternExpr> invalidPattern = new TestConsumer<>();
        instanceOfExpr.ifComponentPatternExpr(invalidPattern);
        assertFalse(invalidPattern.isConsumed);

        TestConsumer<TypePatternExpr> invalidTypePattern = new TestConsumer<>();
        instanceOfExpr.ifTypePatternExpr(invalidTypePattern);
        assertFalse(invalidTypePattern.isConsumed);
    }

    @Test
    public void recordPatternGeneratedMethodsShouldWork() {
        Expression expr = parseExpression("x instanceof Foo(Bar b)");

        assertTrue(expr.isInstanceOfExpr());

        InstanceOfExpr instanceOfExpr = expr.asInstanceOfExpr();

        assertTrue(instanceOfExpr.getPattern().isPresent());
        ComponentPatternExpr pattern = instanceOfExpr.getPattern().get();

        assertTrue(pattern.isRecordPatternExpr());
        assertTrue(pattern.toRecordPatternExpr().isPresent());
        RecordPatternExpr recordPattern = pattern.asRecordPatternExpr();

        NodeList<Modifier> newModifiers = new NodeList<>();
        Modifier newModifier = new Modifier();
        newModifiers.add(newModifier);
        recordPattern.setModifiers(newModifiers);
        assertEquals(newModifiers, recordPattern.getModifiers());

        recordPattern.replace(newModifier, newModifier);
        assertEquals(newModifiers, recordPattern.getModifiers());

        recordPattern.remove(newModifier);
        assertTrue(recordPattern.getModifiers().isEmpty());

        TestConsumer<RecordPatternExpr> validPattern = new TestConsumer<>();
        pattern.ifRecordPatternExpr(validPattern);
        assertTrue(validPattern.isConsumed);

        NodeList<ComponentPatternExpr> patternList = recordPattern.getPatternList();
        assertTrue(patternList.isNonEmpty());

        recordPattern.replace(patternList.get(0), patternList.get(0));
        assertTrue(patternList.isNonEmpty());

        RecordPatternExpr newRecordPattern = recordPattern.clone();
        assertEquals(recordPattern.getTypeAsString(), newRecordPattern.getTypeAsString());
    }

    @Test
    public void aSingleMatchAllPatternInRecordListShouldWork() {
        Expression expr = parseExpression("x instanceof Foo(_)");

        assertTrue(expr.isInstanceOfExpr());

        InstanceOfExpr instanceOfExpr = expr.asInstanceOfExpr();

        assertTrue(instanceOfExpr.getPattern().isPresent());
        ComponentPatternExpr pattern = instanceOfExpr.getPattern().get();

        assertTrue(pattern.isRecordPatternExpr());
        assertTrue(pattern.toRecordPatternExpr().isPresent());
        RecordPatternExpr recordPattern = pattern.asRecordPatternExpr();

        NodeList<ComponentPatternExpr> patternList = recordPattern.getPatternList();
        assertTrue(patternList.getOFirst().isPresent());

        ComponentPatternExpr childPattern = patternList.getOFirst().get();
        assertTrue(childPattern.isMatchAllPatternExpr());
    }

    @Test
    public void multipleMatchAllPatternsInRecordListShouldWork() {
        Expression expr = parseExpression("x instanceof Foo(_, Bar b, _)");

        assertTrue(expr.isInstanceOfExpr());

        InstanceOfExpr instanceOfExpr = expr.asInstanceOfExpr();

        assertTrue(instanceOfExpr.getPattern().isPresent());
        ComponentPatternExpr pattern = instanceOfExpr.getPattern().get();

        assertTrue(pattern.isRecordPatternExpr());
        assertTrue(pattern.toRecordPatternExpr().isPresent());
        RecordPatternExpr recordPattern = pattern.asRecordPatternExpr();

        NodeList<ComponentPatternExpr> patternList = recordPattern.getPatternList();
        assertEquals(3, patternList.size());

        ComponentPatternExpr firstChild = patternList.get(0);
        assertTrue(firstChild.isMatchAllPatternExpr());

        ComponentPatternExpr secondChild = patternList.get(1);
        assertTrue(secondChild.isTypePatternExpr());

        ComponentPatternExpr thirdChild = patternList.get(2);
        assertTrue(thirdChild.isMatchAllPatternExpr());
    }

    @Test
    public void anUnnamedTypePatternShouldWork() {
        Expression expr = parseExpression("x instanceof Foo _");

        assertTrue(expr.isInstanceOfExpr());

        InstanceOfExpr instanceOfExpr = expr.asInstanceOfExpr();

        assertTrue(instanceOfExpr.getPattern().isPresent());
        ComponentPatternExpr pattern = instanceOfExpr.getPattern().get();

        assertTrue(pattern.isTypePatternExpr());
        assertTrue(pattern.toTypePatternExpr().isPresent());
        TypePatternExpr typePattern = pattern.toTypePatternExpr().get();

        assertEquals("Foo", typePattern.getTypeAsString());
        assertEquals("_", typePattern.getNameAsString());
    }
}
