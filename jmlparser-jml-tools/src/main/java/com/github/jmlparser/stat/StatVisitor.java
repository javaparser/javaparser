package com.github.jmlparser.stat;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.jml.NodeWithJmlTags;
import com.github.javaparser.ast.jml.body.JmlClassExprDeclaration;
import com.github.javaparser.ast.jml.body.JmlFieldDeclaration;
import com.github.javaparser.ast.jml.body.JmlMethodDeclaration;
import com.github.javaparser.ast.jml.body.JmlRepresentsDeclaration;
import com.github.javaparser.ast.jml.clauses.*;
import com.github.javaparser.ast.jml.doc.*;
import com.github.javaparser.ast.jml.expr.*;
import com.github.javaparser.ast.jml.stmt.*;
import com.github.javaparser.ast.modules.ModuleDeclaration;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.stmt.LocalClassDeclarationStmt;
import com.github.javaparser.ast.visitor.GenericVisitorAdapter;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.jml.JmlDocSanitizer;
import lombok.Getter;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import java.util.*;


/**
 * @author Alexander Weigl
 * @version 1 (24.05.22)
 */
public class StatVisitor extends VoidVisitorAdapter<Element> {
    private final List<String> keys;
    @Getter
    private final ExpressionCosts expressionCosts;
    private final Document xmlDocument;

    public StatVisitor(Document xmlDocument, List<String> keys, ExpressionCosts expressionCosts) {
        this.keys = keys;
        this.expressionCosts = expressionCosts;
        this.xmlDocument = xmlDocument;
    }

    //region Java Stuff
    @Override
    public void visit(CompilationUnit n, Element arg) {
        super.visit(n, newJavaContext(arg, n.getClass().getSimpleName(), n.getStorage().get().getFileName()));
    }

    @Override
    public void visit(MethodDeclaration n, Element arg) {
        arg = newJavaContext(arg, n.getClass().getSimpleName(),
                n.getDeclarationAsString(false, false, true));
        super.visit(n, arg);
    }

    @Override
    public void visit(ClassOrInterfaceDeclaration n, Element arg) {
        arg = newJavaContext(arg, n);
        super.visit(n, arg);
    }

    @Override
    public void visit(ConstructorDeclaration n, Element arg) {
        arg = newJavaContext(arg, n.getClass().getSimpleName(),
                n.getDeclarationAsString(false, false, true));
        super.visit(n, arg);
    }

    @Override
    public void visit(AnnotationDeclaration n, Element arg) {
        arg = newJavaContext(arg, n);
        super.visit(n, arg);
    }

    @Override
    public void visit(AnnotationMemberDeclaration n, Element arg) {
        super.visit(n, arg);
    }

    @Override
    public void visit(EnumDeclaration n, Element arg) {
        super.visit(n, newJavaContext(arg, n));
    }

    @Override
    public void visit(LocalClassDeclarationStmt n, Element arg) {
        super.visit(n, arg);
    }

    @Override
    public void visit(ModuleDeclaration n, Element arg) {
        super.visit(n, newJavaContext(arg, n));
    }

    private Element newJavaContext(Element parent, NodeWithName<?> node) {
        return newJavaContext(parent, node.getClass().getSimpleName(), node.getNameAsString());
    }

    private Element newJavaContext(Element parent, NodeWithSimpleName<?> node) {
        return newJavaContext(parent, node.getClass().getSimpleName(), node.getNameAsString());
    }

    private Element newJavaContext(Element parent, String simpleName, String name) {
        Element e = xmlDocument.createElement(simpleName);
        e.setAttribute("name", name);
        parent.appendChild(e);
        return e;
    }
    //endregion

    //region plain text reporting
    @Override
    public void visit(JmlDocDeclaration n, Element arg) {
        reportPlainText(n, arg);
    }

    @Override
    public void visit(JmlDoc n, Element arg) {
    }

    public void visit(JmlDocStmt n, Element arg) {
        reportPlainText(n, arg);
    }

    @Override
    public void visit(JmlDocType n, Element arg) {
        reportPlainText(n, arg);
    }

    private void reportPlainText(JmlDocContainer n, Element arg) {
        JmlDocSanitizer doc = new JmlDocSanitizer(new TreeSet<>(keys));
        String san = doc.asString(n.getJmlComments(), false);
        int newlines = newlines(san);
        Element e = xmlDocument.createElement("jml-comment");
        arg.appendChild(e);
        e.setAttribute("newlines", "" + newlines);
        e.setAttribute("type", n.getClass().getSimpleName());
        e.setAttribute("chars", "" + san.length());
    }
    //endregion

    @Override
    public void visit(JmlClassExprDeclaration n, Element arg) {
        if (active(n)) {
            Element e = newElement(arg, n.getKind().getIdentifier());
            Element expr = getExpressionStat(n.getInvariant());
            e.appendChild(expr);
            if (n.getName().isPresent()) {
                e.setAttribute("name", n.getName().get().asString());
            }
            setModifierAsAttributes(n, e);
        }
    }

    private void setModifierAsAttributes(NodeWithModifiers<?> n, Element e) {
        for (Modifier modifier : n.getModifiers()) {
            e.setAttribute("has" + modifier.getKeyword().asString(), "true");
        }
    }

    private Element getExpressionStat(Expression expr) {
        Element e = xmlDocument.createElement("expr");
        Integer costs = expr.accept(new ExpressionComplexity(), expressionCosts);
        int numOfVariables = numberOfVariables(expr);
        int length = lengthOf(expr);
        e.setAttribute("complexity", "" + costs);
        e.setAttribute("numOfVariables", "" + numOfVariables);
        e.setAttribute("length", "" + length);

        Map<Class<?>, Integer> map = count(expr);
        map.forEach((k, v) -> e.setAttribute(k.getSimpleName(), "" + v));
        return e;
    }

    private int lengthOf(Expression expr) {
        return expr.toString().length();
    }

    private int numberOfVariables(Expression expr) {
        int sum = 0;
        for (Node childNode : expr.getChildNodes()) {
            if (childNode instanceof NameExpr) sum++;
            else if (childNode instanceof Expression && !childNode.getChildNodes().isEmpty()) {
                sum += numberOfVariables((Expression) childNode);
            }
        }
        return sum;
    }

    private Element newElement(Element parent, String tag) {
        Element e = xmlDocument.createElement(tag);
        parent.appendChild(e);
        return e;
    }

    private boolean active(NodeWithJmlTags<?> n) {
        return equal(keys, n.getJmlTags());
    }


    @Override
    public void visit(JmlRepresentsDeclaration n, Element arg) {
        if (active(n)) {
            Element a = newElement(arg, "represents");
            a.setAttribute("name", n.getNameAsString());
            setModifierAsAttributes(n, a);
        }
    }

    @Override
    public void visit(JmlMethodDeclaration n, Element arg) {
        if (active(n)) {
            arg = newJavaContext(arg, n.getClass().getSimpleName(), n.getMethodDeclaration().getNameAsString());
            setModifierAsAttributes(n.getMethodDeclaration(), arg);
            super.visit(n.getMethodDeclaration(), arg);
        }
    }


    @Override
    public void visit(JmlContract n, Element arg) {
        if (active(n)) {
            String name = "contract_" + n.getRange().get().begin.line;
            if (n.getName().isPresent()) {
                name = n.getName().get().getIdentifier();
            }
            Element e = newJavaContext(arg, n.getClass().getSimpleName(), name);
            e.setAttribute("type", n.getType().toString());
            setModifierAsAttributes(n, e);
            e.setAttribute("behavior", "" + n.getBehavior());
            super.visit(n, e);
        }
    }

    @Override
    public void visit(JmlExpressionStmt n, Element arg) {
        if (active(n)) {
            Element e = newElement(arg, n.getKind().jmlSymbol());
            e.appendChild(getExpressionStat(n.getExpression()));
        }
    }

    @Override
    public void visit(JmlUnreachableStmt n, Element arg) {
        if (active(n)) {
            Element e = newElement(arg, "jml-unreachable");
        }
    }

    @Override
    public void visit(JmlBeginStmt n, Element arg) {
        if (active(n)) {
            newElement(arg, "jml-begin");
        }
    }

    @Override
    public void visit(JmlEndStmt n, Element arg) {
        if (active(n)) {
            newElement(arg, "jml-end");
        }
    }

    @Override
    public void visit(JmlGhostStmt n, Element arg) {
        if (active(n)) {
            Element e = newElement(arg, "jml-ghost");
            e.setAttribute("statements", "");
            super.visit(n, e);
        }
    }


    @Override
    public void visit(JmlLabelStmt n, Element arg) {
        if (active(n)) {
            newElement(arg, "jml-label");
        }
    }

    @Override
    public void visit(JmlSimpleExprClause n, Element arg) {
        Element e = newElement(arg, n.getKind().jmlSymbol);
        e.appendChild(getExpressionStat(n.getExpression()));
    }

    @Override
    public void visit(JmlSignalsClause n, Element arg) {
        newElement(arg, n.getKind().jmlSymbol);
    }

    @Override
    public void visit(JmlSignalsOnlyClause n, Element arg) {
        Element e = newElement(arg, n.getKind().jmlSymbol);
        e.setAttribute("numOfTypes", "" + n.getTypes().size());
    }

    @Override
    public void visit(JmlOldClause n, Element arg) {
        Element e = newElement(arg, n.getKind().jmlSymbol);
        e.setAttribute("numOfDecls", "" + n.getDeclarations().getVariables().size());
    }

    @Override
    public void visit(JmlAccessibleClause n, Element arg) {
        super.visit(n, arg);
    }

    @Override
    public void visit(JmlMultiExprClause n, Element arg) {
        Element e = newElement(arg, n.getKind().jmlSymbol);
        for (Expression expression : n.getExpressions()) {
            e.appendChild(getExpressionStat(expression));
        }
    }

    @Override
    public void visit(JmlCallableClause n, Element arg) {
        Element e = newElement(arg, n.getKind().jmlSymbol);
    }

    @Override
    public void visit(JmlCapturesClause n, Element arg) {
        Element e = newElement(arg, n.getKind().jmlSymbol);
    }

    @Override
    public void visit(JmlForallClause n, Element arg) {
        Element e = newElement(arg, n.getKind().jmlSymbol);
        e.setAttribute("numVars", "" + n.getVariables().size());
    }

    @Override
    public void visit(JmlRefiningStmt n, Element arg) {
        if (active(n)) {
            Element e = newElement(arg, "jml-refining");
        }
    }

    @Override
    public void visit(JmlClauseIf n, Element arg) {
        super.visit(n, arg);
    }

    private static int newlines(String text) {
        char[] chars = text.toCharArray();
        int n = 0;
        for (char aChar : chars) {
            if (aChar == '\n') {
                n++;
            }
        }
        return n;
    }


    @Override
    public void visit(JmlFieldDeclaration n, Element arg) {
        update(n, this::update);
    }

    interface Update<R> {
        void fn(Element parent, R node);
    }

    public <R extends NodeWithJmlTags<?>> void update(R n, Update<R> update) {
    }

    private static boolean equal(List<String> keySet, NodeList<SimpleName> jmlTags) {
        if (keySet.size() != jmlTags.size()) {
            return false;
        }

        for (int i = 0; i < keySet.size(); i++) {
            if (!keySet.get(i).equals(jmlTags.get(i).getIdentifier())) {
                return false;
            }
        }
        return true;
    }

    private void update(Element parent, JmlFieldDeclaration n) {
        /*if (n.getDecl().hasModifier(Modifier.DefaultKeyword.JML_GHOST)) {
            getClassStat(stat, n).addNumOfGhostFields(1);
        } else if (n.getDecl().hasModifier(Modifier.DefaultKeyword.JML_MODEL)) {
            getClassStat(stat, n).addNumOfModelFields(1);
        }
         */
    }


    private Map<Class<?>, Integer> count(Expression e) {
        final Map<Class<?>, Integer> occCounter = new HashMap<>();
        ArrayDeque<Node> q = new ArrayDeque<>();
        q.add(e);

        while (!q.isEmpty()) {
            Node n = q.pop();
            occCounter.compute(n.getClass(), (k, i) -> i == null ? 1 : i + 1);
            for (Node childNode : n.getChildNodes()) {
                if (childNode instanceof Expression) {
                    q.add(childNode);
                }
            }
        }
        return occCounter;
    }

}

class ExpressionComplexity extends GenericVisitorAdapter<Integer, ExpressionCosts> {
    @Override
    public Integer visit(ArrayAccessExpr n, ExpressionCosts arg) {
        return super.visit(n, arg);
    }

    @Override
    public Integer visit(ArrayCreationExpr n, ExpressionCosts arg) {
        return super.visit(n, arg);
    }

    @Override
    public Integer visit(ArrayInitializerExpr n, ExpressionCosts arg) {
        return super.visit(n, arg);
    }

    @Override
    public Integer visit(AssignExpr n, ExpressionCosts arg) {
        return arg.getAssign() + n.getTarget().accept(this, arg) + n.getValue().accept(this, arg);
    }

    @Override
    public Integer visit(BinaryExpr n, ExpressionCosts arg) {
        //TODO distinguish by operator
        return arg.getMinus() + n.getLeft().accept(this, arg) + n.getRight().accept(this, arg);
    }

    @Override
    public Integer visit(UnaryExpr n, ExpressionCosts arg) {
        return super.visit(n, arg);
    }

    @Override
    public Integer visit(LambdaExpr n, ExpressionCosts arg) {
        return super.visit(n, arg);
    }

    @Override
    public Integer visit(CastExpr n, ExpressionCosts arg) {
        return arg.getCast() + n.getExpression().accept(this, arg);
    }

    @Override
    public Integer visit(CharLiteralExpr n, ExpressionCosts arg) {
        return arg.getCharLiteral();
    }

    @Override
    public Integer visit(ConditionalExpr n, ExpressionCosts arg) {
        return arg.getConditional() + n.getCondition().accept(this, arg) + n.getThenExpr().accept(this, arg) + n.getElseExpr().accept(this, arg);
    }

    @Override
    public Integer visit(EnclosedExpr n, ExpressionCosts arg) {
        return n.getInner().accept(this, arg);
    }

    @Override
    public Integer visit(IntegerLiteralExpr n, ExpressionCosts arg) {
        return arg.getIntegerLiteral();
    }

    @Override
    public Integer visit(LongLiteralExpr n, ExpressionCosts arg) {
        return arg.getLongLiteral();
    }

    @Override
    public Integer visit(MethodCallExpr n, ExpressionCosts arg) {
        return arg.getMethodCall() + sum(n.getArguments(), arg);
    }

    @Override
    public Integer visit(NameExpr n, ExpressionCosts arg) {
        return arg.getName();
    }

    @Override
    public Integer visit(NullLiteralExpr n, ExpressionCosts arg) {
        return arg.getNullLiteral();
    }

    @Override
    public Integer visit(JmlQuantifiedExpr n, ExpressionCosts arg) {
        return arg.getQuantor() + n.getVariables().size() * arg.getBinderCostsPerVariable() + sum(n.getExpressions(), arg);
    }

    private int sum(NodeList<Expression> n, ExpressionCosts arg) {
        return n.stream().mapToInt(it ->
                Objects.requireNonNull(it.accept(this, arg), it.getClass().getSimpleName())).sum();
    }

    @Override
    public Integer visit(JmlTypeExpr n, ExpressionCosts arg) {
        return 1;
    }

    @Override
    public Integer visit(SuperExpr n, ExpressionCosts arg) {
        return 0;
    }

    @Override
    public Integer visit(SwitchExpr n, ExpressionCosts arg) {
        return n.getSelector().accept(this, arg) + n.getEntries().stream().mapToInt(it -> sum(it.getLabels(), arg) + 1).sum();
    }

    @Override
    public Integer visit(PatternExpr n, ExpressionCosts arg) {
        return 0;
    }

    @Override
    public Integer visit(BooleanLiteralExpr n, ExpressionCosts arg) {
        return 0;
    }

    @Override
    public Integer visit(InstanceOfExpr n, ExpressionCosts arg) {
        return arg.get_instanceof() + n.getExpression().accept(this, arg);
    }

    @Override
    public Integer visit(JmlLabelExpr n, ExpressionCosts arg) {
        return super.visit(n, arg);
    }

    @Override
    public Integer visit(JmlLetExpr n, ExpressionCosts arg) {
        return arg.getLet() + arg.getBinderCostsPerVariable() * n.getVariables().getVariables().size();
    }

    @Override
    public Integer visit(JmlMultiCompareExpr n, ExpressionCosts arg) {
        return arg.getCompare() * n.getOperators().size();
    }
}