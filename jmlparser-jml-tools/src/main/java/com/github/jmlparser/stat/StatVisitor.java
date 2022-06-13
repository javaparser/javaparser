package com.github.jmlparser.stat;

import com.github.javaparser.HasParentNode;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.jml.NodeWithJmlTags;
import com.github.javaparser.ast.jml.body.JmlClassExprDeclaration;
import com.github.javaparser.ast.jml.body.JmlFieldDeclaration;
import com.github.javaparser.ast.jml.body.JmlMethodDeclaration;
import com.github.javaparser.ast.jml.body.JmlRepresentsDeclaration;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.ast.jml.doc.*;
import com.github.javaparser.ast.jml.expr.*;
import com.github.javaparser.ast.visitor.GenericVisitorAdapter;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.jml.JmlDocSanitizer;
import lombok.Getter;

import java.util.*;

/**
 * @author Alexander Weigl
 * @version 1 (24.05.22)
 */
public class StatVisitor extends VoidVisitorAdapter<Object> {
    private final List<List<String>> keys;
    @Getter
    private final Map<List<String>, Stat> newlines = new HashMap<>();
    private final ExpressionCosts expressionCosts = new ExpressionCosts();

    public StatVisitor(List<List<String>> keys) {
        this.keys = keys;
    }

    @Override
    public void visit(JmlDocDeclaration n, Object arg) {
        report(n);
    }

    private void report(JmlDocContainer n) {
        for (List<String> keySet : keys) {
            JmlDocSanitizer doc = new JmlDocSanitizer(new TreeSet<>(keySet));
            String san = doc.asString(n.getJmlComments(), false);
            int newlines = newlines(san);
            getStatistics(keySet).addJmlNewlines(newlines);
        }
    }

    @Override
    public void visit(JmlClassExprDeclaration n, Object arg) {
        update(n, this::update);
    }

    private void update(Stat stat, JmlClassExprDeclaration n) {
        Stat.ClassStat classStat = getClassStat(stat, n);
        Stat.ClassStat.CEStat a = classStat.getClassExpressionSpecification(n.getKind().getIdentifier());
        a.numOf++;
        a.sumOfComplexity += n.getInvariant().accept(new ExpressionComplexity(), expressionCosts);
    }

    @Override
    public void visit(JmlRepresentsDeclaration n, Object arg) {
        update(n, this::update);
    }

    private void update(Stat stat, JmlRepresentsDeclaration repr) {
        Stat.ClassStat c = getClassStat(stat, repr);
        c.setNumOfRepresents(c.getNumOfRepresents());
    }

    @Override
    public void visit(JmlDocStmt n, Object arg) {
        report(n);
    }

    @Override
    public void visit(JmlDoc n, Object arg) {
    }

    @Override
    public void visit(JmlDocType n, Object arg) {
        report(n);
    }


    @Override
    public void visit(JmlMethodDeclaration n, Object arg) {
        super.visit(n, arg);
    }


    @Override
    public void visit(MethodDeclaration n, Object arg) {
        super.visit(n, arg);
    }


    @Override
    public void visit(JmlContract n, Object arg) {
        update(n, this::update);
        super.visit(n, arg);
    }


    private Stat getStatistics(List<String> keySet) {
        return newlines.computeIfAbsent(keySet, k -> new Stat());
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
    public void visit(JmlFieldDeclaration n, Object arg) {
        update(n, this::update);
    }

    interface Update<R> {
        void fn(Stat s, R node);
    }

    public <R extends NodeWithJmlTags<?>> void update(R n, Update<R> update) {
        for (List<String> keySet : keys) {
            if (equal(keySet, n.getJmlTags())) {
                Stat stat = getStatistics(keySet);
                update.fn(stat, n);
            }
        }
    }

    private void update(Stat stat, JmlContract n) {
        Stat.MethodStat mstat = getMethodStat(stat, n);
        mstat.addNumOfContracts(1);
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

    private void update(Stat stat, JmlFieldDeclaration n) {
        if (n.getDecl().hasModifier(Modifier.DefaultKeyword.JML_GHOST)) {
            getClassStat(stat, n).addNumOfGhostFields(1);
        } else if (n.getDecl().hasModifier(Modifier.DefaultKeyword.JML_MODEL)) {
            getClassStat(stat, n).addNumOfModelFields(1);
        }
    }

    private Stat.ClassStat getClassStat(Stat stat, HasParentNode<?> n) {
        Optional<TypeDeclaration> tdecl = n.findAncestor(TypeDeclaration.class);
        if (tdecl.isPresent()) {
            final String fqdn = tdecl.get().getFullyQualifiedName().get().toString();
            return stat.getClassStats(fqdn);
        }
        return null;
    }

    private Stat.MethodStat getMethodStat(Stat stat, HasParentNode<Node> n) {
        Optional<TypeDeclaration> tdecl = n.findAncestor(TypeDeclaration.class);
        Optional<MethodDeclaration> mdecl = n.findAncestor(MethodDeclaration.class);
        if (tdecl.isPresent() && mdecl.isPresent()) {
            final String fqdn = tdecl.get().getFullyQualifiedName().get().toString();
            final String sig = mdecl.get().getSignature().asString();
            return stat.getClassStats(fqdn).getMethodStats(sig);
        }
        throw new IllegalArgumentException();
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
        return arg.getCast() + n.accept(this, arg);
    }

    @Override
    public Integer visit(CharLiteralExpr n, ExpressionCosts arg) {
        return arg.getCharLiteral();
    }

    @Override
    public Integer visit(ConditionalExpr n, ExpressionCosts arg) {
        return arg.getConditional() + n.getCondition().accept(this, arg)
                + n.getThenExpr().accept(this, arg)
                + n.getElseExpr().accept(this, arg);
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
        return arg.getQuantor() + n.getVariables().size() * arg.getBinderCostsPerVariable() +
                sum(n.getExpressions(), arg);
    }

    private int sum(NodeList<Expression> n, ExpressionCosts arg) {
        return n.stream().mapToInt(it -> it.accept(this, arg)).sum();
    }

    @Override
    public Integer visit(SuperExpr n, ExpressionCosts arg) {
        return 0;
    }

    @Override
    public Integer visit(SwitchExpr n, ExpressionCosts arg) {
        return n.getSelector().accept(this, arg) +
                n.getEntries().stream().mapToInt(it -> sum(it.getLabels(), arg) + 1).sum();
    }

    @Override
    public Integer visit(PatternExpr n, ExpressionCosts arg) {
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