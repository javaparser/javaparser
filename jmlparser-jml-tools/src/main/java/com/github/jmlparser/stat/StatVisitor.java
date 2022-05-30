package com.github.jmlparser.stat;

import com.github.javaparser.HasParentNode;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.jml.body.JmlFieldDeclaration;
import com.github.javaparser.ast.jml.body.JmlMethodDeclaration;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.ast.jml.doc.*;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.jml.JmlDocSanitizer;
import lombok.Getter;

import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (24.05.22)
 */
public class StatVisitor extends VoidVisitorAdapter<Object> {
    private final List<List<String>> keys;
    @Getter
    private final Map<List<String>, Stat> newlines = new HashMap<>();

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
        for (List<String> keySet : keys) {
            String[] tags = toArray(n.getJmlTags());
            if (JmlDocSanitizer.isActiveJmlSpec(keySet, tags)) {
                Stat stat = getStatistics(keySet);
                update(stat, n);
            }
        }
        super.visit(n, arg);
    }

    private void update(Stat stat, JmlContract n) {
        Stat.MethodStat mstat = getMethodStat(stat, n);
        mstat.addNumOfContracts(1);
    }

    @Override
    public void visit(JmlFieldDeclaration n, Object arg) {
        for (List<String> keySet : keys) {
            if (equal(keySet, n.getJmlTags())) {
                Stat stat = getStatistics(keySet);
                update(stat, n);
            }
        }
    }

    private boolean equal(List<String> keySet, NodeList<SimpleName> jmlTags) {
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

    private List<String> toList(NodeList<SimpleName> jmlTags) {
        return jmlTags.stream().map(it -> it.getIdentifier()).collect(Collectors.toList());
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
        return null;
    }

    private String[] toArray(NodeList<SimpleName> jmlTags) {
        final String[] ret = new String[jmlTags.size()];
        int i = 0;
        for (SimpleName jmlTag : jmlTags) {
            ret[i++] = jmlTag.getIdentifier();
        }
        return ret;
    }
}
