package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ASTParserConstants;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import com.github.javaparser.printer.concretesyntaxmodel.*;
import org.junit.Test;

import java.util.*;

import static org.junit.Assert.assertEquals;

public class CalculatingDifferentialTokensTest extends AbstractLexicalPreservingTest {

    @Test
    public void diffInASimpleMethodRemovingParameterOneFromMethodWithTwoParameters() {
        String code = "class A { void foo(char p1, int p2) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);

        List<Integer> tokens = findCompulsoryTokens(m);
        tokens.forEach(t -> System.out.println(ASTParserConstants.tokenImage[t]));

        m.getParameters().remove(0);

        System.out.println("AFTER");
        tokens = findCompulsoryTokens(m);
        tokens.forEach(t -> System.out.println(ASTParserConstants.tokenImage[t]));

        //assertEquals("void foo(int p2) {}", lpp.print(m));
    }

    private List<Integer> findCompulsoryTokens(Node node) {
        CsmElement csmElement = ConcreteSyntaxModel.forClass(node.getClass());
        return findCompulsoryTokens(csmElement, node);
    }

    private List<Integer> findCompulsoryTokens(CsmElement csmElement, Node node) {
        if (csmElement instanceof CsmSequence) {
            CsmSequence csmSequence = (CsmSequence) csmElement;
            List<Integer> elements = new LinkedList<>();
            csmSequence.getElements().forEach(e -> elements.addAll(findCompulsoryTokens(e, node)));
            return elements;
        } else if (csmElement instanceof CsmNone) {
            // nothing to do
            return Collections.emptyList();
        } else if (csmElement instanceof CsmComment) {
            // nothing to do
            return Collections.emptyList();
        } else if (csmElement instanceof CsmList) {
            List<Integer> elements = new LinkedList<>();
            CsmList csmList = (CsmList) csmElement;
            if (csmList.getProperty().isAboutNodes()) {
                NodeList nodeList = csmList.getProperty().listValueFor(node);
                if (!nodeList.isEmpty()) {
                    elements.addAll(findCompulsoryTokens(csmList.getPreceeding(), node));
                    for (int i = 0; i < nodeList.size(); i++) {
                        if (i != 0) {
                            elements.addAll(findCompulsoryTokens(((CsmList) csmElement).getSeparatorPre(), node));
                        }
                        elements.addAll(findCompulsoryTokens(nodeList.get(i)));
                        if (i != (nodeList.size() - 1)) {
                            elements.addAll(findCompulsoryTokens(((CsmList) csmElement).getSeparatorPost(), node));
                        }

                    }
                    elements.addAll(findCompulsoryTokens(csmList.getFollowing(), node));
                }
            } else {
                Collection collection = csmList.getProperty().listPropertyFor(node);
                if (!collection.isEmpty()) {
                    elements.addAll(findCompulsoryTokens(csmList.getPreceeding(), node));

                    boolean first = true;
                    for (Iterator it = collection.iterator(); it.hasNext(); ) {
                        if (!first) {
                            elements.addAll(findCompulsoryTokens(((CsmList) csmElement).getSeparatorPre(), node));
                        }
                        if (true) throw new UnsupportedOperationException(it.next().toString());
                        //findCompulsoryTokens(it.next());
                        if (it.hasNext()) {
                            elements.addAll(findCompulsoryTokens(((CsmList) csmElement).getSeparatorPost(), node));
                        }
                        first = false;
                    }
                    elements.addAll(findCompulsoryTokens(csmList.getFollowing(), node));
                }
            }
            return elements;
        } else if (csmElement instanceof CsmToken) {
            CsmToken csmToken = (CsmToken) csmElement;
            if (csmToken.getTokenType() <= 5) {
                return Collections.emptyList();
            }
            if (csmToken.getTokenType() >= 31 && csmToken.getTokenType() <= 36) {
                return Collections.emptyList();
            }
            List<Integer> res = new LinkedList<>();
            res.add(csmToken.getTokenType());
            return res;
        } else if (csmElement instanceof CsmConditional) {
            CsmConditional csmConditional = (CsmConditional) csmElement;
            boolean condition;
            switch (csmConditional.getCondition()) {
                case FLAG:
                    condition = (Boolean) csmConditional.getProperty().singleValueFor(node);
                    break;
                case IS_PRESENT:
                    condition = !csmConditional.getProperty().isNull(node);
                    break;
                default:
                    throw new UnsupportedOperationException(csmConditional.getCondition().toString());
            }
            if (condition) {
                return findCompulsoryTokens(csmConditional.getThenElement(), node);
            } else {
                return findCompulsoryTokens(csmConditional.getElseElement(), node);
            }
        } else if (csmElement instanceof CsmSingleReference) {
            CsmSingleReference singleReference = (CsmSingleReference) csmElement;
            return findCompulsoryTokens(singleReference.getProperty().singlePropertyFor(node));
        } else if (csmElement instanceof CsmAttribute) {
            CsmAttribute csmAttribute = (CsmAttribute) csmElement;
            String text = csmAttribute.getProperty().singleValueFor(node).toString();
            List<Integer> res = new LinkedList<>();
            res.add(csmAttribute.getTokenType(text));
            return res;
        } else if (csmElement instanceof CsmIndent) {
            return Collections.emptyList();
        } else if (csmElement instanceof CsmUnindent) {
            return Collections.emptyList();
        } else if (csmElement instanceof CsmOrphanCommentsEnding) {
            return Collections.emptyList();
        } else {
            throw new UnsupportedOperationException(csmElement.getClass().getSimpleName());
        }
    }
}
