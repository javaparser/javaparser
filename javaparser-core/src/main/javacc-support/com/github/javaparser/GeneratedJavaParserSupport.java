package com.github.javaparser;

import com.github.javaparser.ast.ArrayCreationLevel;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.UnknownType;
import com.github.javaparser.utils.Pair;

import java.util.EnumSet;
import java.util.LinkedList;
import java.util.List;
import java.util.TreeSet;

import static com.github.javaparser.GeneratedJavaParser.CustomToken;
import static com.github.javaparser.ast.type.ArrayType.unwrapArrayTypes;
import static com.github.javaparser.ast.type.ArrayType.wrapInArrayTypes;

/**
 * Support class for {@link GeneratedJavaParser}
 */
abstract class GeneratedJavaParserSupport {
    /**
     * Quickly create a new NodeList
     */
    <X extends Node> NodeList<X> emptyList() {
        return new NodeList<>();
    }

    /**
     * Add obj to list and return it. Create a new list if list is null
     */
    <T extends Node> NodeList<T> add(NodeList<T> list, T obj) {
        if (list == null) {
            list = new NodeList<>();
        }
        list.add(obj);
        return list;
    }

    /**
     * Add obj to list only when list is not null
     */
    <T extends Node> NodeList<T> addWhenNotNull(NodeList<T> list, T obj) {
        if (obj == null) {
            return list;
        }
        return add(list, obj);
    }

    /**
     * Add obj to list at position pos
     */
    <T extends Node> NodeList<T> prepend(NodeList<T> list, T obj) {
        if (list == null) {
            list = new NodeList<>();
        }
        list.addFirst(obj);
        return list;
    }

    /**
     * Add obj to list
     */
    <T> List<T> add(List<T> list, T obj) {
        if (list == null) {
            list = new LinkedList<>();
        }
        list.add(obj);
        return list;
    }

    /**
     * Add modifier mod to modifiers
     */
    void addModifier(GeneratedJavaParser generatedJavaParser, EnumSet<Modifier> modifiers, Modifier mod) {
        if (modifiers.contains(mod)) {
            generatedJavaParser.addProblem("Duplicated modifier");
        }
        modifiers.add(mod);
    }

    /**
     * Return a TokenRange spanning from begin to end
     */
    TokenRange range(GeneratedJavaParser generatedJavaParser, JavaToken begin, JavaToken end) {
        if (generatedJavaParser.storeTokens) {
            return new TokenRange(begin, end);
        }
        return null;
    }

    /**
     * Return a TokenRange spanning from begin to end
     */
    TokenRange range(GeneratedJavaParser generatedJavaParser, Node begin, Node end) {
        if (generatedJavaParser.storeTokens) {
            return new TokenRange(begin.getTokenRange().get().getBegin(), end.getTokenRange().get().getEnd());
        }
        return null;
    }

    /**
     * Propagate expansion of the range on the right to the parent. This is necessary when the right border of the child
     * is determining the right border of the parent (i.e., the child is the last element of the parent). In this case
     * when we "enlarge" the child we should enlarge also the parent.
     */
    private void propagateRangeGrowthOnRight(GeneratedJavaParser generatedJavaParser, Node node, Node endNode) {
        if (generatedJavaParser.storeTokens) {
            node.getParentNode().ifPresent(nodeParent -> {
                boolean isChildOnTheRightBorderOfParent = node.getTokenRange().get().getEnd().equals(nodeParent.getTokenRange().get().getEnd());
                if (isChildOnTheRightBorderOfParent) {
                    propagateRangeGrowthOnRight(generatedJavaParser, nodeParent, endNode);
                }
            });
            node.setTokenRange(range(generatedJavaParser, node, endNode));
        }
    }

    /**
     * Workaround for rather complex ambiguity that lambda's create
     */
    Expression generateLambda(GeneratedJavaParser generatedJavaParser, Expression ret, Statement lambdaBody) {
        if (ret instanceof EnclosedExpr) {
            Expression inner = ((EnclosedExpr) ret).getInner();
            SimpleName id = ((NameExpr) inner).getName();
            NodeList<Parameter> params = add(new NodeList<>(), new Parameter(ret.getTokenRange().orElse(null), EnumSet.noneOf(Modifier.class), new NodeList<>(), new UnknownType(), false, new NodeList<>(), id));
            ret = new LambdaExpr(range(generatedJavaParser, ret, lambdaBody), params, lambdaBody, true);
        } else if (ret instanceof NameExpr) {
            SimpleName id = ((NameExpr) ret).getName();
            NodeList<Parameter> params = add(new NodeList<>(), new Parameter(ret.getTokenRange().orElse(null), EnumSet.noneOf(Modifier.class), new NodeList<>(), new UnknownType(), false, new NodeList<>(), id));
            ret = new LambdaExpr(range(generatedJavaParser, ret, lambdaBody), params, lambdaBody, false);
        } else if (ret instanceof LambdaExpr) {
            ((LambdaExpr) ret).setBody(lambdaBody);
            propagateRangeGrowthOnRight(generatedJavaParser, ret, lambdaBody);
        } else if (ret instanceof CastExpr) {
            CastExpr castExpr = (CastExpr) ret;
            Expression inner = generateLambda(generatedJavaParser, castExpr.getExpression(), lambdaBody);
            castExpr.setExpression(inner);
        } else {
            generatedJavaParser.addProblem("Failed to parse lambda expression! Please create an issue at https://github.com/javaparser/javaparser/issues");
        }
        return ret;
    }

    /**
     * Throws together an ArrayCreationExpr from a lot of pieces
     */
    ArrayCreationExpr juggleArrayCreation(TokenRange range, List<TokenRange> levelRanges, Type type, NodeList<Expression> dimensions, List<NodeList<AnnotationExpr>> arrayAnnotations, ArrayInitializerExpr arrayInitializerExpr) {
        NodeList<ArrayCreationLevel> levels = new NodeList<>();

        for (int i = 0; i < arrayAnnotations.size(); i++) {
            levels.add(new ArrayCreationLevel(levelRanges.get(i), dimensions.get(i), arrayAnnotations.get(i)));
        }
        return new ArrayCreationExpr(range, type, levels, arrayInitializerExpr);
    }

    /**
     * Throws together a Type, taking care of all the array brackets
     */
    Type juggleArrayType(Type partialType, List<ArrayType.ArrayBracketPair> additionalBrackets) {
        Pair<Type, List<ArrayType.ArrayBracketPair>> partialParts = unwrapArrayTypes(partialType);
        Type elementType = partialParts.a;
        List<ArrayType.ArrayBracketPair> leftMostBrackets = partialParts.b;
        return wrapInArrayTypes(elementType, leftMostBrackets, additionalBrackets).clone();
    }

    /**
     * Create a TokenRange that spans exactly one token
     */
    TokenRange tokenRange(Token token) {
        JavaToken javaToken = ((CustomToken) token).javaToken;
        return new TokenRange(javaToken, javaToken);
    }

    /**
     * This is the code from ParseException.initialise, modified to be more horizontal.
     */
    String makeMessageForParseException(ParseException exception) {
        final StringBuilder sb = new StringBuilder("Parse error. Found ");
        final StringBuilder expected = new StringBuilder();

        int maxExpectedTokenSequenceLength = 0;
        TreeSet<String> sortedOptions = new TreeSet<>();
        for (int i = 0; i < exception.expectedTokenSequences.length; i++) {
            if (maxExpectedTokenSequenceLength < exception.expectedTokenSequences[i].length) {
                maxExpectedTokenSequenceLength = exception.expectedTokenSequences[i].length;
            }
            for (int j = 0; j < exception.expectedTokenSequences[i].length; j++) {
                sortedOptions.add(exception.tokenImage[exception.expectedTokenSequences[i][j]]);
            }
        }

        for (String option : sortedOptions) {
            expected.append(" ").append(option);
        }

        sb.append("");

        Token token = exception.currentToken.next;
        for (int i = 0; i < maxExpectedTokenSequenceLength; i++) {
            String tokenText = token.image;
            String escapedTokenText = ParseException.add_escapes(tokenText);
            if (i != 0) {
                sb.append(" ");
            }
            if (token.kind == 0) {
                sb.append(exception.tokenImage[0]);
                break;
            }
            escapedTokenText = "\"" + escapedTokenText + "\"";
            String image = exception.tokenImage[token.kind];
            if (image.equals(escapedTokenText)) {
                sb.append(image);
            } else {
                sb.append(" ")
                        .append(escapedTokenText)
                        .append(" ")
                        .append(image);
            }
            token = token.next;
        }

        if (exception.expectedTokenSequences.length != 0) {
            int numExpectedTokens = exception.expectedTokenSequences.length;
            sb.append(", expected")
                    .append(numExpectedTokens == 1 ? "" : " one of ")
                    .append(expected.toString());
        }
        return sb.toString();
    }
}
