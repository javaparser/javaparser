package com.github.javaparser.ast.type;

import com.github.javaparser.Range;
import com.github.javaparser.ast.ArrayBracketPair;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.utils.Pair;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * To indicate that a type is an array, it gets wrapped in an ArrayType for every array level it has.
 * So, int[][] becomes ArrayType(ArrayType(int)).
 */
public class ArrayType extends ReferenceType<ArrayType> implements NodeWithAnnotations<ArrayType> {
    private Type componentType;

    public ArrayType(Type componentType, List<AnnotationExpr> annotations) {
        setComponentType(componentType);
        setAnnotations(annotations);
    }

    public ArrayType(Range range, Type componentType, List<AnnotationExpr> annotations) {
        super(range);
        setComponentType(componentType);
        setAnnotations(annotations);
    }

    @Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    public Type getComponentType() {
        return componentType;
    }

    public ArrayType setComponentType(final Type type) {
        this.componentType = type;
        setAsParentNodeOf(this.componentType);
        return this;
    }

    /**
     * Takes lists of arrayBracketPairs, assumes the lists are ordered left to right and the pairs are ordered left to right, mirroring the actual code.
     * The type gets wrapped in ArrayTypes so that the outermost ArrayType corresponds to the rightmost ArrayBracketPair.
     */
    @SafeVarargs
    public static Type wrapInArrayTypes(Type type, List<ArrayBracketPair>... arrayBracketPairLists) {
        for (int i = arrayBracketPairLists.length - 1; i >= 0; i--) {
            final List<ArrayBracketPair> arrayBracketPairList = arrayBracketPairLists[i];
            if (arrayBracketPairList != null) {
                for (int j = arrayBracketPairList.size() - 1; j >= 0; j--) {
                    type = new ArrayType(type, arrayBracketPairList.get(j).getAnnotations());
                }
            }
        }
        return type;
    }

    /**
     * Takes a type that may be an ArrayType. Unwraps ArrayTypes until the element type is found.
     *
     * @return a pair of the element type, and the unwrapped ArrayTypes, if any.
     */
    public static Pair<Type, List<ArrayBracketPair>> unwrapArrayTypes(Type type) {
        final List<ArrayBracketPair> arrayBracketPairs = new ArrayList<>();
        while (type instanceof ArrayType) {
            ArrayType arrayType = (ArrayType) type;
            arrayBracketPairs.add(new ArrayBracketPair(Range.UNKNOWN, arrayType.getAnnotations()));
            type = arrayType.getComponentType();
        }
        return new Pair<>(type, arrayBracketPairs);
    }
    
    public static ArrayType arrayOf(Type type, AnnotationExpr... annotations) {
        return new ArrayType(type, Arrays.asList(annotations));
    }
}
