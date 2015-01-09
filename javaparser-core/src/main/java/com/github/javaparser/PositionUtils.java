package com.github.javaparser;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.AnnotableNode;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.AnnotationExpr;

import java.util.LinkedList;
import java.util.List;

public class PositionUtils {

    public static <T extends Node> void sortByBeginPosition(List<T> nodes){
        sortByBeginPosition(nodes, false);
    }

    
    public static <T extends Node> void sortByBeginPosition(List<T> nodes, boolean ignoringAnnotations){
        T[] arrayNodos=(T[])new Node[0];
        arrayNodos = (T[])nodes.toArray(arrayNodos);
        for (int i=0;i<arrayNodos.length;i++){
            for (int j=i+1;j<arrayNodos.length;j++){
                T nodeI = arrayNodos[i];
                T nodeJ = arrayNodos[j];
                if (!areInOrder(nodeI, nodeJ, ignoringAnnotations)){
                    arrayNodos[i]=nodeJ;
                    arrayNodos[j]=nodeI;
                }
            }
        }
        for (int i=0;i<arrayNodos.length;i++){
            nodes.set(i,arrayNodos[i]);
        }

    }

    public static boolean areInOrder(Node a, Node b){
        return areInOrder(a, b, false);
    }

    public static boolean areInOrder(Node a, Node b, boolean ignoringAnnotations){
        if (ignoringAnnotations) {
            return
                    (beginLineWithoutConsideringAnnotation(a)<beginLineWithoutConsideringAnnotation(b))
                            || (beginLineWithoutConsideringAnnotation(a)==beginLineWithoutConsideringAnnotation(b)
                                && beginColumnWithoutConsideringAnnotation(a)<beginColumnWithoutConsideringAnnotation(b) );
        }

        return
                (a.getBeginLine()<b.getBeginLine())
                        || (a.getBeginLine()==b.getBeginLine() && a.getBeginColumn()<b.getBeginColumn() );
    }

    public static AnnotationExpr getLastAnnotation(Node node) {
        if (node instanceof AnnotableNode){
            List<AnnotationExpr> annotations = new LinkedList<AnnotationExpr>();
            annotations.addAll(((AnnotableNode) node).getAnnotations());
            if (annotations.size()==0){
                return null;
            }
            sortByBeginPosition(annotations);
            AnnotationExpr lastAnnotation = annotations.get(annotations.size()-1);
            return lastAnnotation;
        } else {
            return null;
        }
    }

    private static int beginLineWithoutConsideringAnnotation(Node node) {
        return beginNodeWithoutConsideringAnnotations(node).getBeginLine();
    }


    private static int beginColumnWithoutConsideringAnnotation(Node node) {
        return beginNodeWithoutConsideringAnnotations(node).getBeginColumn();
    }

    private static Node beginNodeWithoutConsideringAnnotations(Node node) {
        if (node instanceof MethodDeclaration) {
            MethodDeclaration casted = (MethodDeclaration) node;
            return casted.getType();
        } else if (node instanceof FieldDeclaration) {
            FieldDeclaration casted = (FieldDeclaration) node;
            return casted.getType();
        } else if (node instanceof ClassOrInterfaceDeclaration) {
            ClassOrInterfaceDeclaration casted = (ClassOrInterfaceDeclaration) node;
            return casted.getNameExpr();
        }  else {
            return node;
        }
    }

    public static boolean nodeContains(Node container, Node contained, boolean ignoringAnnotations){
        if (!ignoringAnnotations || PositionUtils.getLastAnnotation(container)==null){
            return container.contains(contained);
        }
        if (!container.contains(contained)){
            return false;
        }
        // if the node is contained, but it comes immediately after the annotations,
        // let's not consider it contained
        if (container instanceof AnnotableNode){
            int bl = beginLineWithoutConsideringAnnotation(container);
            int bc = beginColumnWithoutConsideringAnnotation(container);
            if (bl>contained.getBeginLine()) return false;
            if (bl==contained.getBeginLine() && bc>contained.getBeginColumn()) return false;
            if (container.getEndLine()<contained.getEndLine()) return false;
            if (container.getEndLine()==contained.getEndLine() && container.getEndColumn()<contained.getEndColumn()) return false;
            return true;
        }
        return true;
    }

}
