package japa.parser;

import japa.parser.ast.Node;
import japa.parser.ast.body.AnnotableNode;
import japa.parser.ast.body.ClassOrInterfaceDeclaration;
import japa.parser.ast.body.FieldDeclaration;
import japa.parser.ast.body.MethodDeclaration;
import japa.parser.ast.expr.AnnotationExpr;

import java.lang.annotation.Annotation;
import java.util.LinkedList;
import java.util.List;

public class PositionUtils {

    public static <T extends Node> void sortByBeginPosition(List<T> nodes){
        sortByBeginPosition(nodes, false);
    }

    public static <T extends Node> void sortByBeginPosition(List<T> nodes, boolean ignoringAnnotations){
        for (int i=0;i<nodes.size();i++){
            for (int j=i+1;j<nodes.size();j++){
                T nodeI = nodes.get(i);
                T nodeJ = nodes.get(j);
                if (!areInOrder(nodeI, nodeJ, ignoringAnnotations)){
                    nodes.set(i,nodeJ);
                    nodes.set(j,nodeI);
                }
            }
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
