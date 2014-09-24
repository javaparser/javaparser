package japa.parser.ast;

public abstract class TreeVisitor {

    public void visitDepthFirst(Node node){
        process(node);
        for (Node child : node.getChildrenNodes()){
            visitDepthFirst(child);
        }
    }

    public abstract void process(Node node);

}
