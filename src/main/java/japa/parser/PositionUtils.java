package japa.parser;

import japa.parser.ast.Node;

import java.util.List;

public class PositionUtils {
    public static <T extends Node> void sortByBeginPosition(List<T> nodes){
        for (int i=0;i<nodes.size();i++){
            for (int j=i+1;j<nodes.size();j++){
                T nodeI = nodes.get(i);
                T nodeJ = nodes.get(j);
                if (!areInOrder(nodeI,nodeJ)){
                    nodes.set(i,nodeJ);
                    nodes.set(j,nodeI);
                }
            }
        }
    }
    public static boolean areInOrder(Node a, Node b){
        return
                (a.getBeginLine()<b.getBeginLine())
                        || (a.getBeginLine()==b.getBeginLine() && a.getBeginColumn()<b.getBeginColumn() );
    }
}
