package japa.parser.ast.comments;

import japa.parser.ast.BlockComment;
import japa.parser.ast.LineComment;

import java.util.LinkedList;
import java.util.List;

/**
 * Set of comments produced by CommentsParser.
 */
public class CommentsCollection {
    private List<LineComment> lineComments = new LinkedList<LineComment>();
    private List<BlockComment> blockComments = new LinkedList<BlockComment>();

    public List<LineComment> getLineComments(){
        return lineComments;
    }

    public void addComment(LineComment lineComment){
        this.lineComments.add(lineComment);
    }

    public void addComment(BlockComment blockComment){
        this.blockComments.add(blockComment);
    }
}
