
package japa.parser.ast.comments;

import java.util.LinkedList;
import java.util.List;

/**
 * Set of comments produced by CommentsParser.
 */
public class CommentsCollection {
    private List<LineComment> lineComments = new LinkedList<LineComment>();
    private List<BlockComment> blockComments = new LinkedList<BlockComment>();
    private List<JavadocComment> javadocComments = new LinkedList<JavadocComment>();

    public List<LineComment> getLineComments(){
        return lineComments;
    }

    public List<BlockComment> getBlockComments(){
        return blockComments;
    }

    public List<JavadocComment> getJavadocComments(){
        return javadocComments;
    }

    public void addComment(LineComment lineComment){
        this.lineComments.add(lineComment);
    }

    public void addComment(BlockComment blockComment){
        this.blockComments.add(blockComment);
    }

    public void addComment(JavadocComment javadocComment){
        this.javadocComments.add(javadocComment);
    }

    public boolean contains(Comment comment){
        for (Comment c : getAll()){
            // we tollerate a difference of one element in the end column:
            // it depends how \r and \n are calculated...
            if ( c.getBeginLine()==comment.getBeginLine() &&
                 c.getBeginColumn()==comment.getBeginColumn() &&
                 c.getEndLine()==comment.getEndLine() &&
                 Math.abs(c.getEndColumn()-comment.getEndColumn())<2 ){
                return true;
            }
        }
        return false;
    }

    public List<Comment> getAll(){
        List<Comment> comments = new LinkedList<Comment>();
        comments.addAll(lineComments);
        comments.addAll(blockComments);
        comments.addAll(javadocComments);
        return comments;
    }

    public int size(){
        return lineComments.size()+blockComments.size()+javadocComments.size();
    }

    public CommentsCollection minus(CommentsCollection other){
        CommentsCollection result = new CommentsCollection();
        for (LineComment comment : lineComments){
            if (!other.contains(comment)){
                result.lineComments.add(comment);
            }
        }
        for (BlockComment comment : blockComments){
            if (!other.contains(comment)){
                result.blockComments.add(comment);
            }
        }
        for (JavadocComment comment : javadocComments){
            if (!other.contains(comment)){
                result.javadocComments.add(comment);
            }
        }
        return result;
    }
}
