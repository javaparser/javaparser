package com.github.javaparser;

/**
 * The configuration that is used by the parser when it is instantiated.
 */
public class ParserConfiguration {
    public boolean attributeComments = true;
    public boolean doNotAssignCommentsPrecedingEmptyLines = true;
    public boolean doNotConsiderAnnotationsAsNodeStartForCodeAttribution = false;

    public boolean isAttributeComments() {
        return attributeComments;
    }

    public ParserConfiguration setAttributeComments(boolean attributeComments) {
        this.attributeComments = attributeComments;
        return this;
    }

    public boolean isDoNotAssignCommentsPrecedingEmptyLines() {
        return doNotAssignCommentsPrecedingEmptyLines;
    }

    public ParserConfiguration setDoNotAssignCommentsPrecedingEmptyLines(boolean doNotAssignCommentsPrecedingEmptyLines) {
        this.doNotAssignCommentsPrecedingEmptyLines = doNotAssignCommentsPrecedingEmptyLines;
        return this;
    }

    public boolean isDoNotConsiderAnnotationsAsNodeStartForCodeAttribution() {
        return doNotConsiderAnnotationsAsNodeStartForCodeAttribution;
    }

    public ParserConfiguration setDoNotConsiderAnnotationsAsNodeStartForCodeAttribution(boolean doNotConsiderAnnotationsAsNodeStartForCodeAttribution) {
        this.doNotConsiderAnnotationsAsNodeStartForCodeAttribution = doNotConsiderAnnotationsAsNodeStartForCodeAttribution;
        return this;
    }
}
