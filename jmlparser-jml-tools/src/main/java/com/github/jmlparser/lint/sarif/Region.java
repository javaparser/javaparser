
package com.github.jmlparser.lint.sarif;

import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * A region within an artifact where a result was detected.
 */
@Generated("jsonschema2pojo")
public class Region {

    /**
     * The line number of the first character in the region.
     */
    @SerializedName("startLine")
    @Expose
    private int startLine;
    /**
     * The column number of the first character in the region.
     */
    @SerializedName("startColumn")
    @Expose
    private int startColumn;
    /**
     * The line number of the last character in the region.
     */
    @SerializedName("endLine")
    @Expose
    private int endLine;
    /**
     * The column number of the character following the end of the region.
     */
    @SerializedName("endColumn")
    @Expose
    private int endColumn;
    /**
     * The zero-based offset from the beginning of the artifact of the first character in the region.
     */
    @SerializedName("charOffset")
    @Expose
    private int charOffset = -1;
    /**
     * The length of the region in characters.
     */
    @SerializedName("charLength")
    @Expose
    private int charLength;
    /**
     * The zero-based offset from the beginning of the artifact of the first byte in the region.
     */
    @SerializedName("byteOffset")
    @Expose
    private int byteOffset = -1;
    /**
     * The length of the region in bytes.
     */
    @SerializedName("byteLength")
    @Expose
    private int byteLength;
    /**
     * Represents the contents of an artifact.
     */
    @SerializedName("snippet")
    @Expose
    private ArtifactContent snippet;
    /**
     * Encapsulates a message intended to be read by the end user.
     */
    @SerializedName("message")
    @Expose
    private Message message;
    /**
     * Specifies the source language, if any, of the portion of the artifact specified by the region object.
     */
    @SerializedName("sourceLanguage")
    @Expose
    private String sourceLanguage;
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public Region() {
    }

    /**
     * @param endLine
     * @param snippet
     * @param charOffset
     * @param endColumn
     * @param charLength
     * @param byteOffset
     * @param startColumn
     * @param startLine
     * @param byteLength
     * @param message
     * @param sourceLanguage
     * @param properties
     */
    public Region(int startLine, int startColumn, int endLine, int endColumn, int charOffset, int charLength, int byteOffset, int byteLength, ArtifactContent snippet, Message message, String sourceLanguage, PropertyBag properties) {
        super();
        this.startLine = startLine;
        this.startColumn = startColumn;
        this.endLine = endLine;
        this.endColumn = endColumn;
        this.charOffset = charOffset;
        this.charLength = charLength;
        this.byteOffset = byteOffset;
        this.byteLength = byteLength;
        this.snippet = snippet;
        this.message = message;
        this.sourceLanguage = sourceLanguage;
        this.properties = properties;
    }

    /**
     * The line number of the first character in the region.
     */
    public int getStartLine() {
        return startLine;
    }

    /**
     * The line number of the first character in the region.
     */
    public void setStartLine(int startLine) {
        this.startLine = startLine;
    }

    public Region withStartLine(int startLine) {
        this.startLine = startLine;
        return this;
    }

    /**
     * The column number of the first character in the region.
     */
    public int getStartColumn() {
        return startColumn;
    }

    /**
     * The column number of the first character in the region.
     */
    public void setStartColumn(int startColumn) {
        this.startColumn = startColumn;
    }

    public Region withStartColumn(int startColumn) {
        this.startColumn = startColumn;
        return this;
    }

    /**
     * The line number of the last character in the region.
     */
    public int getEndLine() {
        return endLine;
    }

    /**
     * The line number of the last character in the region.
     */
    public void setEndLine(int endLine) {
        this.endLine = endLine;
    }

    public Region withEndLine(int endLine) {
        this.endLine = endLine;
        return this;
    }

    /**
     * The column number of the character following the end of the region.
     */
    public int getEndColumn() {
        return endColumn;
    }

    /**
     * The column number of the character following the end of the region.
     */
    public void setEndColumn(int endColumn) {
        this.endColumn = endColumn;
    }

    public Region withEndColumn(int endColumn) {
        this.endColumn = endColumn;
        return this;
    }

    /**
     * The zero-based offset from the beginning of the artifact of the first character in the region.
     */
    public int getCharOffset() {
        return charOffset;
    }

    /**
     * The zero-based offset from the beginning of the artifact of the first character in the region.
     */
    public void setCharOffset(int charOffset) {
        this.charOffset = charOffset;
    }

    public Region withCharOffset(int charOffset) {
        this.charOffset = charOffset;
        return this;
    }

    /**
     * The length of the region in characters.
     */
    public int getCharLength() {
        return charLength;
    }

    /**
     * The length of the region in characters.
     */
    public void setCharLength(int charLength) {
        this.charLength = charLength;
    }

    public Region withCharLength(int charLength) {
        this.charLength = charLength;
        return this;
    }

    /**
     * The zero-based offset from the beginning of the artifact of the first byte in the region.
     */
    public int getByteOffset() {
        return byteOffset;
    }

    /**
     * The zero-based offset from the beginning of the artifact of the first byte in the region.
     */
    public void setByteOffset(int byteOffset) {
        this.byteOffset = byteOffset;
    }

    public Region withByteOffset(int byteOffset) {
        this.byteOffset = byteOffset;
        return this;
    }

    /**
     * The length of the region in bytes.
     */
    public int getByteLength() {
        return byteLength;
    }

    /**
     * The length of the region in bytes.
     */
    public void setByteLength(int byteLength) {
        this.byteLength = byteLength;
    }

    public Region withByteLength(int byteLength) {
        this.byteLength = byteLength;
        return this;
    }

    /**
     * Represents the contents of an artifact.
     */
    public ArtifactContent getSnippet() {
        return snippet;
    }

    /**
     * Represents the contents of an artifact.
     */
    public void setSnippet(ArtifactContent snippet) {
        this.snippet = snippet;
    }

    public Region withSnippet(ArtifactContent snippet) {
        this.snippet = snippet;
        return this;
    }

    /**
     * Encapsulates a message intended to be read by the end user.
     */
    public Message getMessage() {
        return message;
    }

    /**
     * Encapsulates a message intended to be read by the end user.
     */
    public void setMessage(Message message) {
        this.message = message;
    }

    public Region withMessage(Message message) {
        this.message = message;
        return this;
    }

    /**
     * Specifies the source language, if any, of the portion of the artifact specified by the region object.
     */
    public String getSourceLanguage() {
        return sourceLanguage;
    }

    /**
     * Specifies the source language, if any, of the portion of the artifact specified by the region object.
     */
    public void setSourceLanguage(String sourceLanguage) {
        this.sourceLanguage = sourceLanguage;
    }

    public Region withSourceLanguage(String sourceLanguage) {
        this.sourceLanguage = sourceLanguage;
        return this;
    }

    /**
     * Key/value pairs that provide additional information about the object.
     */
    public PropertyBag getProperties() {
        return properties;
    }

    /**
     * Key/value pairs that provide additional information about the object.
     */
    public void setProperties(PropertyBag properties) {
        this.properties = properties;
    }

    public Region withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(Region.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("startLine");
        sb.append('=');
        sb.append(this.startLine);
        sb.append(',');
        sb.append("startColumn");
        sb.append('=');
        sb.append(this.startColumn);
        sb.append(',');
        sb.append("endLine");
        sb.append('=');
        sb.append(this.endLine);
        sb.append(',');
        sb.append("endColumn");
        sb.append('=');
        sb.append(this.endColumn);
        sb.append(',');
        sb.append("charOffset");
        sb.append('=');
        sb.append(this.charOffset);
        sb.append(',');
        sb.append("charLength");
        sb.append('=');
        sb.append(this.charLength);
        sb.append(',');
        sb.append("byteOffset");
        sb.append('=');
        sb.append(this.byteOffset);
        sb.append(',');
        sb.append("byteLength");
        sb.append('=');
        sb.append(this.byteLength);
        sb.append(',');
        sb.append("snippet");
        sb.append('=');
        sb.append(((this.snippet == null) ? "<null>" : this.snippet));
        sb.append(',');
        sb.append("message");
        sb.append('=');
        sb.append(((this.message == null) ? "<null>" : this.message));
        sb.append(',');
        sb.append("sourceLanguage");
        sb.append('=');
        sb.append(((this.sourceLanguage == null) ? "<null>" : this.sourceLanguage));
        sb.append(',');
        sb.append("properties");
        sb.append('=');
        sb.append(((this.properties == null) ? "<null>" : this.properties));
        sb.append(',');
        if (sb.charAt((sb.length() - 1)) == ',') {
            sb.setCharAt((sb.length() - 1), ']');
        } else {
            sb.append(']');
        }
        return sb.toString();
    }

    @Override
    public int hashCode() {
        int result = 1;
        result = ((result * 31) + this.endLine);
        result = ((result * 31) + ((this.snippet == null) ? 0 : this.snippet.hashCode()));
        result = ((result * 31) + this.charOffset);
        result = ((result * 31) + this.endColumn);
        result = ((result * 31) + this.charLength);
        result = ((result * 31) + this.byteOffset);
        result = ((result * 31) + this.startColumn);
        result = ((result * 31) + this.startLine);
        result = ((result * 31) + this.byteLength);
        result = ((result * 31) + ((this.message == null) ? 0 : this.message.hashCode()));
        result = ((result * 31) + ((this.sourceLanguage == null) ? 0 : this.sourceLanguage.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof Region) == false) {
            return false;
        }
        Region rhs = ((Region) other);
        return ((((((((((((this.endLine == rhs.endLine) && ((this.snippet == rhs.snippet) || ((this.snippet != null) && this.snippet.equals(rhs.snippet)))) && (this.charOffset == rhs.charOffset)) && (this.endColumn == rhs.endColumn)) && (this.charLength == rhs.charLength)) && (this.byteOffset == rhs.byteOffset)) && (this.startColumn == rhs.startColumn)) && (this.startLine == rhs.startLine)) && (this.byteLength == rhs.byteLength)) && ((this.message == rhs.message) || ((this.message != null) && this.message.equals(rhs.message)))) && ((this.sourceLanguage == rhs.sourceLanguage) || ((this.sourceLanguage != null) && this.sourceLanguage.equals(rhs.sourceLanguage)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }

}
