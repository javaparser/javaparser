
package com.github.jmlparser.lint.sarif;

import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * Represents the contents of an artifact.
 */
@Generated("jsonschema2pojo")
public class ArtifactContent {

    /**
     * UTF-8-encoded content from a text artifact.
     */
    @SerializedName("text")
    @Expose
    private String text;
    /**
     * MIME Base64-encoded content from a binary artifact, or from a text artifact in its original encoding.
     */
    @SerializedName("binary")
    @Expose
    private String binary;
    /**
     * A message string or message format string rendered in multiple formats.
     */
    @SerializedName("rendered")
    @Expose
    private MultiformatMessageString rendered;
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public ArtifactContent() {
    }

    /**
     * @param rendered
     * @param binary
     * @param text
     * @param properties
     */
    public ArtifactContent(String text, String binary, MultiformatMessageString rendered, PropertyBag properties) {
        super();
        this.text = text;
        this.binary = binary;
        this.rendered = rendered;
        this.properties = properties;
    }

    /**
     * UTF-8-encoded content from a text artifact.
     */
    public String getText() {
        return text;
    }

    /**
     * UTF-8-encoded content from a text artifact.
     */
    public void setText(String text) {
        this.text = text;
    }

    public ArtifactContent withText(String text) {
        this.text = text;
        return this;
    }

    /**
     * MIME Base64-encoded content from a binary artifact, or from a text artifact in its original encoding.
     */
    public String getBinary() {
        return binary;
    }

    /**
     * MIME Base64-encoded content from a binary artifact, or from a text artifact in its original encoding.
     */
    public void setBinary(String binary) {
        this.binary = binary;
    }

    public ArtifactContent withBinary(String binary) {
        this.binary = binary;
        return this;
    }

    /**
     * A message string or message format string rendered in multiple formats.
     */
    public MultiformatMessageString getRendered() {
        return rendered;
    }

    /**
     * A message string or message format string rendered in multiple formats.
     */
    public void setRendered(MultiformatMessageString rendered) {
        this.rendered = rendered;
    }

    public ArtifactContent withRendered(MultiformatMessageString rendered) {
        this.rendered = rendered;
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

    public ArtifactContent withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(ArtifactContent.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("text");
        sb.append('=');
        sb.append(((this.text == null) ? "<null>" : this.text));
        sb.append(',');
        sb.append("binary");
        sb.append('=');
        sb.append(((this.binary == null) ? "<null>" : this.binary));
        sb.append(',');
        sb.append("rendered");
        sb.append('=');
        sb.append(((this.rendered == null) ? "<null>" : this.rendered));
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
        result = ((result * 31) + ((this.text == null) ? 0 : this.text.hashCode()));
        result = ((result * 31) + ((this.rendered == null) ? 0 : this.rendered.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        result = ((result * 31) + ((this.binary == null) ? 0 : this.binary.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof ArtifactContent) == false) {
            return false;
        }
        ArtifactContent rhs = ((ArtifactContent) other);
        return (((((this.text == rhs.text) || ((this.text != null) && this.text.equals(rhs.text))) && ((this.rendered == rhs.rendered) || ((this.rendered != null) && this.rendered.equals(rhs.rendered)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties)))) && ((this.binary == rhs.binary) || ((this.binary != null) && this.binary.equals(rhs.binary))));
    }

}
