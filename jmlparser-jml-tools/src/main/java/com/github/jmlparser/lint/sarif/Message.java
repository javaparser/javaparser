
package com.github.jmlparser.lint.sarif;

import java.util.ArrayList;
import java.util.List;
import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * Encapsulates a message intended to be read by the end user.
 */
@Generated("jsonschema2pojo")
public class Message {

    /**
     * A plain text message string.
     */
    @SerializedName("text")
    @Expose
    private String text;
    /**
     * A Markdown message string.
     */
    @SerializedName("markdown")
    @Expose
    private String markdown;
    /**
     * The identifier for this message.
     */
    @SerializedName("id")
    @Expose
    private String id;
    /**
     * An array of strings to substitute into the message string.
     */
    @SerializedName("arguments")
    @Expose
    private List<String> arguments = new ArrayList<String>();
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public Message() {
    }

    /**
     * @param markdown
     * @param arguments
     * @param text
     * @param id
     * @param properties
     */
    public Message(String text, String markdown, String id, List<String> arguments, PropertyBag properties) {
        super();
        this.text = text;
        this.markdown = markdown;
        this.id = id;
        this.arguments = arguments;
        this.properties = properties;
    }

    /**
     * A plain text message string.
     */
    public String getText() {
        return text;
    }

    /**
     * A plain text message string.
     */
    public void setText(String text) {
        this.text = text;
    }

    public Message withText(String text) {
        this.text = text;
        return this;
    }

    /**
     * A Markdown message string.
     */
    public String getMarkdown() {
        return markdown;
    }

    /**
     * A Markdown message string.
     */
    public void setMarkdown(String markdown) {
        this.markdown = markdown;
    }

    public Message withMarkdown(String markdown) {
        this.markdown = markdown;
        return this;
    }

    /**
     * The identifier for this message.
     */
    public String getId() {
        return id;
    }

    /**
     * The identifier for this message.
     */
    public void setId(String id) {
        this.id = id;
    }

    public Message withId(String id) {
        this.id = id;
        return this;
    }

    /**
     * An array of strings to substitute into the message string.
     */
    public List<String> getArguments() {
        return arguments;
    }

    /**
     * An array of strings to substitute into the message string.
     */
    public void setArguments(List<String> arguments) {
        this.arguments = arguments;
    }

    public Message withArguments(List<String> arguments) {
        this.arguments = arguments;
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

    public Message withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(Message.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("text");
        sb.append('=');
        sb.append(((this.text == null) ? "<null>" : this.text));
        sb.append(',');
        sb.append("markdown");
        sb.append('=');
        sb.append(((this.markdown == null) ? "<null>" : this.markdown));
        sb.append(',');
        sb.append("id");
        sb.append('=');
        sb.append(((this.id == null) ? "<null>" : this.id));
        sb.append(',');
        sb.append("arguments");
        sb.append('=');
        sb.append(((this.arguments == null) ? "<null>" : this.arguments));
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
        result = ((result * 31) + ((this.markdown == null) ? 0 : this.markdown.hashCode()));
        result = ((result * 31) + ((this.arguments == null) ? 0 : this.arguments.hashCode()));
        result = ((result * 31) + ((this.text == null) ? 0 : this.text.hashCode()));
        result = ((result * 31) + ((this.id == null) ? 0 : this.id.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof Message) == false) {
            return false;
        }
        Message rhs = ((Message) other);
        return ((((((this.markdown == rhs.markdown) || ((this.markdown != null) && this.markdown.equals(rhs.markdown))) && ((this.arguments == rhs.arguments) || ((this.arguments != null) && this.arguments.equals(rhs.arguments)))) && ((this.text == rhs.text) || ((this.text != null) && this.text.equals(rhs.text)))) && ((this.id == rhs.id) || ((this.id != null) && this.id.equals(rhs.id)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }

}
