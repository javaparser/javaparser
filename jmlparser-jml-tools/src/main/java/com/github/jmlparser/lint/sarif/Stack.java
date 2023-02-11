
package com.github.jmlparser.lint.sarif;

import java.util.ArrayList;
import java.util.List;
import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * A call stack that is relevant to a result.
 */
@Generated("jsonschema2pojo")
public class Stack {

    /**
     * Encapsulates a message intended to be read by the end user.
     */
    @SerializedName("message")
    @Expose
    private Message message;
    /**
     * An array of stack frames that represents a sequence of calls, rendered in reverse chronological order, that comprise the call stack.
     * (Required)
     */
    @SerializedName("frames")
    @Expose
    private List<StackFrame> frames = new ArrayList<StackFrame>();
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public Stack() {
    }

    /**
     * @param frames
     * @param message
     * @param properties
     */
    public Stack(Message message, List<StackFrame> frames, PropertyBag properties) {
        super();
        this.message = message;
        this.frames = frames;
        this.properties = properties;
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

    public Stack withMessage(Message message) {
        this.message = message;
        return this;
    }

    /**
     * An array of stack frames that represents a sequence of calls, rendered in reverse chronological order, that comprise the call stack.
     * (Required)
     */
    public List<StackFrame> getFrames() {
        return frames;
    }

    /**
     * An array of stack frames that represents a sequence of calls, rendered in reverse chronological order, that comprise the call stack.
     * (Required)
     */
    public void setFrames(List<StackFrame> frames) {
        this.frames = frames;
    }

    public Stack withFrames(List<StackFrame> frames) {
        this.frames = frames;
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

    public Stack withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(Stack.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("message");
        sb.append('=');
        sb.append(((this.message == null) ? "<null>" : this.message));
        sb.append(',');
        sb.append("frames");
        sb.append('=');
        sb.append(((this.frames == null) ? "<null>" : this.frames));
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
        result = ((result * 31) + ((this.message == null) ? 0 : this.message.hashCode()));
        result = ((result * 31) + ((this.frames == null) ? 0 : this.frames.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof Stack) == false) {
            return false;
        }
        Stack rhs = ((Stack) other);
        return ((((this.message == rhs.message) || ((this.message != null) && this.message.equals(rhs.message))) && ((this.frames == rhs.frames) || ((this.frames != null) && this.frames.equals(rhs.frames)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }

}
