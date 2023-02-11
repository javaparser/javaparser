
package com.github.jmlparser.lint.sarif;

import java.util.ArrayList;
import java.util.List;
import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * Describes a runtime exception encountered during the execution of an analysis tool.
 */
@Generated("jsonschema2pojo")
public class Exception {

    /**
     * A string that identifies the kind of exception, for example, the fully qualified type name of an object that was thrown, or the symbolic name of a signal.
     */
    @SerializedName("kind")
    @Expose
    private String kind;
    /**
     * A message that describes the exception.
     */
    @SerializedName("message")
    @Expose
    private String message;
    /**
     * A call stack that is relevant to a result.
     */
    @SerializedName("stack")
    @Expose
    private Stack stack;
    /**
     * An array of exception objects each of which is considered a cause of this exception.
     */
    @SerializedName("innerExceptions")
    @Expose
    private List<Exception> innerExceptions = new ArrayList<Exception>();
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public Exception() {
    }

    /**
     * @param stack
     * @param kind
     * @param innerExceptions
     * @param message
     * @param properties
     */
    public Exception(String kind, String message, Stack stack, List<Exception> innerExceptions, PropertyBag properties) {
        super();
        this.kind = kind;
        this.message = message;
        this.stack = stack;
        this.innerExceptions = innerExceptions;
        this.properties = properties;
    }

    /**
     * A string that identifies the kind of exception, for example, the fully qualified type name of an object that was thrown, or the symbolic name of a signal.
     */
    public String getKind() {
        return kind;
    }

    /**
     * A string that identifies the kind of exception, for example, the fully qualified type name of an object that was thrown, or the symbolic name of a signal.
     */
    public void setKind(String kind) {
        this.kind = kind;
    }

    public Exception withKind(String kind) {
        this.kind = kind;
        return this;
    }

    /**
     * A message that describes the exception.
     */
    public String getMessage() {
        return message;
    }

    /**
     * A message that describes the exception.
     */
    public void setMessage(String message) {
        this.message = message;
    }

    public Exception withMessage(String message) {
        this.message = message;
        return this;
    }

    /**
     * A call stack that is relevant to a result.
     */
    public Stack getStack() {
        return stack;
    }

    /**
     * A call stack that is relevant to a result.
     */
    public void setStack(Stack stack) {
        this.stack = stack;
    }

    public Exception withStack(Stack stack) {
        this.stack = stack;
        return this;
    }

    /**
     * An array of exception objects each of which is considered a cause of this exception.
     */
    public List<Exception> getInnerExceptions() {
        return innerExceptions;
    }

    /**
     * An array of exception objects each of which is considered a cause of this exception.
     */
    public void setInnerExceptions(List<Exception> innerExceptions) {
        this.innerExceptions = innerExceptions;
    }

    public Exception withInnerExceptions(List<Exception> innerExceptions) {
        this.innerExceptions = innerExceptions;
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

    public Exception withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(Exception.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("kind");
        sb.append('=');
        sb.append(((this.kind == null) ? "<null>" : this.kind));
        sb.append(',');
        sb.append("message");
        sb.append('=');
        sb.append(((this.message == null) ? "<null>" : this.message));
        sb.append(',');
        sb.append("stack");
        sb.append('=');
        sb.append(((this.stack == null) ? "<null>" : this.stack));
        sb.append(',');
        sb.append("innerExceptions");
        sb.append('=');
        sb.append(((this.innerExceptions == null) ? "<null>" : this.innerExceptions));
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
        result = ((result * 31) + ((this.stack == null) ? 0 : this.stack.hashCode()));
        result = ((result * 31) + ((this.innerExceptions == null) ? 0 : this.innerExceptions.hashCode()));
        result = ((result * 31) + ((this.message == null) ? 0 : this.message.hashCode()));
        result = ((result * 31) + ((this.kind == null) ? 0 : this.kind.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof Exception) == false) {
            return false;
        }
        Exception rhs = ((Exception) other);
        return ((((((this.stack == rhs.stack) || ((this.stack != null) && this.stack.equals(rhs.stack))) && ((this.innerExceptions == rhs.innerExceptions) || ((this.innerExceptions != null) && this.innerExceptions.equals(rhs.innerExceptions)))) && ((this.message == rhs.message) || ((this.message != null) && this.message.equals(rhs.message)))) && ((this.kind == rhs.kind) || ((this.kind != null) && this.kind.equals(rhs.kind)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }

}
