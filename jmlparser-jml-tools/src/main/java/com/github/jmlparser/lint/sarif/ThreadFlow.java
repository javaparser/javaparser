
package com.github.jmlparser.lint.sarif;

import java.util.ArrayList;
import java.util.List;
import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * Describes a sequence of code locations that specify a path through a single thread of execution such as an operating system or fiber.
 */
@Generated("jsonschema2pojo")
public class ThreadFlow {

    /**
     * An string that uniquely identifies the threadFlow within the codeFlow in which it occurs.
     */
    @SerializedName("id")
    @Expose
    private String id;
    /**
     * Encapsulates a message intended to be read by the end user.
     */
    @SerializedName("message")
    @Expose
    private Message message;
    /**
     * Values of relevant expressions at the start of the thread flow that may change during thread flow execution.
     */
    @SerializedName("initialState")
    @Expose
    private InitialState initialState;
    /**
     * Values of relevant expressions at the start of the thread flow that remain constant.
     */
    @SerializedName("immutableState")
    @Expose
    private ImmutableState immutableState;
    /**
     * A temporally ordered array of 'threadFlowLocation' objects, each of which describes a location visited by the tool while producing the result.
     * (Required)
     */
    @SerializedName("locations")
    @Expose
    private List<ThreadFlowLocation> locations = new ArrayList<ThreadFlowLocation>();
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public ThreadFlow() {
    }

    /**
     * @param initialState
     * @param immutableState
     * @param locations
     * @param id
     * @param message
     * @param properties
     */
    public ThreadFlow(String id, Message message, InitialState initialState, ImmutableState immutableState, List<ThreadFlowLocation> locations, PropertyBag properties) {
        super();
        this.id = id;
        this.message = message;
        this.initialState = initialState;
        this.immutableState = immutableState;
        this.locations = locations;
        this.properties = properties;
    }

    /**
     * An string that uniquely identifies the threadFlow within the codeFlow in which it occurs.
     */
    public String getId() {
        return id;
    }

    /**
     * An string that uniquely identifies the threadFlow within the codeFlow in which it occurs.
     */
    public void setId(String id) {
        this.id = id;
    }

    public ThreadFlow withId(String id) {
        this.id = id;
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

    public ThreadFlow withMessage(Message message) {
        this.message = message;
        return this;
    }

    /**
     * Values of relevant expressions at the start of the thread flow that may change during thread flow execution.
     */
    public InitialState getInitialState() {
        return initialState;
    }

    /**
     * Values of relevant expressions at the start of the thread flow that may change during thread flow execution.
     */
    public void setInitialState(InitialState initialState) {
        this.initialState = initialState;
    }

    public ThreadFlow withInitialState(InitialState initialState) {
        this.initialState = initialState;
        return this;
    }

    /**
     * Values of relevant expressions at the start of the thread flow that remain constant.
     */
    public ImmutableState getImmutableState() {
        return immutableState;
    }

    /**
     * Values of relevant expressions at the start of the thread flow that remain constant.
     */
    public void setImmutableState(ImmutableState immutableState) {
        this.immutableState = immutableState;
    }

    public ThreadFlow withImmutableState(ImmutableState immutableState) {
        this.immutableState = immutableState;
        return this;
    }

    /**
     * A temporally ordered array of 'threadFlowLocation' objects, each of which describes a location visited by the tool while producing the result.
     * (Required)
     */
    public List<ThreadFlowLocation> getLocations() {
        return locations;
    }

    /**
     * A temporally ordered array of 'threadFlowLocation' objects, each of which describes a location visited by the tool while producing the result.
     * (Required)
     */
    public void setLocations(List<ThreadFlowLocation> locations) {
        this.locations = locations;
    }

    public ThreadFlow withLocations(List<ThreadFlowLocation> locations) {
        this.locations = locations;
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

    public ThreadFlow withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(ThreadFlow.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("id");
        sb.append('=');
        sb.append(((this.id == null) ? "<null>" : this.id));
        sb.append(',');
        sb.append("message");
        sb.append('=');
        sb.append(((this.message == null) ? "<null>" : this.message));
        sb.append(',');
        sb.append("initialState");
        sb.append('=');
        sb.append(((this.initialState == null) ? "<null>" : this.initialState));
        sb.append(',');
        sb.append("immutableState");
        sb.append('=');
        sb.append(((this.immutableState == null) ? "<null>" : this.immutableState));
        sb.append(',');
        sb.append("locations");
        sb.append('=');
        sb.append(((this.locations == null) ? "<null>" : this.locations));
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
        result = ((result * 31) + ((this.immutableState == null) ? 0 : this.immutableState.hashCode()));
        result = ((result * 31) + ((this.locations == null) ? 0 : this.locations.hashCode()));
        result = ((result * 31) + ((this.id == null) ? 0 : this.id.hashCode()));
        result = ((result * 31) + ((this.initialState == null) ? 0 : this.initialState.hashCode()));
        result = ((result * 31) + ((this.message == null) ? 0 : this.message.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof ThreadFlow) == false) {
            return false;
        }
        ThreadFlow rhs = ((ThreadFlow) other);
        return (((((((this.immutableState == rhs.immutableState) || ((this.immutableState != null) && this.immutableState.equals(rhs.immutableState))) && ((this.locations == rhs.locations) || ((this.locations != null) && this.locations.equals(rhs.locations)))) && ((this.id == rhs.id) || ((this.id != null) && this.id.equals(rhs.id)))) && ((this.initialState == rhs.initialState) || ((this.initialState != null) && this.initialState.equals(rhs.initialState)))) && ((this.message == rhs.message) || ((this.message != null) && this.message.equals(rhs.message)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }

}
