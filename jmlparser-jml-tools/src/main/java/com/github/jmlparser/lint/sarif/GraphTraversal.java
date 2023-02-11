
package com.github.jmlparser.lint.sarif;

import java.util.ArrayList;
import java.util.List;
import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * Represents a path through a graph.
 */
@Generated("jsonschema2pojo")
public class GraphTraversal {

    /**
     * The index within the run.graphs to be associated with the result.
     */
    @SerializedName("runGraphIndex")
    @Expose
    private int runGraphIndex = -1;
    /**
     * The index within the result.graphs to be associated with the result.
     */
    @SerializedName("resultGraphIndex")
    @Expose
    private int resultGraphIndex = -1;
    /**
     * Encapsulates a message intended to be read by the end user.
     */
    @SerializedName("description")
    @Expose
    private Message description;
    /**
     * Values of relevant expressions at the start of the graph traversal that may change during graph traversal.
     */
    @SerializedName("initialState")
    @Expose
    private InitialState__1 initialState;
    /**
     * Values of relevant expressions at the start of the graph traversal that remain constant for the graph traversal.
     */
    @SerializedName("immutableState")
    @Expose
    private ImmutableState__1 immutableState;
    /**
     * The sequences of edges traversed by this graph traversal.
     */
    @SerializedName("edgeTraversals")
    @Expose
    private List<EdgeTraversal> edgeTraversals = new ArrayList<EdgeTraversal>();
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public GraphTraversal() {
    }

    /**
     * @param initialState
     * @param description
     * @param immutableState
     * @param runGraphIndex
     * @param resultGraphIndex
     * @param edgeTraversals
     * @param properties
     */
    public GraphTraversal(int runGraphIndex, int resultGraphIndex, Message description, InitialState__1 initialState, ImmutableState__1 immutableState, List<EdgeTraversal> edgeTraversals, PropertyBag properties) {
        super();
        this.runGraphIndex = runGraphIndex;
        this.resultGraphIndex = resultGraphIndex;
        this.description = description;
        this.initialState = initialState;
        this.immutableState = immutableState;
        this.edgeTraversals = edgeTraversals;
        this.properties = properties;
    }

    /**
     * The index within the run.graphs to be associated with the result.
     */
    public int getRunGraphIndex() {
        return runGraphIndex;
    }

    /**
     * The index within the run.graphs to be associated with the result.
     */
    public void setRunGraphIndex(int runGraphIndex) {
        this.runGraphIndex = runGraphIndex;
    }

    public GraphTraversal withRunGraphIndex(int runGraphIndex) {
        this.runGraphIndex = runGraphIndex;
        return this;
    }

    /**
     * The index within the result.graphs to be associated with the result.
     */
    public int getResultGraphIndex() {
        return resultGraphIndex;
    }

    /**
     * The index within the result.graphs to be associated with the result.
     */
    public void setResultGraphIndex(int resultGraphIndex) {
        this.resultGraphIndex = resultGraphIndex;
    }

    public GraphTraversal withResultGraphIndex(int resultGraphIndex) {
        this.resultGraphIndex = resultGraphIndex;
        return this;
    }

    /**
     * Encapsulates a message intended to be read by the end user.
     */
    public Message getDescription() {
        return description;
    }

    /**
     * Encapsulates a message intended to be read by the end user.
     */
    public void setDescription(Message description) {
        this.description = description;
    }

    public GraphTraversal withDescription(Message description) {
        this.description = description;
        return this;
    }

    /**
     * Values of relevant expressions at the start of the graph traversal that may change during graph traversal.
     */
    public InitialState__1 getInitialState() {
        return initialState;
    }

    /**
     * Values of relevant expressions at the start of the graph traversal that may change during graph traversal.
     */
    public void setInitialState(InitialState__1 initialState) {
        this.initialState = initialState;
    }

    public GraphTraversal withInitialState(InitialState__1 initialState) {
        this.initialState = initialState;
        return this;
    }

    /**
     * Values of relevant expressions at the start of the graph traversal that remain constant for the graph traversal.
     */
    public ImmutableState__1 getImmutableState() {
        return immutableState;
    }

    /**
     * Values of relevant expressions at the start of the graph traversal that remain constant for the graph traversal.
     */
    public void setImmutableState(ImmutableState__1 immutableState) {
        this.immutableState = immutableState;
    }

    public GraphTraversal withImmutableState(ImmutableState__1 immutableState) {
        this.immutableState = immutableState;
        return this;
    }

    /**
     * The sequences of edges traversed by this graph traversal.
     */
    public List<EdgeTraversal> getEdgeTraversals() {
        return edgeTraversals;
    }

    /**
     * The sequences of edges traversed by this graph traversal.
     */
    public void setEdgeTraversals(List<EdgeTraversal> edgeTraversals) {
        this.edgeTraversals = edgeTraversals;
    }

    public GraphTraversal withEdgeTraversals(List<EdgeTraversal> edgeTraversals) {
        this.edgeTraversals = edgeTraversals;
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

    public GraphTraversal withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(GraphTraversal.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("runGraphIndex");
        sb.append('=');
        sb.append(this.runGraphIndex);
        sb.append(',');
        sb.append("resultGraphIndex");
        sb.append('=');
        sb.append(this.resultGraphIndex);
        sb.append(',');
        sb.append("description");
        sb.append('=');
        sb.append(((this.description == null) ? "<null>" : this.description));
        sb.append(',');
        sb.append("initialState");
        sb.append('=');
        sb.append(((this.initialState == null) ? "<null>" : this.initialState));
        sb.append(',');
        sb.append("immutableState");
        sb.append('=');
        sb.append(((this.immutableState == null) ? "<null>" : this.immutableState));
        sb.append(',');
        sb.append("edgeTraversals");
        sb.append('=');
        sb.append(((this.edgeTraversals == null) ? "<null>" : this.edgeTraversals));
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
        result = ((result * 31) + ((this.initialState == null) ? 0 : this.initialState.hashCode()));
        result = ((result * 31) + ((this.description == null) ? 0 : this.description.hashCode()));
        result = ((result * 31) + ((this.immutableState == null) ? 0 : this.immutableState.hashCode()));
        result = ((result * 31) + this.runGraphIndex);
        result = ((result * 31) + this.resultGraphIndex);
        result = ((result * 31) + ((this.edgeTraversals == null) ? 0 : this.edgeTraversals.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof GraphTraversal) == false) {
            return false;
        }
        GraphTraversal rhs = ((GraphTraversal) other);
        return ((((((((this.initialState == rhs.initialState) || ((this.initialState != null) && this.initialState.equals(rhs.initialState))) && ((this.description == rhs.description) || ((this.description != null) && this.description.equals(rhs.description)))) && ((this.immutableState == rhs.immutableState) || ((this.immutableState != null) && this.immutableState.equals(rhs.immutableState)))) && (this.runGraphIndex == rhs.runGraphIndex)) && (this.resultGraphIndex == rhs.resultGraphIndex)) && ((this.edgeTraversals == rhs.edgeTraversals) || ((this.edgeTraversals != null) && this.edgeTraversals.equals(rhs.edgeTraversals)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }

}
