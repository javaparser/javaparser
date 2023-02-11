
package com.github.jmlparser.lint.sarif;

import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * Represents a directed edge in a graph.
 */
@Generated("jsonschema2pojo")
public class Edge {

    /**
     * A string that uniquely identifies the edge within its graph.
     * (Required)
     */
    @SerializedName("id")
    @Expose
    private String id;
    /**
     * Encapsulates a message intended to be read by the end user.
     */
    @SerializedName("label")
    @Expose
    private Message label;
    /**
     * Identifies the source node (the node at which the edge starts).
     * (Required)
     */
    @SerializedName("sourceNodeId")
    @Expose
    private String sourceNodeId;
    /**
     * Identifies the target node (the node at which the edge ends).
     * (Required)
     */
    @SerializedName("targetNodeId")
    @Expose
    private String targetNodeId;
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public Edge() {
    }

    /**
     * @param sourceNodeId
     * @param id
     * @param label
     * @param targetNodeId
     * @param properties
     */
    public Edge(String id, Message label, String sourceNodeId, String targetNodeId, PropertyBag properties) {
        super();
        this.id = id;
        this.label = label;
        this.sourceNodeId = sourceNodeId;
        this.targetNodeId = targetNodeId;
        this.properties = properties;
    }

    /**
     * A string that uniquely identifies the edge within its graph.
     * (Required)
     */
    public String getId() {
        return id;
    }

    /**
     * A string that uniquely identifies the edge within its graph.
     * (Required)
     */
    public void setId(String id) {
        this.id = id;
    }

    public Edge withId(String id) {
        this.id = id;
        return this;
    }

    /**
     * Encapsulates a message intended to be read by the end user.
     */
    public Message getLabel() {
        return label;
    }

    /**
     * Encapsulates a message intended to be read by the end user.
     */
    public void setLabel(Message label) {
        this.label = label;
    }

    public Edge withLabel(Message label) {
        this.label = label;
        return this;
    }

    /**
     * Identifies the source node (the node at which the edge starts).
     * (Required)
     */
    public String getSourceNodeId() {
        return sourceNodeId;
    }

    /**
     * Identifies the source node (the node at which the edge starts).
     * (Required)
     */
    public void setSourceNodeId(String sourceNodeId) {
        this.sourceNodeId = sourceNodeId;
    }

    public Edge withSourceNodeId(String sourceNodeId) {
        this.sourceNodeId = sourceNodeId;
        return this;
    }

    /**
     * Identifies the target node (the node at which the edge ends).
     * (Required)
     */
    public String getTargetNodeId() {
        return targetNodeId;
    }

    /**
     * Identifies the target node (the node at which the edge ends).
     * (Required)
     */
    public void setTargetNodeId(String targetNodeId) {
        this.targetNodeId = targetNodeId;
    }

    public Edge withTargetNodeId(String targetNodeId) {
        this.targetNodeId = targetNodeId;
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

    public Edge withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(Edge.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("id");
        sb.append('=');
        sb.append(((this.id == null) ? "<null>" : this.id));
        sb.append(',');
        sb.append("label");
        sb.append('=');
        sb.append(((this.label == null) ? "<null>" : this.label));
        sb.append(',');
        sb.append("sourceNodeId");
        sb.append('=');
        sb.append(((this.sourceNodeId == null) ? "<null>" : this.sourceNodeId));
        sb.append(',');
        sb.append("targetNodeId");
        sb.append('=');
        sb.append(((this.targetNodeId == null) ? "<null>" : this.targetNodeId));
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
        result = ((result * 31) + ((this.id == null) ? 0 : this.id.hashCode()));
        result = ((result * 31) + ((this.label == null) ? 0 : this.label.hashCode()));
        result = ((result * 31) + ((this.targetNodeId == null) ? 0 : this.targetNodeId.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        result = ((result * 31) + ((this.sourceNodeId == null) ? 0 : this.sourceNodeId.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof Edge) == false) {
            return false;
        }
        Edge rhs = ((Edge) other);
        return ((((((this.id == rhs.id) || ((this.id != null) && this.id.equals(rhs.id))) && ((this.label == rhs.label) || ((this.label != null) && this.label.equals(rhs.label)))) && ((this.targetNodeId == rhs.targetNodeId) || ((this.targetNodeId != null) && this.targetNodeId.equals(rhs.targetNodeId)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties)))) && ((this.sourceNodeId == rhs.sourceNodeId) || ((this.sourceNodeId != null) && this.sourceNodeId.equals(rhs.sourceNodeId))));
    }

}
