
package com.github.jmlparser.lint.sarif;

import java.util.HashMap;
import java.util.Map;
import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * A suppression that is relevant to a result.
 */
@Generated("jsonschema2pojo")
public class Suppression {

    /**
     * A stable, unique identifer for the suprression in the form of a GUID.
     */
    @SerializedName("guid")
    @Expose
    private String guid;
    /**
     * A string that indicates where the suppression is persisted.
     * (Required)
     */
    @SerializedName("kind")
    @Expose
    private Suppression.Kind kind;
    /**
     * A string that indicates the state of the suppression.
     */
    @SerializedName("state")
    @Expose
    private Suppression.State state;
    /**
     * A string representing the justification for the suppression.
     */
    @SerializedName("justification")
    @Expose
    private String justification;
    /**
     * A location within a programming artifact.
     */
    @SerializedName("location")
    @Expose
    private Location location;
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public Suppression() {
    }

    /**
     * @param kind
     * @param guid
     * @param location
     * @param state
     * @param justification
     * @param properties
     */
    public Suppression(String guid, Suppression.Kind kind, Suppression.State state, String justification, Location location, PropertyBag properties) {
        super();
        this.guid = guid;
        this.kind = kind;
        this.state = state;
        this.justification = justification;
        this.location = location;
        this.properties = properties;
    }

    /**
     * A stable, unique identifer for the suprression in the form of a GUID.
     */
    public String getGuid() {
        return guid;
    }

    /**
     * A stable, unique identifer for the suprression in the form of a GUID.
     */
    public void setGuid(String guid) {
        this.guid = guid;
    }

    public Suppression withGuid(String guid) {
        this.guid = guid;
        return this;
    }

    /**
     * A string that indicates where the suppression is persisted.
     * (Required)
     */
    public Suppression.Kind getKind() {
        return kind;
    }

    /**
     * A string that indicates where the suppression is persisted.
     * (Required)
     */
    public void setKind(Suppression.Kind kind) {
        this.kind = kind;
    }

    public Suppression withKind(Suppression.Kind kind) {
        this.kind = kind;
        return this;
    }

    /**
     * A string that indicates the state of the suppression.
     */
    public Suppression.State getState() {
        return state;
    }

    /**
     * A string that indicates the state of the suppression.
     */
    public void setState(Suppression.State state) {
        this.state = state;
    }

    public Suppression withState(Suppression.State state) {
        this.state = state;
        return this;
    }

    /**
     * A string representing the justification for the suppression.
     */
    public String getJustification() {
        return justification;
    }

    /**
     * A string representing the justification for the suppression.
     */
    public void setJustification(String justification) {
        this.justification = justification;
    }

    public Suppression withJustification(String justification) {
        this.justification = justification;
        return this;
    }

    /**
     * A location within a programming artifact.
     */
    public Location getLocation() {
        return location;
    }

    /**
     * A location within a programming artifact.
     */
    public void setLocation(Location location) {
        this.location = location;
    }

    public Suppression withLocation(Location location) {
        this.location = location;
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

    public Suppression withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(Suppression.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("guid");
        sb.append('=');
        sb.append(((this.guid == null) ? "<null>" : this.guid));
        sb.append(',');
        sb.append("kind");
        sb.append('=');
        sb.append(((this.kind == null) ? "<null>" : this.kind));
        sb.append(',');
        sb.append("state");
        sb.append('=');
        sb.append(((this.state == null) ? "<null>" : this.state));
        sb.append(',');
        sb.append("justification");
        sb.append('=');
        sb.append(((this.justification == null) ? "<null>" : this.justification));
        sb.append(',');
        sb.append("location");
        sb.append('=');
        sb.append(((this.location == null) ? "<null>" : this.location));
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
        result = ((result * 31) + ((this.guid == null) ? 0 : this.guid.hashCode()));
        result = ((result * 31) + ((this.location == null) ? 0 : this.location.hashCode()));
        result = ((result * 31) + ((this.state == null) ? 0 : this.state.hashCode()));
        result = ((result * 31) + ((this.justification == null) ? 0 : this.justification.hashCode()));
        result = ((result * 31) + ((this.kind == null) ? 0 : this.kind.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof Suppression) == false) {
            return false;
        }
        Suppression rhs = ((Suppression) other);
        return (((((((this.guid == rhs.guid) || ((this.guid != null) && this.guid.equals(rhs.guid))) && ((this.location == rhs.location) || ((this.location != null) && this.location.equals(rhs.location)))) && ((this.state == rhs.state) || ((this.state != null) && this.state.equals(rhs.state)))) && ((this.justification == rhs.justification) || ((this.justification != null) && this.justification.equals(rhs.justification)))) && ((this.kind == rhs.kind) || ((this.kind != null) && this.kind.equals(rhs.kind)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }


    /**
     * A string that indicates where the suppression is persisted.
     */
    @Generated("jsonschema2pojo")
    public enum Kind {

        @SerializedName("inSource")
        IN_SOURCE("inSource"),
        @SerializedName("external")
        EXTERNAL("external");
        private final String value;
        private final static Map<String, Suppression.Kind> CONSTANTS = new HashMap<String, Suppression.Kind>();

        static {
            for (Suppression.Kind c : values()) {
                CONSTANTS.put(c.value, c);
            }
        }

        Kind(String value) {
            this.value = value;
        }

        @Override
        public String toString() {
            return this.value;
        }

        public String value() {
            return this.value;
        }

        public static Suppression.Kind fromValue(String value) {
            Suppression.Kind constant = CONSTANTS.get(value);
            if (constant == null) {
                throw new IllegalArgumentException(value);
            } else {
                return constant;
            }
        }

    }


    /**
     * A string that indicates the state of the suppression.
     */
    @Generated("jsonschema2pojo")
    public enum State {

        @SerializedName("accepted")
        ACCEPTED("accepted"),
        @SerializedName("underReview")
        UNDER_REVIEW("underReview"),
        @SerializedName("rejected")
        REJECTED("rejected");
        private final String value;
        private final static Map<String, Suppression.State> CONSTANTS = new HashMap<String, Suppression.State>();

        static {
            for (Suppression.State c : values()) {
                CONSTANTS.put(c.value, c);
            }
        }

        State(String value) {
            this.value = value;
        }

        @Override
        public String toString() {
            return this.value;
        }

        public String value() {
            return this.value;
        }

        public static Suppression.State fromValue(String value) {
            Suppression.State constant = CONSTANTS.get(value);
            if (constant == null) {
                throw new IllegalArgumentException(value);
            } else {
                return constant;
            }
        }

    }

}
