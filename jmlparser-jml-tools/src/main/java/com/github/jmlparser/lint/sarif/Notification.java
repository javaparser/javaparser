
package com.github.jmlparser.lint.sarif;

import java.util.Date;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * Describes a condition relevant to the tool itself, as opposed to being relevant to a target being analyzed by the tool.
 */
@Generated("jsonschema2pojo")
public class Notification {

    /**
     * The locations relevant to this notification.
     */
    @SerializedName("locations")
    @Expose
    private Set<Location> locations = new LinkedHashSet<Location>();
    /**
     * Encapsulates a message intended to be read by the end user.
     * (Required)
     */
    @SerializedName("message")
    @Expose
    private Message message;
    /**
     * A value specifying the severity level of the notification.
     */
    @SerializedName("level")
    @Expose
    private Notification.Level level = Notification.Level.fromValue("warning");
    /**
     * The thread identifier of the code that generated the notification.
     */
    @SerializedName("threadId")
    @Expose
    private int threadId;
    /**
     * The Coordinated Universal Time (UTC) date and time at which the analysis tool generated the notification.
     */
    @SerializedName("timeUtc")
    @Expose
    private Date timeUtc;
    /**
     * Describes a runtime exception encountered during the execution of an analysis tool.
     */
    @SerializedName("exception")
    @Expose
    private Exception exception;
    /**
     * Information about how to locate a relevant reporting descriptor.
     */
    @SerializedName("descriptor")
    @Expose
    private ReportingDescriptorReference descriptor;
    /**
     * Information about how to locate a relevant reporting descriptor.
     */
    @SerializedName("associatedRule")
    @Expose
    private ReportingDescriptorReference associatedRule;
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public Notification() {
    }

    /**
     * @param threadId
     * @param exception
     * @param level
     * @param associatedRule
     * @param timeUtc
     * @param locations
     * @param descriptor
     * @param message
     * @param properties
     */
    public Notification(Set<Location> locations, Message message, Notification.Level level, int threadId, Date timeUtc, Exception exception, ReportingDescriptorReference descriptor, ReportingDescriptorReference associatedRule, PropertyBag properties) {
        super();
        this.locations = locations;
        this.message = message;
        this.level = level;
        this.threadId = threadId;
        this.timeUtc = timeUtc;
        this.exception = exception;
        this.descriptor = descriptor;
        this.associatedRule = associatedRule;
        this.properties = properties;
    }

    /**
     * The locations relevant to this notification.
     */
    public Set<Location> getLocations() {
        return locations;
    }

    /**
     * The locations relevant to this notification.
     */
    public void setLocations(Set<Location> locations) {
        this.locations = locations;
    }

    public Notification withLocations(Set<Location> locations) {
        this.locations = locations;
        return this;
    }

    /**
     * Encapsulates a message intended to be read by the end user.
     * (Required)
     */
    public Message getMessage() {
        return message;
    }

    /**
     * Encapsulates a message intended to be read by the end user.
     * (Required)
     */
    public void setMessage(Message message) {
        this.message = message;
    }

    public Notification withMessage(Message message) {
        this.message = message;
        return this;
    }

    /**
     * A value specifying the severity level of the notification.
     */
    public Notification.Level getLevel() {
        return level;
    }

    /**
     * A value specifying the severity level of the notification.
     */
    public void setLevel(Notification.Level level) {
        this.level = level;
    }

    public Notification withLevel(Notification.Level level) {
        this.level = level;
        return this;
    }

    /**
     * The thread identifier of the code that generated the notification.
     */
    public int getThreadId() {
        return threadId;
    }

    /**
     * The thread identifier of the code that generated the notification.
     */
    public void setThreadId(int threadId) {
        this.threadId = threadId;
    }

    public Notification withThreadId(int threadId) {
        this.threadId = threadId;
        return this;
    }

    /**
     * The Coordinated Universal Time (UTC) date and time at which the analysis tool generated the notification.
     */
    public Date getTimeUtc() {
        return timeUtc;
    }

    /**
     * The Coordinated Universal Time (UTC) date and time at which the analysis tool generated the notification.
     */
    public void setTimeUtc(Date timeUtc) {
        this.timeUtc = timeUtc;
    }

    public Notification withTimeUtc(Date timeUtc) {
        this.timeUtc = timeUtc;
        return this;
    }

    /**
     * Describes a runtime exception encountered during the execution of an analysis tool.
     */
    public Exception getException() {
        return exception;
    }

    /**
     * Describes a runtime exception encountered during the execution of an analysis tool.
     */
    public void setException(Exception exception) {
        this.exception = exception;
    }

    public Notification withException(Exception exception) {
        this.exception = exception;
        return this;
    }

    /**
     * Information about how to locate a relevant reporting descriptor.
     */
    public ReportingDescriptorReference getDescriptor() {
        return descriptor;
    }

    /**
     * Information about how to locate a relevant reporting descriptor.
     */
    public void setDescriptor(ReportingDescriptorReference descriptor) {
        this.descriptor = descriptor;
    }

    public Notification withDescriptor(ReportingDescriptorReference descriptor) {
        this.descriptor = descriptor;
        return this;
    }

    /**
     * Information about how to locate a relevant reporting descriptor.
     */
    public ReportingDescriptorReference getAssociatedRule() {
        return associatedRule;
    }

    /**
     * Information about how to locate a relevant reporting descriptor.
     */
    public void setAssociatedRule(ReportingDescriptorReference associatedRule) {
        this.associatedRule = associatedRule;
    }

    public Notification withAssociatedRule(ReportingDescriptorReference associatedRule) {
        this.associatedRule = associatedRule;
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

    public Notification withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(Notification.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("locations");
        sb.append('=');
        sb.append(((this.locations == null) ? "<null>" : this.locations));
        sb.append(',');
        sb.append("message");
        sb.append('=');
        sb.append(((this.message == null) ? "<null>" : this.message));
        sb.append(',');
        sb.append("level");
        sb.append('=');
        sb.append(((this.level == null) ? "<null>" : this.level));
        sb.append(',');
        sb.append("threadId");
        sb.append('=');
        sb.append(this.threadId);
        sb.append(',');
        sb.append("timeUtc");
        sb.append('=');
        sb.append(((this.timeUtc == null) ? "<null>" : this.timeUtc));
        sb.append(',');
        sb.append("exception");
        sb.append('=');
        sb.append(((this.exception == null) ? "<null>" : this.exception));
        sb.append(',');
        sb.append("descriptor");
        sb.append('=');
        sb.append(((this.descriptor == null) ? "<null>" : this.descriptor));
        sb.append(',');
        sb.append("associatedRule");
        sb.append('=');
        sb.append(((this.associatedRule == null) ? "<null>" : this.associatedRule));
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
        result = ((result * 31) + this.threadId);
        result = ((result * 31) + ((this.exception == null) ? 0 : this.exception.hashCode()));
        result = ((result * 31) + ((this.level == null) ? 0 : this.level.hashCode()));
        result = ((result * 31) + ((this.associatedRule == null) ? 0 : this.associatedRule.hashCode()));
        result = ((result * 31) + ((this.timeUtc == null) ? 0 : this.timeUtc.hashCode()));
        result = ((result * 31) + ((this.locations == null) ? 0 : this.locations.hashCode()));
        result = ((result * 31) + ((this.descriptor == null) ? 0 : this.descriptor.hashCode()));
        result = ((result * 31) + ((this.message == null) ? 0 : this.message.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof Notification) == false) {
            return false;
        }
        Notification rhs = ((Notification) other);
        return (((((((((this.threadId == rhs.threadId) && ((this.exception == rhs.exception) || ((this.exception != null) && this.exception.equals(rhs.exception)))) && ((this.level == rhs.level) || ((this.level != null) && this.level.equals(rhs.level)))) && ((this.associatedRule == rhs.associatedRule) || ((this.associatedRule != null) && this.associatedRule.equals(rhs.associatedRule)))) && ((this.timeUtc == rhs.timeUtc) || ((this.timeUtc != null) && this.timeUtc.equals(rhs.timeUtc)))) && ((this.locations == rhs.locations) || ((this.locations != null) && this.locations.equals(rhs.locations)))) && ((this.descriptor == rhs.descriptor) || ((this.descriptor != null) && this.descriptor.equals(rhs.descriptor)))) && ((this.message == rhs.message) || ((this.message != null) && this.message.equals(rhs.message)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }


    /**
     * A value specifying the severity level of the notification.
     */
    @Generated("jsonschema2pojo")
    public enum Level {

        @SerializedName("none")
        NONE("none"),
        @SerializedName("note")
        NOTE("note"),
        @SerializedName("warning")
        WARNING("warning"),
        @SerializedName("error")
        ERROR("error");
        private final String value;
        private final static Map<String, Notification.Level> CONSTANTS = new HashMap<String, Notification.Level>();

        static {
            for (Notification.Level c : values()) {
                CONSTANTS.put(c.value, c);
            }
        }

        Level(String value) {
            this.value = value;
        }

        @Override
        public String toString() {
            return this.value;
        }

        public String value() {
            return this.value;
        }

        public static Notification.Level fromValue(String value) {
            Notification.Level constant = CONSTANTS.get(value);
            if (constant == null) {
                throw new IllegalArgumentException(value);
            } else {
                return constant;
            }
        }

    }

}
