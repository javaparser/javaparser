
package com.github.jmlparser.lint.sarif;

import java.util.Date;
import java.util.LinkedHashSet;
import java.util.Set;
import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * Contains information about how and when a result was detected.
 */
@Generated("jsonschema2pojo")
public class ResultProvenance {

    /**
     * The Coordinated Universal Time (UTC) date and time at which the result was first detected. See "Date/time properties" in the SARIF spec for the required format.
     */
    @SerializedName("firstDetectionTimeUtc")
    @Expose
    private Date firstDetectionTimeUtc;
    /**
     * The Coordinated Universal Time (UTC) date and time at which the result was most recently detected. See "Date/time properties" in the SARIF spec for the required format.
     */
    @SerializedName("lastDetectionTimeUtc")
    @Expose
    private Date lastDetectionTimeUtc;
    /**
     * A GUID-valued string equal to the automationDetails.guid property of the run in which the result was first detected.
     */
    @SerializedName("firstDetectionRunGuid")
    @Expose
    private String firstDetectionRunGuid;
    /**
     * A GUID-valued string equal to the automationDetails.guid property of the run in which the result was most recently detected.
     */
    @SerializedName("lastDetectionRunGuid")
    @Expose
    private String lastDetectionRunGuid;
    /**
     * The index within the run.invocations array of the invocation object which describes the tool invocation that detected the result.
     */
    @SerializedName("invocationIndex")
    @Expose
    private int invocationIndex = -1;
    /**
     * An array of physicalLocation objects which specify the portions of an analysis tool's output that a converter transformed into the result.
     */
    @SerializedName("conversionSources")
    @Expose
    private Set<PhysicalLocation> conversionSources = new LinkedHashSet<PhysicalLocation>();
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public ResultProvenance() {
    }

    /**
     * @param firstDetectionRunGuid
     * @param lastDetectionTimeUtc
     * @param invocationIndex
     * @param lastDetectionRunGuid
     * @param conversionSources
     * @param firstDetectionTimeUtc
     * @param properties
     */
    public ResultProvenance(Date firstDetectionTimeUtc, Date lastDetectionTimeUtc, String firstDetectionRunGuid, String lastDetectionRunGuid, int invocationIndex, Set<PhysicalLocation> conversionSources, PropertyBag properties) {
        super();
        this.firstDetectionTimeUtc = firstDetectionTimeUtc;
        this.lastDetectionTimeUtc = lastDetectionTimeUtc;
        this.firstDetectionRunGuid = firstDetectionRunGuid;
        this.lastDetectionRunGuid = lastDetectionRunGuid;
        this.invocationIndex = invocationIndex;
        this.conversionSources = conversionSources;
        this.properties = properties;
    }

    /**
     * The Coordinated Universal Time (UTC) date and time at which the result was first detected. See "Date/time properties" in the SARIF spec for the required format.
     */
    public Date getFirstDetectionTimeUtc() {
        return firstDetectionTimeUtc;
    }

    /**
     * The Coordinated Universal Time (UTC) date and time at which the result was first detected. See "Date/time properties" in the SARIF spec for the required format.
     */
    public void setFirstDetectionTimeUtc(Date firstDetectionTimeUtc) {
        this.firstDetectionTimeUtc = firstDetectionTimeUtc;
    }

    public ResultProvenance withFirstDetectionTimeUtc(Date firstDetectionTimeUtc) {
        this.firstDetectionTimeUtc = firstDetectionTimeUtc;
        return this;
    }

    /**
     * The Coordinated Universal Time (UTC) date and time at which the result was most recently detected. See "Date/time properties" in the SARIF spec for the required format.
     */
    public Date getLastDetectionTimeUtc() {
        return lastDetectionTimeUtc;
    }

    /**
     * The Coordinated Universal Time (UTC) date and time at which the result was most recently detected. See "Date/time properties" in the SARIF spec for the required format.
     */
    public void setLastDetectionTimeUtc(Date lastDetectionTimeUtc) {
        this.lastDetectionTimeUtc = lastDetectionTimeUtc;
    }

    public ResultProvenance withLastDetectionTimeUtc(Date lastDetectionTimeUtc) {
        this.lastDetectionTimeUtc = lastDetectionTimeUtc;
        return this;
    }

    /**
     * A GUID-valued string equal to the automationDetails.guid property of the run in which the result was first detected.
     */
    public String getFirstDetectionRunGuid() {
        return firstDetectionRunGuid;
    }

    /**
     * A GUID-valued string equal to the automationDetails.guid property of the run in which the result was first detected.
     */
    public void setFirstDetectionRunGuid(String firstDetectionRunGuid) {
        this.firstDetectionRunGuid = firstDetectionRunGuid;
    }

    public ResultProvenance withFirstDetectionRunGuid(String firstDetectionRunGuid) {
        this.firstDetectionRunGuid = firstDetectionRunGuid;
        return this;
    }

    /**
     * A GUID-valued string equal to the automationDetails.guid property of the run in which the result was most recently detected.
     */
    public String getLastDetectionRunGuid() {
        return lastDetectionRunGuid;
    }

    /**
     * A GUID-valued string equal to the automationDetails.guid property of the run in which the result was most recently detected.
     */
    public void setLastDetectionRunGuid(String lastDetectionRunGuid) {
        this.lastDetectionRunGuid = lastDetectionRunGuid;
    }

    public ResultProvenance withLastDetectionRunGuid(String lastDetectionRunGuid) {
        this.lastDetectionRunGuid = lastDetectionRunGuid;
        return this;
    }

    /**
     * The index within the run.invocations array of the invocation object which describes the tool invocation that detected the result.
     */
    public int getInvocationIndex() {
        return invocationIndex;
    }

    /**
     * The index within the run.invocations array of the invocation object which describes the tool invocation that detected the result.
     */
    public void setInvocationIndex(int invocationIndex) {
        this.invocationIndex = invocationIndex;
    }

    public ResultProvenance withInvocationIndex(int invocationIndex) {
        this.invocationIndex = invocationIndex;
        return this;
    }

    /**
     * An array of physicalLocation objects which specify the portions of an analysis tool's output that a converter transformed into the result.
     */
    public Set<PhysicalLocation> getConversionSources() {
        return conversionSources;
    }

    /**
     * An array of physicalLocation objects which specify the portions of an analysis tool's output that a converter transformed into the result.
     */
    public void setConversionSources(Set<PhysicalLocation> conversionSources) {
        this.conversionSources = conversionSources;
    }

    public ResultProvenance withConversionSources(Set<PhysicalLocation> conversionSources) {
        this.conversionSources = conversionSources;
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

    public ResultProvenance withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(ResultProvenance.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("firstDetectionTimeUtc");
        sb.append('=');
        sb.append(((this.firstDetectionTimeUtc == null) ? "<null>" : this.firstDetectionTimeUtc));
        sb.append(',');
        sb.append("lastDetectionTimeUtc");
        sb.append('=');
        sb.append(((this.lastDetectionTimeUtc == null) ? "<null>" : this.lastDetectionTimeUtc));
        sb.append(',');
        sb.append("firstDetectionRunGuid");
        sb.append('=');
        sb.append(((this.firstDetectionRunGuid == null) ? "<null>" : this.firstDetectionRunGuid));
        sb.append(',');
        sb.append("lastDetectionRunGuid");
        sb.append('=');
        sb.append(((this.lastDetectionRunGuid == null) ? "<null>" : this.lastDetectionRunGuid));
        sb.append(',');
        sb.append("invocationIndex");
        sb.append('=');
        sb.append(this.invocationIndex);
        sb.append(',');
        sb.append("conversionSources");
        sb.append('=');
        sb.append(((this.conversionSources == null) ? "<null>" : this.conversionSources));
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
        result = ((result * 31) + ((this.firstDetectionRunGuid == null) ? 0 : this.firstDetectionRunGuid.hashCode()));
        result = ((result * 31) + ((this.lastDetectionTimeUtc == null) ? 0 : this.lastDetectionTimeUtc.hashCode()));
        result = ((result * 31) + this.invocationIndex);
        result = ((result * 31) + ((this.lastDetectionRunGuid == null) ? 0 : this.lastDetectionRunGuid.hashCode()));
        result = ((result * 31) + ((this.conversionSources == null) ? 0 : this.conversionSources.hashCode()));
        result = ((result * 31) + ((this.firstDetectionTimeUtc == null) ? 0 : this.firstDetectionTimeUtc.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof ResultProvenance) == false) {
            return false;
        }
        ResultProvenance rhs = ((ResultProvenance) other);
        return ((((((((this.firstDetectionRunGuid == rhs.firstDetectionRunGuid) || ((this.firstDetectionRunGuid != null) && this.firstDetectionRunGuid.equals(rhs.firstDetectionRunGuid))) && ((this.lastDetectionTimeUtc == rhs.lastDetectionTimeUtc) || ((this.lastDetectionTimeUtc != null) && this.lastDetectionTimeUtc.equals(rhs.lastDetectionTimeUtc)))) && (this.invocationIndex == rhs.invocationIndex)) && ((this.lastDetectionRunGuid == rhs.lastDetectionRunGuid) || ((this.lastDetectionRunGuid != null) && this.lastDetectionRunGuid.equals(rhs.lastDetectionRunGuid)))) && ((this.conversionSources == rhs.conversionSources) || ((this.conversionSources != null) && this.conversionSources.equals(rhs.conversionSources)))) && ((this.firstDetectionTimeUtc == rhs.firstDetectionTimeUtc) || ((this.firstDetectionTimeUtc != null) && this.firstDetectionTimeUtc.equals(rhs.firstDetectionTimeUtc)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }

}
