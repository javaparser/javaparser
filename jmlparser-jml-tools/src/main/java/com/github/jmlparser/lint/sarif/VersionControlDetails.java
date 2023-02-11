
package com.github.jmlparser.lint.sarif;

import java.net.URI;
import java.util.Date;
import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * Specifies the information necessary to retrieve a desired revision from a version control system.
 */
@Generated("jsonschema2pojo")
public class VersionControlDetails {

    /**
     * The absolute URI of the repository.
     * (Required)
     */
    @SerializedName("repositoryUri")
    @Expose
    private URI repositoryUri;
    /**
     * A string that uniquely and permanently identifies the revision within the repository.
     */
    @SerializedName("revisionId")
    @Expose
    private String revisionId;
    /**
     * The name of a branch containing the revision.
     */
    @SerializedName("branch")
    @Expose
    private String branch;
    /**
     * A tag that has been applied to the revision.
     */
    @SerializedName("revisionTag")
    @Expose
    private String revisionTag;
    /**
     * A Coordinated Universal Time (UTC) date and time that can be used to synchronize an enlistment to the state of the repository at that time.
     */
    @SerializedName("asOfTimeUtc")
    @Expose
    private Date asOfTimeUtc;
    /**
     * Specifies the location of an artifact.
     */
    @SerializedName("mappedTo")
    @Expose
    private ArtifactLocation mappedTo;
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public VersionControlDetails() {
    }

    /**
     * @param revisionId
     * @param repositoryUri
     * @param mappedTo
     * @param branch
     * @param asOfTimeUtc
     * @param properties
     * @param revisionTag
     */
    public VersionControlDetails(URI repositoryUri, String revisionId, String branch, String revisionTag, Date asOfTimeUtc, ArtifactLocation mappedTo, PropertyBag properties) {
        super();
        this.repositoryUri = repositoryUri;
        this.revisionId = revisionId;
        this.branch = branch;
        this.revisionTag = revisionTag;
        this.asOfTimeUtc = asOfTimeUtc;
        this.mappedTo = mappedTo;
        this.properties = properties;
    }

    /**
     * The absolute URI of the repository.
     * (Required)
     */
    public URI getRepositoryUri() {
        return repositoryUri;
    }

    /**
     * The absolute URI of the repository.
     * (Required)
     */
    public void setRepositoryUri(URI repositoryUri) {
        this.repositoryUri = repositoryUri;
    }

    public VersionControlDetails withRepositoryUri(URI repositoryUri) {
        this.repositoryUri = repositoryUri;
        return this;
    }

    /**
     * A string that uniquely and permanently identifies the revision within the repository.
     */
    public String getRevisionId() {
        return revisionId;
    }

    /**
     * A string that uniquely and permanently identifies the revision within the repository.
     */
    public void setRevisionId(String revisionId) {
        this.revisionId = revisionId;
    }

    public VersionControlDetails withRevisionId(String revisionId) {
        this.revisionId = revisionId;
        return this;
    }

    /**
     * The name of a branch containing the revision.
     */
    public String getBranch() {
        return branch;
    }

    /**
     * The name of a branch containing the revision.
     */
    public void setBranch(String branch) {
        this.branch = branch;
    }

    public VersionControlDetails withBranch(String branch) {
        this.branch = branch;
        return this;
    }

    /**
     * A tag that has been applied to the revision.
     */
    public String getRevisionTag() {
        return revisionTag;
    }

    /**
     * A tag that has been applied to the revision.
     */
    public void setRevisionTag(String revisionTag) {
        this.revisionTag = revisionTag;
    }

    public VersionControlDetails withRevisionTag(String revisionTag) {
        this.revisionTag = revisionTag;
        return this;
    }

    /**
     * A Coordinated Universal Time (UTC) date and time that can be used to synchronize an enlistment to the state of the repository at that time.
     */
    public Date getAsOfTimeUtc() {
        return asOfTimeUtc;
    }

    /**
     * A Coordinated Universal Time (UTC) date and time that can be used to synchronize an enlistment to the state of the repository at that time.
     */
    public void setAsOfTimeUtc(Date asOfTimeUtc) {
        this.asOfTimeUtc = asOfTimeUtc;
    }

    public VersionControlDetails withAsOfTimeUtc(Date asOfTimeUtc) {
        this.asOfTimeUtc = asOfTimeUtc;
        return this;
    }

    /**
     * Specifies the location of an artifact.
     */
    public ArtifactLocation getMappedTo() {
        return mappedTo;
    }

    /**
     * Specifies the location of an artifact.
     */
    public void setMappedTo(ArtifactLocation mappedTo) {
        this.mappedTo = mappedTo;
    }

    public VersionControlDetails withMappedTo(ArtifactLocation mappedTo) {
        this.mappedTo = mappedTo;
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

    public VersionControlDetails withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(VersionControlDetails.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("repositoryUri");
        sb.append('=');
        sb.append(((this.repositoryUri == null) ? "<null>" : this.repositoryUri));
        sb.append(',');
        sb.append("revisionId");
        sb.append('=');
        sb.append(((this.revisionId == null) ? "<null>" : this.revisionId));
        sb.append(',');
        sb.append("branch");
        sb.append('=');
        sb.append(((this.branch == null) ? "<null>" : this.branch));
        sb.append(',');
        sb.append("revisionTag");
        sb.append('=');
        sb.append(((this.revisionTag == null) ? "<null>" : this.revisionTag));
        sb.append(',');
        sb.append("asOfTimeUtc");
        sb.append('=');
        sb.append(((this.asOfTimeUtc == null) ? "<null>" : this.asOfTimeUtc));
        sb.append(',');
        sb.append("mappedTo");
        sb.append('=');
        sb.append(((this.mappedTo == null) ? "<null>" : this.mappedTo));
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
        result = ((result * 31) + ((this.revisionId == null) ? 0 : this.revisionId.hashCode()));
        result = ((result * 31) + ((this.repositoryUri == null) ? 0 : this.repositoryUri.hashCode()));
        result = ((result * 31) + ((this.mappedTo == null) ? 0 : this.mappedTo.hashCode()));
        result = ((result * 31) + ((this.branch == null) ? 0 : this.branch.hashCode()));
        result = ((result * 31) + ((this.asOfTimeUtc == null) ? 0 : this.asOfTimeUtc.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        result = ((result * 31) + ((this.revisionTag == null) ? 0 : this.revisionTag.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof VersionControlDetails) == false) {
            return false;
        }
        VersionControlDetails rhs = ((VersionControlDetails) other);
        return ((((((((this.revisionId == rhs.revisionId) || ((this.revisionId != null) && this.revisionId.equals(rhs.revisionId))) && ((this.repositoryUri == rhs.repositoryUri) || ((this.repositoryUri != null) && this.repositoryUri.equals(rhs.repositoryUri)))) && ((this.mappedTo == rhs.mappedTo) || ((this.mappedTo != null) && this.mappedTo.equals(rhs.mappedTo)))) && ((this.branch == rhs.branch) || ((this.branch != null) && this.branch.equals(rhs.branch)))) && ((this.asOfTimeUtc == rhs.asOfTimeUtc) || ((this.asOfTimeUtc != null) && this.asOfTimeUtc.equals(rhs.asOfTimeUtc)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties)))) && ((this.revisionTag == rhs.revisionTag) || ((this.revisionTag != null) && this.revisionTag.equals(rhs.revisionTag))));
    }

}
