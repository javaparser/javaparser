
package com.github.jmlparser.lint.sarif;

import java.net.URI;
import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * Provides additional metadata related to translation.
 */
@Generated("jsonschema2pojo")
public class TranslationMetadata {

    /**
     * The name associated with the translation metadata.
     * (Required)
     */
    @SerializedName("name")
    @Expose
    private String name;
    /**
     * The full name associated with the translation metadata.
     */
    @SerializedName("fullName")
    @Expose
    private String fullName;
    /**
     * A message string or message format string rendered in multiple formats.
     */
    @SerializedName("shortDescription")
    @Expose
    private MultiformatMessageString shortDescription;
    /**
     * A message string or message format string rendered in multiple formats.
     */
    @SerializedName("fullDescription")
    @Expose
    private MultiformatMessageString fullDescription;
    /**
     * The absolute URI from which the translation metadata can be downloaded.
     */
    @SerializedName("downloadUri")
    @Expose
    private URI downloadUri;
    /**
     * The absolute URI from which information related to the translation metadata can be downloaded.
     */
    @SerializedName("informationUri")
    @Expose
    private URI informationUri;
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public TranslationMetadata() {
    }

    /**
     * @param name
     * @param fullName
     * @param shortDescription
     * @param downloadUri
     * @param fullDescription
     * @param informationUri
     * @param properties
     */
    public TranslationMetadata(String name, String fullName, MultiformatMessageString shortDescription, MultiformatMessageString fullDescription, URI downloadUri, URI informationUri, PropertyBag properties) {
        super();
        this.name = name;
        this.fullName = fullName;
        this.shortDescription = shortDescription;
        this.fullDescription = fullDescription;
        this.downloadUri = downloadUri;
        this.informationUri = informationUri;
        this.properties = properties;
    }

    /**
     * The name associated with the translation metadata.
     * (Required)
     */
    public String getName() {
        return name;
    }

    /**
     * The name associated with the translation metadata.
     * (Required)
     */
    public void setName(String name) {
        this.name = name;
    }

    public TranslationMetadata withName(String name) {
        this.name = name;
        return this;
    }

    /**
     * The full name associated with the translation metadata.
     */
    public String getFullName() {
        return fullName;
    }

    /**
     * The full name associated with the translation metadata.
     */
    public void setFullName(String fullName) {
        this.fullName = fullName;
    }

    public TranslationMetadata withFullName(String fullName) {
        this.fullName = fullName;
        return this;
    }

    /**
     * A message string or message format string rendered in multiple formats.
     */
    public MultiformatMessageString getShortDescription() {
        return shortDescription;
    }

    /**
     * A message string or message format string rendered in multiple formats.
     */
    public void setShortDescription(MultiformatMessageString shortDescription) {
        this.shortDescription = shortDescription;
    }

    public TranslationMetadata withShortDescription(MultiformatMessageString shortDescription) {
        this.shortDescription = shortDescription;
        return this;
    }

    /**
     * A message string or message format string rendered in multiple formats.
     */
    public MultiformatMessageString getFullDescription() {
        return fullDescription;
    }

    /**
     * A message string or message format string rendered in multiple formats.
     */
    public void setFullDescription(MultiformatMessageString fullDescription) {
        this.fullDescription = fullDescription;
    }

    public TranslationMetadata withFullDescription(MultiformatMessageString fullDescription) {
        this.fullDescription = fullDescription;
        return this;
    }

    /**
     * The absolute URI from which the translation metadata can be downloaded.
     */
    public URI getDownloadUri() {
        return downloadUri;
    }

    /**
     * The absolute URI from which the translation metadata can be downloaded.
     */
    public void setDownloadUri(URI downloadUri) {
        this.downloadUri = downloadUri;
    }

    public TranslationMetadata withDownloadUri(URI downloadUri) {
        this.downloadUri = downloadUri;
        return this;
    }

    /**
     * The absolute URI from which information related to the translation metadata can be downloaded.
     */
    public URI getInformationUri() {
        return informationUri;
    }

    /**
     * The absolute URI from which information related to the translation metadata can be downloaded.
     */
    public void setInformationUri(URI informationUri) {
        this.informationUri = informationUri;
    }

    public TranslationMetadata withInformationUri(URI informationUri) {
        this.informationUri = informationUri;
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

    public TranslationMetadata withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(TranslationMetadata.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("name");
        sb.append('=');
        sb.append(((this.name == null) ? "<null>" : this.name));
        sb.append(',');
        sb.append("fullName");
        sb.append('=');
        sb.append(((this.fullName == null) ? "<null>" : this.fullName));
        sb.append(',');
        sb.append("shortDescription");
        sb.append('=');
        sb.append(((this.shortDescription == null) ? "<null>" : this.shortDescription));
        sb.append(',');
        sb.append("fullDescription");
        sb.append('=');
        sb.append(((this.fullDescription == null) ? "<null>" : this.fullDescription));
        sb.append(',');
        sb.append("downloadUri");
        sb.append('=');
        sb.append(((this.downloadUri == null) ? "<null>" : this.downloadUri));
        sb.append(',');
        sb.append("informationUri");
        sb.append('=');
        sb.append(((this.informationUri == null) ? "<null>" : this.informationUri));
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
        result = ((result * 31) + ((this.name == null) ? 0 : this.name.hashCode()));
        result = ((result * 31) + ((this.fullName == null) ? 0 : this.fullName.hashCode()));
        result = ((result * 31) + ((this.shortDescription == null) ? 0 : this.shortDescription.hashCode()));
        result = ((result * 31) + ((this.downloadUri == null) ? 0 : this.downloadUri.hashCode()));
        result = ((result * 31) + ((this.fullDescription == null) ? 0 : this.fullDescription.hashCode()));
        result = ((result * 31) + ((this.informationUri == null) ? 0 : this.informationUri.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof TranslationMetadata) == false) {
            return false;
        }
        TranslationMetadata rhs = ((TranslationMetadata) other);
        return ((((((((this.name == rhs.name) || ((this.name != null) && this.name.equals(rhs.name))) && ((this.fullName == rhs.fullName) || ((this.fullName != null) && this.fullName.equals(rhs.fullName)))) && ((this.shortDescription == rhs.shortDescription) || ((this.shortDescription != null) && this.shortDescription.equals(rhs.shortDescription)))) && ((this.downloadUri == rhs.downloadUri) || ((this.downloadUri != null) && this.downloadUri.equals(rhs.downloadUri)))) && ((this.fullDescription == rhs.fullDescription) || ((this.fullDescription != null) && this.fullDescription.equals(rhs.fullDescription)))) && ((this.informationUri == rhs.informationUri) || ((this.informationUri != null) && this.informationUri.equals(rhs.informationUri)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }

}
