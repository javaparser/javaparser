
package com.github.jmlparser.lint.sarif;

import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * An area within an image.
 */
@Generated("jsonschema2pojo")
public class Rectangle {

    /**
     * The Y coordinate of the top edge of the rectangle, measured in the image's natural units.
     */
    @SerializedName("top")
    @Expose
    private double top;
    /**
     * The X coordinate of the left edge of the rectangle, measured in the image's natural units.
     */
    @SerializedName("left")
    @Expose
    private double left;
    /**
     * The Y coordinate of the bottom edge of the rectangle, measured in the image's natural units.
     */
    @SerializedName("bottom")
    @Expose
    private double bottom;
    /**
     * The X coordinate of the right edge of the rectangle, measured in the image's natural units.
     */
    @SerializedName("right")
    @Expose
    private double right;
    /**
     * Encapsulates a message intended to be read by the end user.
     */
    @SerializedName("message")
    @Expose
    private Message message;
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public Rectangle() {
    }

    /**
     * @param top
     * @param left
     * @param bottom
     * @param right
     * @param message
     * @param properties
     */
    public Rectangle(double top, double left, double bottom, double right, Message message, PropertyBag properties) {
        super();
        this.top = top;
        this.left = left;
        this.bottom = bottom;
        this.right = right;
        this.message = message;
        this.properties = properties;
    }

    /**
     * The Y coordinate of the top edge of the rectangle, measured in the image's natural units.
     */
    public double getTop() {
        return top;
    }

    /**
     * The Y coordinate of the top edge of the rectangle, measured in the image's natural units.
     */
    public void setTop(double top) {
        this.top = top;
    }

    public Rectangle withTop(double top) {
        this.top = top;
        return this;
    }

    /**
     * The X coordinate of the left edge of the rectangle, measured in the image's natural units.
     */
    public double getLeft() {
        return left;
    }

    /**
     * The X coordinate of the left edge of the rectangle, measured in the image's natural units.
     */
    public void setLeft(double left) {
        this.left = left;
    }

    public Rectangle withLeft(double left) {
        this.left = left;
        return this;
    }

    /**
     * The Y coordinate of the bottom edge of the rectangle, measured in the image's natural units.
     */
    public double getBottom() {
        return bottom;
    }

    /**
     * The Y coordinate of the bottom edge of the rectangle, measured in the image's natural units.
     */
    public void setBottom(double bottom) {
        this.bottom = bottom;
    }

    public Rectangle withBottom(double bottom) {
        this.bottom = bottom;
        return this;
    }

    /**
     * The X coordinate of the right edge of the rectangle, measured in the image's natural units.
     */
    public double getRight() {
        return right;
    }

    /**
     * The X coordinate of the right edge of the rectangle, measured in the image's natural units.
     */
    public void setRight(double right) {
        this.right = right;
    }

    public Rectangle withRight(double right) {
        this.right = right;
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

    public Rectangle withMessage(Message message) {
        this.message = message;
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

    public Rectangle withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(Rectangle.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("top");
        sb.append('=');
        sb.append(this.top);
        sb.append(',');
        sb.append("left");
        sb.append('=');
        sb.append(this.left);
        sb.append(',');
        sb.append("bottom");
        sb.append('=');
        sb.append(this.bottom);
        sb.append(',');
        sb.append("right");
        sb.append('=');
        sb.append(this.right);
        sb.append(',');
        sb.append("message");
        sb.append('=');
        sb.append(((this.message == null) ? "<null>" : this.message));
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
        result = ((result * 31) + ((int) (Double.doubleToLongBits(this.right) ^ (Double.doubleToLongBits(this.right) >>> 32))));
        result = ((result * 31) + ((int) (Double.doubleToLongBits(this.top) ^ (Double.doubleToLongBits(this.top) >>> 32))));
        result = ((result * 31) + ((this.message == null) ? 0 : this.message.hashCode()));
        result = ((result * 31) + ((int) (Double.doubleToLongBits(this.left) ^ (Double.doubleToLongBits(this.left) >>> 32))));
        result = ((result * 31) + ((int) (Double.doubleToLongBits(this.bottom) ^ (Double.doubleToLongBits(this.bottom) >>> 32))));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof Rectangle) == false) {
            return false;
        }
        Rectangle rhs = ((Rectangle) other);
        return ((((((Double.doubleToLongBits(this.right) == Double.doubleToLongBits(rhs.right)) && (Double.doubleToLongBits(this.top) == Double.doubleToLongBits(rhs.top))) && ((this.message == rhs.message) || ((this.message != null) && this.message.equals(rhs.message)))) && (Double.doubleToLongBits(this.left) == Double.doubleToLongBits(rhs.left))) && (Double.doubleToLongBits(this.bottom) == Double.doubleToLongBits(rhs.bottom))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }

}
