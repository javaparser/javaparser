
package com.github.jmlparser.lint.sarif;

import javax.annotation.processing.Generated;


/**
 * A set of name/value pairs with arbitrary names. Each value is a multiformatMessageString object, which holds message strings in plain text and (optionally) Markdown format. The strings can include placeholders, which can be used to construct a message in combination with an arbitrary number of additional string arguments.
 */
@Generated("jsonschema2pojo")
public class MessageStrings {


    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(MessageStrings.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
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
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof MessageStrings) == false) {
            return false;
        }
        MessageStrings rhs = ((MessageStrings) other);
        return true;
    }

}
