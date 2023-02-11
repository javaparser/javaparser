
package com.github.jmlparser.lint.sarif;

import javax.annotation.processing.Generated;


/**
 * The artifact location specified by each uriBaseId symbol on the machine where the tool originally ran.
 */
@Generated("jsonschema2pojo")
public class OriginalUriBaseIds {


    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(OriginalUriBaseIds.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
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
        if ((other instanceof OriginalUriBaseIds) == false) {
            return false;
        }
        OriginalUriBaseIds rhs = ((OriginalUriBaseIds) other);
        return true;
    }

}
