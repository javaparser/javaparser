
package com.github.jmlparser.lint.sarif;

import javax.annotation.processing.Generated;


/**
 * A set of strings each of which individually defines a stable, unique identity for the result.
 */
@Generated("jsonschema2pojo")
public class Fingerprints {


    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(Fingerprints.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
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
        if ((other instanceof Fingerprints) == false) {
            return false;
        }
        Fingerprints rhs = ((Fingerprints) other);
        return true;
    }

}
