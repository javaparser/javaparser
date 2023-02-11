
package com.github.jmlparser.lint.sarif;

import javax.annotation.processing.Generated;


/**
 * Values of relevant expressions at the start of the graph traversal that remain constant for the graph traversal.
 */
@Generated("jsonschema2pojo")
public class ImmutableState__1 {


    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(ImmutableState__1.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
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
        if ((other instanceof ImmutableState__1) == false) {
            return false;
        }
        ImmutableState__1 rhs = ((ImmutableState__1) other);
        return true;
    }

}
