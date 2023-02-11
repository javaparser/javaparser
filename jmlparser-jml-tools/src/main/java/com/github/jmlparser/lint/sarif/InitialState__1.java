
package com.github.jmlparser.lint.sarif;

import javax.annotation.processing.Generated;


/**
 * Values of relevant expressions at the start of the graph traversal that may change during graph traversal.
 */
@Generated("jsonschema2pojo")
public class InitialState__1 {


    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(InitialState__1.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
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
        if ((other instanceof InitialState__1) == false) {
            return false;
        }
        InitialState__1 rhs = ((InitialState__1) other);
        return true;
    }

}
