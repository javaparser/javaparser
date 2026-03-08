package com.github.javaparser.ast;

/**
 * A key to a piece of user data associated with a {@link Node} at runtime.
 * The key contains type information that can be used to check the
 * type of any user data value for the key when the value is set. UserDataKey is abstract in order to
 * force the creation of a subtype. That subtype is used to test for identity when looking for the
 * user data because actual object identity would suffer from problems under serialization.
 * So, the correct way to declare a UserDataKey is like this:
 *
 * <pre>
 * <code>
 * public static final UserDataKey&lt;Role&gt; ROLE = new UserDataKey&lt;Role&gt;() { };
 * </code>
 * </pre>
 *
 * This code was taken from the <a href="http://wicket.apache.org/">Wicket project</a>.
 *
 * @param <T>
 *            The type of the object which is stored
 *
 * @see Node#getUserData(UserDataKey)
 */
public abstract class UserDataKey<T> {
    @Override
    public int hashCode()
    {
        return getClass().hashCode();
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj)
    {
        return obj != null && getClass().equals(obj.getClass());
    }
}
