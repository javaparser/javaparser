package org.apache.commons.lang3;

/**
 * <p>Operations on arrays, primitive arrays (like {@code int[]}) and
 * primitive wrapper arrays (like {@code Integer[]}).
 * <p>
 * <p>This class tries to handle {@code null} input gracefully.
 * An exception will not be thrown for a {@code null}
 * array input. However, an Object array that contains a {@code null}
 * element may throw an exception. Each method documents its behaviour.
 * <p>
 * <p>#ThreadSafe#
 *
 * @since 2.0
 */
public class ArrayUtils {

    /**
     * <p>Shallow clones an array returning a typecast result and handling
     * {@code null}.
     * <p>
     * <p>The objects in the array are not cloned, thus there is no special
     * handling for multi-dimensional arrays.
     * <p>
     * <p>This method returns {@code null} for a {@code null} input array.
     *
     * @param <T> the component type of the array
     * @param array the array to shallow clone, may be {@code null}
     * @return the cloned array, {@code null} if {@code null} input
     */
    public static <T> T[] clone(final T[] array) {
        if (array == null) {
            return null;
        }
        return array.clone();
    }

}
