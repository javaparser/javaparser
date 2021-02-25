package jml;

import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.Collections;
import java.util.Set;
import java.util.TreeSet;

/**
 * This class represents Jml annotation/classes on a Jml comment.
 * <p>
 * Jml annotations are tags, which are either enable or disabled on a Jml comment.
 * They are used to tag a comment for a specific tool or feature.
 *
 * @author Alexander Weigl
 * @version 1 (2/2/20)
 * @see jml.services.IJmlTagger
 */
public class JmlAnnotations {
    private @Nullable Set<String> set = null;

    public JmlAnnotations() {
    }

    public JmlAnnotations(@Nullable Set<String> set) {
        if (set != null && !set.isEmpty()) {
            this.set = new TreeSet<>(set);
        }
    }

    /**
     * @param tag
     */
    public void remove(String tag) {
        if (set == null) return;
        String stripped = stripTag(tag);
        set.remove("+" + stripped);
        set.remove("-" + stripped);
    }

    private @NotNull String stripTag(@NotNull String tag) {
        return (tag.charAt(0) == '-' || tag.charAt(0) == '+')
                ? tag.substring(1) : tag;
    }

    public void enable(String tag) {
        final String t = stripTag(tag);
        if (set == null) {
            set = new TreeSet<>();
        } else {
            set.remove("-" + t);
        }
        set.add("+" + t);
    }

    public void disable(String tag) {
        final String t = stripTag(tag);
        if (set == null) {
            set = new TreeSet<>();
        } else {
            set.remove("+" + t);
        }
        set.add("-" + t);

    }

    public Set<String> getTags() {
        return Collections.unmodifiableSet(set);
    }
}
