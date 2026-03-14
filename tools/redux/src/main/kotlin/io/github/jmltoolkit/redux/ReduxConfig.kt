package io.github.jmltoolkit.redux


/**
 * Configuration for the Redux transformation pipeline.
 */
class ReduxConfig {
    private val disabled: MutableSet<String> = HashSet()

    fun enable(clazz: Class<*>) {
        disabled.remove(clazz.toString())
    }

    fun disable(clazz: Class<*>) {
        disabled.add(clazz.toString())
    }

    fun getDisabled(): Set<String> {
        return disabled
    }

    fun isEnabled(clazz: String): Boolean {
        return !disabled.contains(clazz)
    }
}