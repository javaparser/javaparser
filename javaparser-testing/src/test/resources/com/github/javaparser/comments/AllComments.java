// Dangling(0) []

// Leading(0) []
package com.acme;

// Dangling(1) []

// Leading(0) [1]
import java.util.List; // Trailing(0) [1]

// Dangling(2) []
// Dangling(3) []


// Dangling(4) []

// Leading(0) [2]
public /* Dangling(0) [2] */ class TestClass {
    // Dangling(1) [2]

    // Leading(0) [2.0]
    // Leading(1) [2.0]
    public static String /* Dangling(0) [2.0] */ method1(/* Leading(0) [2.0.1] */ List<String> /* Leading(0) [2.0.1.0] */ strings) {
        StringBuilder buffer = new StringBuilder(); // Trailing(0) [2.0.2.0]
        // Leading(0) [2.0.2.1]
        for (String string /* Dangling(0) [2.0.2.1] */ : strings) /* Leading(0) [2.0.2.1.2] */ { // Leading(0) [2.0.2.1.2.0]
            // Leading(1) [2.0.2.1.2.0]
            /* Leading(2) [2.0.2.1.2.0] */ buffer.append(string); // Trailing(0) [2.0.2.1.2.0]
        } // Trailing(0) [2.0.2.1]
        return buffer.toString(); // Trailing(0) [2.0.2.2]
    } // Trailing(0) [2.0]

    // Dangling(2) [2]
} // Trailing(0) [2]
