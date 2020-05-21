
# Features

## JDK 1.1 - January 1996
## JDK 1.2 - February 1997
## JDK 1.3 - December 1998
## JDK 1.4 - May 2000
## JDK 5 - February 2002
Source: https://en.wikipedia.org/wiki/Java_version_history#J2SE_5.0
## JDK 6 - September 2004
Source: https://en.wikipedia.org/wiki/Java_version_history#Java_SE_6

## JDK 7 - July 2011
Source: https://en.wikipedia.org/wiki/Java_version_history#Java_SE_7


## JDK 8 - March 2014
Source: https://en.wikipedia.org/wiki/Java_version_history#Java_SE_8

- JSR 335, JEP 126: Language-level support for lambda expressions (officially, lambda expressions; unofficially, closures) under Project Lambda and default methods (virtual extension methods) which allow the addition of methods to interfaces without breaking existing implementations. There was an ongoing debate in the Java community on whether to add support for lambda expressions. Sun later declared that lambda expressions would be included in Java and asked for community input to refine the feature. Supporting lambda expressions also enables functional-style operations on streams of elements, such as MapReduce-inspired transformations on collections. Default methods allow an author of an API to add new methods to an interface without breaking the old code using it. Although it was not their primary intent, default methods also allow multiple inheritance of behavior (but not state).
- JSR 223, JEP 174: Project Nashorn, a JavaScript runtime which allows developers to embed JavaScript code within applications
- JSR 308, JEP 104: Annotation on Java types, Unsigned integer arithmetic
- JSR 337, JEP 120: Repeating annotations
- JSR 310, JEP 150: Date and time API
- JEP 178: Statically-linked JNI libraries
- JEP 153: Launch JavaFX applications (direct launching of JavaFX application JARs)
- JEP 122: Remove the permanent generation

## JDK 9 - September 2017
Source: https://en.wikipedia.org/wiki/Java_version_history#Java_SE_9

- JSR 376: Modularization of the JDK under Project Jigsaw (Java Platform Module System)
- JEP 222: JShell: The Java Shell (a Java REPL)
- JEP 295: Ahead-of-time compilation
- JEP 268: XML catalogs
- JEP 266: More concurrency updates. It includes a Java implementation of Reactive Streams, including a new Flow class that included the interfaces previously provided by Reactive Streams
- JEP 193: Variable handles: define a standard means to invoke the equivalents of various java.util.concurrent.atomic and sun.misc.Unsafe operations
- JEP 282: jlink: The Java Linker: create a tool that can assemble and optimize a set of modules and their dependencies into a custom run-time image. It effectively allows to produce a fully usable executable including the JVM to run it. JavaDB was removed from JDK
- JEP 263: HiDPI graphics: automatic scaling and sizing
- JEP 254: Compact Strings
- JEP 213: Milling Project Coin

## JDK 10 - March 2018
Source: https://openjdk.java.net/projects/jdk/10/

- 286: Local-Variable Type Inference
- 296: Consolidate the JDK Forest into a Single Repository
- 304: Garbage-Collector Interface
- 307: Parallel Full GC for G1
- 310: Application Class-Data Sharing
- 312: Thread-Local Handshakes
- 313: Remove the Native-Header Generation Tool (javah)
- 314: Additional Unicode Language-Tag Extensions
- 316: Heap Allocation on Alternative Memory Devices
- 317: Experimental Java-Based JIT Compiler
- 319: Root Certificates
- 322: Time-Based Release Versioning

## JDK 11 - September 2018
Source: https://openjdk.java.net/projects/jdk/11/

- JEP 181: Nest-Based Access Control
- JEP 309: Dynamic Class-File Constants
- JEP 315: Improve Aarch64 Intrinsics
- JEP 318: Epsilon: A No-Op Garbage Collector
- JEP 320: Remove the Java EE and CORBA Modules
- JEP 321: HTTP Client (Standard)
- JEP 323: Local-Variable Syntax for Lambda Parameters
- JEP 324: Key Agreement with Curve25519 and Curve448
- JEP 327: Unicode 10
- JEP 328: Flight Recorder
- JEP 329: ChaCha20 and Poly1305 Cryptographic Algorithms
- JEP 330: Launch Single-File Source-Code Programs
- JEP 331: Low-Overhead Heap Profiling
- JEP 332: Transport Layer Security (TLS) 1.3
- JEP 333: ZGC: A Scalable Low-Latency Garbage Collector (Experimental)
- JEP 335: Deprecate the Nashorn JavaScript Engine
- JEP 336: Deprecate the Pack200 Tools and API

## JDK 12 - March 2019
Source: https://openjdk.java.net/projects/jdk/12/

- JEP 189: Shenandoah: A Low-Pause-Time Garbage Collector (Experimental)
- JEP 230: Microbenchmark Suite
- JEP 325: Switch Expressions (Preview)
- JEP 334: JVM Constants API
- JEP 340: One AArch64 Port, Not Two
- JEP 341: Default CDS Archives
- JEP 344: Abortable Mixed Collections for G1
- JEP 346: Promptly Return Unused Committed Memory from G1

## JDK 13 - September 2018
Source: https://openjdk.java.net/projects/jdk/13/

- JEP 350: Dynamic CDS Archives
- JEP 351: ZGC: Uncommit Unused Memory
- JEP 353: Reimplement the Legacy Socket API
- JEP 354: Switch Expressions (Preview)
- JEP 355: Text Blocks (Preview)

## JDK 14 (current) - March 2020
Source: https://openjdk.java.net/projects/jdk/14/

- JEP 305: Pattern Matching for instanceof (Preview)
- JEP 343: Packaging Tool (Incubator)
- JEP 345: NUMA-Aware Memory Allocation for G1
- JEP 349: JFR Event Streaming
- JEP 352: Non-Volatile Mapped Byte Buffers
- JEP 358: Helpful NullPointerExceptions
- JEP 359: Records (Preview)
- JEP 361: Switch Expressions (Standard)
- JEP 362: Deprecate the Solaris and SPARC Ports
- JEP 363: Remove the Concurrent Mark Sweep (CMS) Garbage Collector
- JEP 364: ZGC on macOS
- JEP 365: ZGC on Windows
- JEP 366: Deprecate the ParallelScavenge + SerialOld GC Combination
- JEP 367: Remove the Pack200 Tools and API
- JEP 368: Text Blocks (Second Preview)
- JEP 370: Foreign-Memory Access API (Incubator)

## JDK 15 - _targeted for September 2020_
Source: https://openjdk.java.net/projects/jdk/15/

#### JEPs proposed to target JDK 15 review ends
- 383: Foreign-Memory Access API (Second Incubator) 2020/05/21

#### JEPs targeted to JDK 15, so far
- JEP 339: Edwards-Curve Digital Signature Algorithm (EdDSA)
- JEP 360: Sealed Classes (Preview)
- JEP 371: Hidden Classes
- JEP 372: Remove the Nashorn JavaScript Engine
- JEP 373: Reimplement the Legacy DatagramSocket API
- JEP 374: Disable and Deprecate Biased Locking
- JEP 375: Pattern Matching for instanceof (Second Preview)
- JEP 377: ZGC: A Scalable Low-Latency Garbage Collector
- JEP 378: Text Blocks
- JEP 379: Shenandoah: A Low-Pause-Time Garbage Collector
- JEP 381: Remove the Solaris and SPARC Ports
- JEP 384: Records (Second Preview)

## JDK 16 - _targeted for March 2021_

## JDK 17 - _targeted for September 2021_
