
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

| JEP | Status | JavaParser Since | Description |
| --- | --- | --- | --- |
| [JEP 181](https://openjdk.java.net/jeps/181) |    Release       | **????**                                                                      | Nest-Based Access Control                                         |
| [JEP 309](https://openjdk.java.net/jeps/309) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Dynamic Class-File Constants~~                                  |
| [JEP 315](https://openjdk.java.net/jeps/315) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Improve Aarch64 Intrinsics~~                                    |
| [JEP 318](https://openjdk.java.net/jeps/318) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Epsilon: A No-Op Garbage Collector~~                            |
| [JEP 320](https://openjdk.java.net/jeps/320) |  ~~Release~~     | ~~_NA_~~ - JavaParser needs no knowledge of available classes/packages        | ~~Remove the Java EE and CORBA Modules~~                          |
| [JEP 321](https://openjdk.java.net/jeps/321) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~HTTP Client (Standard)~~                                        |
| [JEP 323](https://openjdk.java.net/jeps/323) |    Release       | **v3.TBC [#TBC]()**                                                           | Local-Variable Syntax for Lambda Parameters                       |
| [JEP 324](https://openjdk.java.net/jeps/324) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Key Agreement with Curve25519 and Curve448~~                    |
| [JEP 327](https://openjdk.java.net/jeps/327) |  ~~Release~~     | **????**                                                                      | Unicode 10                                                        |
| [JEP 328](https://openjdk.java.net/jeps/328) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Flight Recorder~~                                               |
| [JEP 329](https://openjdk.java.net/jeps/329) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~ChaCha20 and Poly1305 Cryptographic Algorithms~~                |
| [JEP 330](https://openjdk.java.net/jeps/330) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Launch Single-File Source-Code Programs~~                       |
| [JEP 331](https://openjdk.java.net/jeps/331) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Low-Overhead Heap Profiling~~                                   |
| [JEP 332](https://openjdk.java.net/jeps/332) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Transport Layer Security (TLS) 1.3~~                            |
| [JEP 333](https://openjdk.java.net/jeps/333) | ~~Experimental~~ | ~~_NA_~~                                                                      | ~~ZGC: A Scalable Low-Latency Garbage Collector (Experimental)~~  |
| [JEP 335](https://openjdk.java.net/jeps/335) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Deprecate the Nashorn JavaScript Engine~~                       |
| [JEP 336](https://openjdk.java.net/jeps/336) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Deprecate the Pack200 Tools and API~~                           |

## JDK 12 - March 2019
Source: https://openjdk.java.net/projects/jdk/12/

| JEP | Status | JavaParser Since | Description |
| --- | --- | --- | --- |
| [JEP 189](https://openjdk.java.net/jeps/189) | ~~Experimental~~ | ~~_NA_~~                                                                      | ~~Shenandoah: A Low-Pause-Time Garbage Collector (Experimental)~~ |
| [JEP 230](https://openjdk.java.net/jeps/230) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Microbenchmark Suite~~                                          |
| [JEP 325](https://openjdk.java.net/jeps/325) |  _Preview_       | **v3.TBC [#TBC]()**                                                           | Switch Expressions (Preview)                                      |
| [JEP 334](https://openjdk.java.net/jeps/334) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~JVM Constants API~~                                             |
| [JEP 340](https://openjdk.java.net/jeps/340) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~One AArch64 Port, Not Two~~                                     |
| [JEP 341](https://openjdk.java.net/jeps/341) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Default CDS Archives~~                                          |
| [JEP 344](https://openjdk.java.net/jeps/344) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Abortable Mixed Collections for G1~~                            |
| [JEP 346](https://openjdk.java.net/jeps/346) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Promptly Return Unused Committed Memory from G1~~               |

## JDK 13 - September 2018
Source: https://openjdk.java.net/projects/jdk/13/

| JEP | Status | JavaParser Since | Description |
| --- | --- | --- | --- |
| [JEP 350](https://openjdk.java.net/jeps/350) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Dynamic CDS Archives~~                                        |
| [JEP 351](https://openjdk.java.net/jeps/351) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~ZGC: Uncommit Unused Memory~~                                 |
| [JEP 353](https://openjdk.java.net/jeps/353) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Reimplement the Legacy Socket API~~                           |
| [JEP 354](https://openjdk.java.net/jeps/354) |  _Preview_       | **v3.TBC [#TBC]()**                                                           | Switch Expressions (Preview)                                    |
| [JEP 355](https://openjdk.java.net/jeps/355) |  _Preview_       | **v3.TBC [#TBC]()**                                                           | Text Blocks (Preview)                                           |



## JDK 14 (current) - March 2020
Source: https://openjdk.java.net/projects/jdk/14/

| JEP | Status | JavaParser Since | Description |
| --- | --- | --- | --- |
| [JEP 305](https://openjdk.java.net/jeps/305) |  _Preview_       | **WIP - [#2512](https://github.com/javaparser/javaparser/pull/2512)**         | Pattern Matching for instanceof (Preview)                       |
| [JEP 343](https://openjdk.java.net/jeps/343) |  _Incubator_     | ~~_NA_~~                                                                      | ~~Packaging Tool (Incubator)~~                                  |
| [JEP 345](https://openjdk.java.net/jeps/345) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~NUMA-Aware Memory Allocation for G1~~                         |
| [JEP 349](https://openjdk.java.net/jeps/349) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~JFR Event Streaming~~                                         |
| [JEP 352](https://openjdk.java.net/jeps/352) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Non-Volatile Mapped Byte Buffers~~                            |
| [JEP 358](https://openjdk.java.net/jeps/358) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Helpful NullPointerExceptions~~                               |
| [JEP 359](https://openjdk.java.net/jeps/359) |  _Preview_       | **WIP - [#2654](https://github.com/javaparser/javaparser/pull/2654)**         | Records (Preview)                                               |
| [JEP 361](https://openjdk.java.net/jeps/361) |   Release        | **TBC**                                                                       | Switch Expressions (Standard)                                   |
| [JEP 362](https://openjdk.java.net/jeps/362) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Deprecate the Solaris and SPARC Ports~~                       |
| [JEP 363](https://openjdk.java.net/jeps/363) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Remove the Concurrent Mark Sweep (CMS) Garbage Collector~~    |
| [JEP 364](https://openjdk.java.net/jeps/364) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~ZGC on macOS~~                                                |
| [JEP 365](https://openjdk.java.net/jeps/365) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~ZGC on Windows~~                                              |
| [JEP 366](https://openjdk.java.net/jeps/366) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Deprecate the ParallelScavenge + SerialOld GC Combination~~   |
| [JEP 367](https://openjdk.java.net/jeps/367) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Remove the Pack200 Tools and API~~                            |
| [JEP 368](https://openjdk.java.net/jeps/368) |   Release        | **v3.TBC [#TBC]()**                                                           | Text Blocks (Second Preview)                                    |
| [JEP 370](https://openjdk.java.net/jeps/370) |  ~~Release~~     | ~~_NA_~~                                                                      | ~~Foreign-Memory Access API (Incubator)~~                       |

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
