
# Features
This page describes the changes introduced within each version.

Language-related changes should normally have a validator, used in conjunction with the grammar, as part of the parsing process.

Where a change is not a language-related change _(e.g. JVM and garbage collection changes)_, this is marked as "Not Applicable (NA)".

## JDK 1.0 - January 1996
Source: https://en.wikipedia.org/wiki/Java_version_history#JDK_1.0
## JDK 1.1 - February 1997
Source: https://en.wikipedia.org/wiki/Java_version_history#JDK_1.1
## JDK 1.2 - December 1998
Source: https://en.wikipedia.org/wiki/Java_version_history#J2SE_1.2
## JDK 1.3 - May 2000
Source: https://en.wikipedia.org/wiki/Java_version_history#J2SE_1.3
## JDK 1.4 - February 2002
Source: https://en.wikipedia.org/wiki/Java_version_history#J2SE_1.4
## JDK 5 - September 2004
Source: https://en.wikipedia.org/wiki/Java_version_history#J2SE_5.0
## JDK 6 - December 2006
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

Java 10 support [complete on 25/Feb/2018](https://github.com/javaparser/javaparser/blob/master/changelog.md#version-3515)

|                     JEP                      |      Status      |                        JavaParser Since                         | Description                                             |
|:--------------------------------------------:|:----------------:|:---------------------------------------------------------------:|---------------------------------------------------------|
| [JEP 286](https://openjdk.java.net/jeps/286) |   **Release**    |    **Supported Since: v3.5.15<br>Released on: 25/Feb/2018**     | **Local-Variable Type Inference**                       |
| [JEP 296](https://openjdk.java.net/jeps/296) |  ~~_Release_~~   | ~~_Not Applicable - Not a language specification change (NA)_~~ | ~~Consolidate the JDK Forest into a Single Repository~~ |
| [JEP 304](https://openjdk.java.net/jeps/304) |  ~~_Release_~~   | ~~_Not Applicable - Not a language specification change (NA)_~~ | ~~Garbage-Collector Interface~~                         |
| [JEP 307](https://openjdk.java.net/jeps/307) |  ~~_Release_~~   | ~~_Not Applicable - Not a language specification change (NA)_~~ | ~~Parallel Full GC for G1~~                             |
| [JEP 310](https://openjdk.java.net/jeps/310) |  ~~_Release_~~   | ~~_Not Applicable - Not a language specification change (NA)_~~ | ~~Application Class-Data Sharing~~                      |
| [JEP 312](https://openjdk.java.net/jeps/312) |  ~~_Release_~~   | ~~_Not Applicable - Not a language specification change (NA)_~~ | ~~Thread-Local Handshakes~~                             |
| [JEP 313](https://openjdk.java.net/jeps/313) |  ~~_Release_~~   | ~~_Not Applicable - Not a language specification change (NA)_~~ | ~~Remove the Native-Header Generation Tool (javah)~~    |
| [JEP 314](https://openjdk.java.net/jeps/314) |  ~~_Release_~~   | ~~_Not Applicable - Not a language specification change (NA)_~~ | ~~Additional Unicode Language-Tag Extensions~~          |
| [JEP 316](https://openjdk.java.net/jeps/316) |  ~~_Release_~~   | ~~_Not Applicable - Not a language specification change (NA)_~~ | ~~Heap Allocation on Alternative Memory Devices~~       |
| [JEP 317](https://openjdk.java.net/jeps/317) | ~~Experimental~~ | ~~_Not Applicable - Not a language specification change (NA)_~~ | ~~Experimental Java-Based JIT Compiler~~                |
| [JEP 319](https://openjdk.java.net/jeps/319) |  ~~_Release_~~   | ~~_Not Applicable - Not a language specification change (NA)_~~ | ~~Root Certificates~~                                   |
| [JEP 322](https://openjdk.java.net/jeps/322) |  ~~_Release_~~   | ~~_Not Applicable - Not a language specification change (NA)_~~ | ~~Time-Based Release Versioning~~                       |

## JDK 11 - September 2018
Source: https://openjdk.java.net/projects/jdk/11/

Java 11 support [complete on 19/Aug/2018](https://github.com/javaparser/javaparser/blob/master/changelog.md#version-3618)

|                     JEP                      |      Status      |                                           JavaParser Since                                           | Description                                                      |
|:--------------------------------------------:|:----------------:|:----------------------------------------------------------------------------------------------------:|------------------------------------------------------------------|
| [JEP 323](https://openjdk.java.net/jeps/323) |   **Release**    |                      **Supported Since: v3.xx.yy<br>Released on: dd/mmm/yyyy**                       | **Local-Variable Syntax for Lambda Parameters**                  |
| [JEP 327](https://openjdk.java.net/jeps/327) |    _Release_     |                _Discussion Needed <sup id="a_11_JEP327">[JEP327](#f_11_JEP327)</sup>_                | _Unicode 10_                                                     |
| [JEP 181](https://openjdk.java.net/jeps/181) |    _Release_     |                _Discussion Needed <sup id="a_11_JEP181">[JEP181](#f_11_JEP181)</sup>_                | _Nest-Based Access Control_                                      |
| [JEP 309](https://openjdk.java.net/jeps/309) |  ~~_Release_~~   |                   ~~_Not Applicable - Not a language specification change (NA)_~~                    | ~~Dynamic Class-File Constants~~                                 |
| [JEP 315](https://openjdk.java.net/jeps/315) |  ~~_Release_~~   |                   ~~_Not Applicable - Not a language specification change (NA)_~~                    | ~~Improve Aarch64 Intrinsics~~                                   |
| [JEP 318](https://openjdk.java.net/jeps/318) |  ~~_Release_~~   |                   ~~_Not Applicable - Not a language specification change (NA)_~~                    | ~~Epsilon: A No-Op Garbage Collector~~                           |
| [JEP 320](https://openjdk.java.net/jeps/320) |  ~~_Release_~~   | ~~_Not Applicable - Not a language change (NA) <sup id="a_11_JEP320">[JEP320](#f_11_JEP320)</sup>_~~ | ~~Remove the Java EE and CORBA Modules~~                         |
| [JEP 321](https://openjdk.java.net/jeps/321) |  ~~_Release_~~   |                   ~~_Not Applicable - Not a language specification change (NA)_~~                    | ~~HTTP Client (Standard)~~                                       |
| [JEP 324](https://openjdk.java.net/jeps/324) |  ~~_Release_~~   |                   ~~_Not Applicable - Not a language specification change (NA)_~~                    | ~~Key Agreement with Curve25519 and Curve448~~                   |
| [JEP 328](https://openjdk.java.net/jeps/328) |  ~~_Release_~~   |                   ~~_Not Applicable - Not a language specification change (NA)_~~                    | ~~Flight Recorder~~                                              |
| [JEP 329](https://openjdk.java.net/jeps/329) |  ~~_Release_~~   |                   ~~_Not Applicable - Not a language specification change (NA)_~~                    | ~~ChaCha20 and Poly1305 Cryptographic Algorithms~~               |
| [JEP 330](https://openjdk.java.net/jeps/330) |  ~~_Release_~~   |                   ~~_Not Applicable - Not a language specification change (NA)_~~                    | ~~Launch Single-File Source-Code Programs~~                      |
| [JEP 331](https://openjdk.java.net/jeps/331) |  ~~_Release_~~   |                   ~~_Not Applicable - Not a language specification change (NA)_~~                    | ~~Low-Overhead Heap Profiling~~                                  |
| [JEP 332](https://openjdk.java.net/jeps/332) |  ~~_Release_~~   |                   ~~_Not Applicable - Not a language specification change (NA)_~~                    | ~~Transport Layer Security (TLS) 1.3~~                           |
| [JEP 333](https://openjdk.java.net/jeps/333) | ~~Experimental~~ |                   ~~_Not Applicable - Not a language specification change (NA)_~~                    | ~~ZGC: A Scalable Low-Latency Garbage Collector (Experimental)~~ |
| [JEP 335](https://openjdk.java.net/jeps/335) |  ~~_Release_~~   |                   ~~_Not Applicable - Not a language specification change (NA)_~~                    | ~~Deprecate the Nashorn JavaScript Engine~~                      |
| [JEP 336](https://openjdk.java.net/jeps/336) |  ~~_Release_~~   |                   ~~_Not Applicable - Not a language specification change (NA)_~~                    | ~~Deprecate the Pack200 Tools and API~~                          |

##### Footnotes:

- <b id="f_11_JEP181">JEP181</b> - Based on a cursory reading of this JEP, it is unclear if this is a change that affects JavaParser. 
                                      Comments/discussion on this are welcomed. [↩](#a_11_JEP181)
- <b id="f_11_JEP327">JEP327</b> - Based on a cursory reading of this JEP, it is unclear if this is a change that affects JavaParser. 
                                     Comments/discussion on this are welcomed. [↩](#a_11_JEP327)
- <b id="f_11_JEP320">JEP320</b> - JEP 320 is marked as NA. This is because JavaParser does not make use of classes within these packages, 
                                       and any users of JavaParser will need to provide the relevant files in order to do parsing/solving 
                                       (e.g. as source files, a jar, or via reflection). [↩](#a_11_JEP320) 


## JDK 12 - March 2019
Source: https://openjdk.java.net/projects/jdk/12/

Parsing support for Java 12 (including preview features) [complete on 03/Feb/2019](https://github.com/javaparser/javaparser/blob/master/changelog.md#version-3110)

Resolution support for Java 12 complete on ??/??/2019

|                     JEP                      |      Status      |                        JavaParser Since                         | Description                                                       |
|:--------------------------------------------:|:----------------:|:---------------------------------------------------------------:|-------------------------------------------------------------------|
| [JEP 325](https://openjdk.java.net/jeps/325) |  **_Preview_**   |    **Supported Since: v3.11.0<br>Released on: 03/Feb/2019**     | Switch Expressions (Preview)                                      |
| [JEP 189](https://openjdk.java.net/jeps/189) | ~~Experimental~~ | ~~_Not Applicable - Not a language specification change (NA)_~~ | ~~Shenandoah: A Low-Pause-Time Garbage Collector (Experimental)~~ |
| [JEP 230](https://openjdk.java.net/jeps/230) |  ~~_Release_~~   | ~~_Not Applicable - Not a language specification change (NA)_~~ | ~~Microbenchmark Suite~~                                          |
| [JEP 334](https://openjdk.java.net/jeps/334) |  ~~_Release_~~   | ~~_Not Applicable - Not a language specification change (NA)_~~ | ~~JVM Constants API~~                                             |
| [JEP 340](https://openjdk.java.net/jeps/340) |  ~~_Release_~~   | ~~_Not Applicable - Not a language specification change (NA)_~~ | ~~One AArch64 Port, Not Two~~                                     |
| [JEP 341](https://openjdk.java.net/jeps/341) |  ~~_Release_~~   | ~~_Not Applicable - Not a language specification change (NA)_~~ | ~~Default CDS Archives~~                                          |
| [JEP 344](https://openjdk.java.net/jeps/344) |  ~~_Release_~~   | ~~_Not Applicable - Not a language specification change (NA)_~~ | ~~Abortable Mixed Collections for G1~~                            |
| [JEP 346](https://openjdk.java.net/jeps/346) |  ~~_Release_~~   | ~~_Not Applicable - Not a language specification change (NA)_~~ | ~~Promptly Return Unused Committed Memory from G1~~               |

## JDK 13 - September 2018
Source: https://openjdk.java.net/projects/jdk/13/

No language specification changes in JDK 13 -- thus no "complete" date. Details of preview support is below.

|                     JEP                      |    Status     |                        JavaParser Since                         | Description                           |
|:--------------------------------------------:|:-------------:|:---------------------------------------------------------------:|---------------------------------------|
| [JEP 354](https://openjdk.java.net/jeps/354) | **_Preview_** |    **Supported Since: v3.11.0<br>Released on: 03/Feb/2019**     | Switch Expressions (Preview)          |
| [JEP 355](https://openjdk.java.net/jeps/355) | **_Preview_** |    **Supported Since: v3.14.0<br>Released on: 05/May/2019**     | Text Blocks (Preview)                 |
| [JEP 350](https://openjdk.java.net/jeps/350) | ~~_Release_~~ | ~~_Not Applicable - Not a language specification change (NA)_~~ | ~~Dynamic CDS Archives~~              |
| [JEP 351](https://openjdk.java.net/jeps/351) | ~~_Release_~~ | ~~_Not Applicable - Not a language specification change (NA)_~~ | ~~ZGC: Uncommit Unused Memory~~       |
| [JEP 353](https://openjdk.java.net/jeps/353) | ~~_Release_~~ | ~~_Not Applicable - Not a language specification change (NA)_~~ | ~~Reimplement the Legacy Socket API~~ |



## JDK 14 - March 2020
Source: https://openjdk.java.net/projects/jdk/14/

Switch support was complete during preview status. 

The preview features of records are work-in-progress.

|                     JEP                      |     Status      |                                                 JavaParser Since                                                  | Description                                                   |
|:--------------------------------------------:|:---------------:|:-----------------------------------------------------------------------------------------------------------------:|---------------------------------------------------------------|
| [JEP 361](https://openjdk.java.net/jeps/361) |   **Release**   |                             **Supported Since: v3.xx.yy<br>Released on: dd/mmm/yyyy**                             | **Switch Expressions (Standard)**                             |
| [JEP 368](https://openjdk.java.net/jeps/368) | **2nd Preview** |                             **Supported Since: v3.14.0<br>Released on: 05/May/2019**                              | **Text Blocks (Second Preview)**                              |
| [JEP 305](https://openjdk.java.net/jeps/305) |  **_Preview_**  |                             **Supported Since: v3.18.0<br>Released on: 01/Dec/2020**                              | **Pattern Matching for `instanceof` (Preview)**               |
| [JEP 359](https://openjdk.java.net/jeps/359) |  **_Preview_**  | **Partial Support Since: v3.22.0<br>Released on: 11/May/2021 <sup id="a_14_JEP359">[JEP343](#f_14_JEP359)</sup>** | **Records (Preview)**                                         |
| [JEP 343](https://openjdk.java.net/jeps/343) | ~~_Incubator_~~ |                    ~~_Not Applicable (NA)<sup id="a_14_JEP343">[JEP343](#f_14_JEP343)</sup>_~~                    | ~~Packaging Tool (Incubator)~~                                |
| [JEP 345](https://openjdk.java.net/jeps/345) |  ~~_Release_~~  |                          ~~_Not Applicable - Not a language specification change (NA)_~~                          | ~~NUMA-Aware Memory Allocation for G1~~                       |
| [JEP 349](https://openjdk.java.net/jeps/349) |  ~~_Release_~~  |                          ~~_Not Applicable - Not a language specification change (NA)_~~                          | ~~JFR Event Streaming~~                                       |
| [JEP 352](https://openjdk.java.net/jeps/352) |  ~~_Release_~~  |                          ~~_Not Applicable - Not a language specification change (NA)_~~                          | ~~Non-Volatile Mapped Byte Buffers~~                          |
| [JEP 358](https://openjdk.java.net/jeps/358) |  ~~_Release_~~  |                          ~~_Not Applicable - Not a language specification change (NA)_~~                          | ~~Helpful NullPointerExceptions~~                             |
| [JEP 362](https://openjdk.java.net/jeps/362) |  ~~_Release_~~  |                          ~~_Not Applicable - Not a language specification change (NA)_~~                          | ~~Deprecate the Solaris and SPARC Ports~~                     |
| [JEP 363](https://openjdk.java.net/jeps/363) |  ~~_Release_~~  |                          ~~_Not Applicable - Not a language specification change (NA)_~~                          | ~~Remove the Concurrent Mark Sweep (CMS) Garbage Collector~~  |
| [JEP 364](https://openjdk.java.net/jeps/364) |  ~~_Release_~~  |                          ~~_Not Applicable - Not a language specification change (NA)_~~                          | ~~ZGC on macOS~~                                              |
| [JEP 365](https://openjdk.java.net/jeps/365) |  ~~_Release_~~  |                          ~~_Not Applicable - Not a language specification change (NA)_~~                          | ~~ZGC on Windows~~                                            |
| [JEP 366](https://openjdk.java.net/jeps/366) |  ~~_Release_~~  |                          ~~_Not Applicable - Not a language specification change (NA)_~~                          | ~~Deprecate the ParallelScavenge + SerialOld GC Combination~~ |
| [JEP 367](https://openjdk.java.net/jeps/367) |  ~~_Release_~~  |                          ~~_Not Applicable - Not a language specification change (NA)_~~                          | ~~Remove the Pack200 Tools and API~~                          |
| [JEP 370](https://openjdk.java.net/jeps/370) |  ~~_Release_~~  |                          ~~_Not Applicable - Not a language specification change (NA)_~~                          | ~~Foreign-Memory Access API (Incubator)~~                     |

##### Footnotes:

- <b id="f_14_JEP343">JEP343</b> - JEP 343 is marked as not applicable, as it relates to packaging of apps - e.g. as `.exe`/`.msi`/`.deb`/`.rpm`/`.pkg`/`.dmg`. 
  The JEP describes the layout/structure of the output file, suggesting that _maybe_ in the future the files may be examined, and _potentially_ used similarly to a `.jar` or set of `.class` files. 
  This is not going to be actively pursued (_especially_ since this is still in the incubator stage), though tested PRs are always welcome. 
  [↩](#a_14_JEP343)


- <b id="f_14_JEP359">JEP359</b> - The behaviour of records changed between preview/2nd preview/release.
  Unless otherwise stated, the JavaParser implementation follows the released behaviour.
  Additionally, note that "partial" support refers to javaparser-core being complete since 3.21.0, and javaparser-symbol-solver-core support is TBC.
  [↩](#a_14_JEP359)



## JDK 15 - September 2020
Source: https://openjdk.java.net/projects/jdk/15/

Note: Unless otherwise stated, the JavaParser implementations of features follows the released behaviour.

|                     JEP                      |     Status      |                                                 JavaParser Since                                                  | Description                                            |
|:--------------------------------------------:|:---------------:|:-----------------------------------------------------------------------------------------------------------------:|--------------------------------------------------------|
| [JEP 378](https://openjdk.java.net/jeps/378) |  **_Release_**  |                             **Supported Since: v3.14.0<br>Released on: 05/May/2019**                              | **Text Blocks**                                        |
| [JEP 384](https://openjdk.java.net/jeps/384) |  **_Release_**  | **Partial Support Since: v3.22.0<br>Released on: 11/May/2021 <sup id="a_15_JEP384">[JEP384](#f_15_JEP384)</sup>** | **Records (Second Preview)**                           |
| [JEP 375](https://openjdk.java.net/jeps/375) |  **_Release_**  |                             **Supported Since: v3.18.0<br>Released on: 01/Dec/2020**                              | **Pattern Matching for `instanceof` (Second Preview)** |
| [JEP 360](https://openjdk.java.net/jeps/360) |  **_Preview_**  |                                                                                                                   | **Sealed Classes (Preview)**                           |
| [JEP 339](https://openjdk.java.net/jeps/339) |  **_Release_**  |                          ~~_Not Applicable - Not a language specification change (NA)_~~                          | ~~Edwards-Curve Digital Signature Algorithm (EdDSA)~~  |
| [JEP 371](https://openjdk.java.net/jeps/371) |  **_Release_**  |                          ~~_Not Applicable - Not a language specification change (NA)_~~                          | ~~Hidden Classes~~                                     |
| [JEP 372](https://openjdk.java.net/jeps/372) |  **_Release_**  |                          ~~_Not Applicable - Not a language specification change (NA)_~~                          | ~~Remove the Nashorn JavaScript Engine~~               |
| [JEP 373](https://openjdk.java.net/jeps/373) |  **_Release_**  |                          ~~_Not Applicable - Not a language specification change (NA)_~~                          | ~~Reimplement the Legacy DatagramSocket API~~          |
| [JEP 374](https://openjdk.java.net/jeps/374) |  **_Release_**  |                          ~~_Not Applicable - Not a language specification change (NA)_~~                          | ~~Disable and Deprecate Biased Locking~~               |
| [JEP 377](https://openjdk.java.net/jeps/377) |  **_Release_**  |                          ~~_Not Applicable - Not a language specification change (NA)_~~                          | ~~ZGC: A Scalable Low-Latency Garbage Collector~~      |
| [JEP 379](https://openjdk.java.net/jeps/379) |  **_Release_**  |                          ~~_Not Applicable - Not a language specification change (NA)_~~                          | ~~Shenandoah: A Low-Pause-Time Garbage Collector~~     |
| [JEP 381](https://openjdk.java.net/jeps/381) |  **_Release_**  |                          ~~_Not Applicable - Not a language specification change (NA)_~~                          | ~~Remove the Solaris and SPARC Ports~~                 |
| [JEP 383](https://openjdk.java.net/jeps/383) | **_Incubator_** |                          ~~_Not Applicable - Not a language specification change (NA)_~~                          | ~~Foreign-Memory Access API (Second Incubator)~~       |
| [JEP 385](https://openjdk.java.net/jeps/385) |  **_Release_**  |                          ~~_Not Applicable - Not a language specification change (NA)_~~                          | ~~Deprecate RMI Activation for Removal~~               |

- <b id="f_15_JEP384">JEP384</b> - The behaviour of records changed between preview/2nd preview/release. 
  Unless otherwise stated, the JavaParser implementation follows the released behaviour. 
  Additionally, note that "partial" support refers to javaparser-core being complete since 3.21.0, and javaparser-symbol-solver-core support is TBC.
  [↩](#a_15_JEP384)
  


## JDK 16 - March 2021
Source: https://openjdk.java.net/projects/jdk/16/

Note: Unless otherwise stated, the JavaParser implementations of features follows the released behaviour.

|                     JEP                      |     Status      |                                                        JavaParser Since                                                        | Description                                       |
|:--------------------------------------------:|:---------------:|:------------------------------------------------------------------------------------------------------------------------------:|---------------------------------------------------|
| [JEP 395](https://openjdk.java.net/jeps/395) |  **_Release_**  | **Parser Support Since: v3.22.0<br>Released on: 11/May/2021, Solving TBC  <sup id="a_16_JEP384">[JEP395](#f_16_JEP395)</sup>** | **Records**                                       |
| [JEP 394](https://openjdk.java.net/jeps/394) |  **_Release_**  |                                    **Supported Since: v3.18.0<br>Released on: 01/Dec/2020**                                    | **Pattern Matching for `instanceof`**             |
| [JEP 397](https://openjdk.java.net/jeps/397) | **2nd Preview** |                                                                                                                                | **Sealed Classes (Second Preview)**               |
| [JEP 338](https://openjdk.java.net/jeps/338) |  **_Release_**  |                                ~~_Not Applicable - Not a language specification change (NA)_~~                                 | ~~Vector API (Incubator)~~                        |
| [JEP 347](https://openjdk.java.net/jeps/347) |  **_Release_**  |                                ~~_Not Applicable - Not a language specification change (NA)_~~                                 | ~~Enable C++14 Language Features~~                |
| [JEP 357](https://openjdk.java.net/jeps/357) |  **_Release_**  |                                ~~_Not Applicable - Not a language specification change (NA)_~~                                 | ~~Migrate from Mercurial to Git~~                 |
| [JEP 369](https://openjdk.java.net/jeps/369) |  **_Release_**  |                                ~~_Not Applicable - Not a language specification change (NA)_~~                                 | ~~Migrate to GitHub~~                             |
| [JEP 376](https://openjdk.java.net/jeps/376) |  **_Release_**  |                                ~~_Not Applicable - Not a language specification change (NA)_~~                                 | ~~ZGC: Concurrent Thread-Stack Processing~~       |
| [JEP 380](https://openjdk.java.net/jeps/380) |  **_Release_**  |                                ~~_Not Applicable - Not a language specification change (NA)_~~                                 | ~~Unix-Domain Socket Channels~~                   |
| [JEP 386](https://openjdk.java.net/jeps/386) |  **_Release_**  |                                ~~_Not Applicable - Not a language specification change (NA)_~~                                 | ~~Alpine Linux Port~~                             |
| [JEP 387](https://openjdk.java.net/jeps/387) |  **_Release_**  |                                ~~_Not Applicable - Not a language specification change (NA)_~~                                 | ~~Elastic Metaspace~~                             |
| [JEP 388](https://openjdk.java.net/jeps/388) |  **_Release_**  |                                ~~_Not Applicable - Not a language specification change (NA)_~~                                 | ~~Windows/AArch64 Port~~                          |
| [JEP 389](https://openjdk.java.net/jeps/389) | **_Incubator_** |                                ~~_Not Applicable - Not a language specification change (NA)_~~                                 | ~~Foreign Linker API (Incubator)~~                |
| [JEP 390](https://openjdk.java.net/jeps/390) |  **_Release_**  |                                ~~_Not Applicable - Not a language specification change (NA)_~~                                 | ~~Warnings for Value-Based Classes~~              |
| [JEP 392](https://openjdk.java.net/jeps/392) |  **_Release_**  |                                ~~_Not Applicable - Not a language specification change (NA)_~~                                 | ~~Packaging Tool~~                                |
| [JEP 393](https://openjdk.java.net/jeps/393) |  **_Release_**  |                                ~~_Not Applicable - Not a language specification change (NA)_~~                                 | ~~Foreign-Memory Access API (Third Incubator)~~   |
| [JEP 396](https://openjdk.java.net/jeps/396) |  **_Release_**  |                                ~~_Not Applicable - Not a language specification change (NA)_~~                                 | ~~Strongly Encapsulate JDK Internals by Default~~ |

- <b id="f_16_JEP395">JEP395</b> - The behaviour of records changed between preview/2nd preview/release.
  Unless otherwise stated, the JavaParser implementation follows the released behaviour.
  Additionally, note that "partial" support refers to javaparser-core being complete since 3.21.0, and javaparser-symbol-solver-core support is TBC.
  [↩](#a_16_JEP395)


## JDK 17 - September 2021
Source: https://openjdk.java.net/projects/jdk/17/

Note: Unless otherwise stated, the JavaParser implementations of features follows the released behaviour.

|                     JEP                      |       Status        |                        JavaParser Since                         | Description                                    |
|:--------------------------------------------:|:-------------------:|:---------------------------------------------------------------:|------------------------------------------------|
| [JEP 306](https://openjdk.java.net/jeps/306) |    **_Release_**    |                                                                 | Restore Always-Strict Floating-Point Semantics |
| [JEP 409](https://openjdk.java.net/jeps/409) |    **_Release_**    |                                                                 | Sealed Classes                                 |
| [JEP 406](https://openjdk.java.net/jeps/406) |    **_Preview_**    |                                                                 | Pattern Matching for `switch` (Preview)        |
| [JEP 356](https://openjdk.java.net/jeps/356) |    **_Release_**    | ~~_Not Applicable - Not a language specification change (NA)_~~ | Enhanced Pseudo-Random Number Generators       |
| [JEP 382](https://openjdk.java.net/jeps/382) |    **_Release_**    | ~~_Not Applicable - Not a language specification change (NA)_~~ | New macOS Rendering Pipeline                   |
| [JEP 391](https://openjdk.java.net/jeps/391) |    **_Release_**    | ~~_Not Applicable - Not a language specification change (NA)_~~ | macOS/AArch64 Port                             |
| [JEP 398](https://openjdk.java.net/jeps/398) |    **_Release_**    | ~~_Not Applicable - Not a language specification change (NA)_~~ | Deprecate the Applet API for Removal           |
| [JEP 403](https://openjdk.java.net/jeps/403) |    **_Release_**    | ~~_Not Applicable - Not a language specification change (NA)_~~ | Strongly Encapsulate JDK Internals             |
| [JEP 407](https://openjdk.java.net/jeps/407) |    **_Release_**    | ~~_Not Applicable - Not a language specification change (NA)_~~ | Remove RMI Activation                          |
| [JEP 410](https://openjdk.java.net/jeps/410) |    **_Release_**    | ~~_Not Applicable - Not a language specification change (NA)_~~ | Remove the Experimental AOT and JIT Compiler   |
| [JEP 411](https://openjdk.java.net/jeps/411) |    **_Release_**    | ~~_Not Applicable - Not a language specification change (NA)_~~ | Deprecate the Security Manager for Removal     |
| [JEP 412](https://openjdk.java.net/jeps/412) |   **_Incubator_**   | ~~_Not Applicable - Not a language specification change (NA)_~~ | Foreign Function & Memory API (Incubator)      |
| [JEP 414](https://openjdk.java.net/jeps/414) | **_2nd Incubator_** | ~~_Not Applicable - Not a language specification change (NA)_~~ | Vector API (Second Incubator)                  |
| [JEP 415](https://openjdk.java.net/jeps/415) |    **_Release_**    | ~~_Not Applicable - Not a language specification change (NA)_~~ | Context-Specific Deserialization Filters       |



## JDK 18 - March 2022
Source: https://openjdk.java.net/projects/jdk/18/

Note: Unless otherwise stated, the JavaParser implementations of features follows the released behaviour.

### Schedule 

    2021/12/09 		Rampdown Phase One (fork from main line)
    2022/01/20 		Rampdown Phase Two
    2022/02/10 		Initial Release Candidate
    2022/02/24 		Final Release Candidate
    2022/03/22 		General Availability


### Features

|                     JEP                      |       Status        |                        JavaParser Since                         | Description                                      |
|:--------------------------------------------:|:-------------------:|:---------------------------------------------------------------:|--------------------------------------------------|
| [JEP 413](https://openjdk.java.net/jeps/413) |    **_Release_**    |                                                                 | Code Snippets in Java API Documentation          |
| [JEP 420](https://openjdk.java.net/jeps/420) |    **_Preview_**    |                                                                 | Pattern Matching for `switch` (Second Preview)   |
| [JEP 400](https://openjdk.java.net/jeps/400) |    **_Release_**    | ~~_Not Applicable - Not a language specification change (NA)_~~ | UTF-8 by Default                                 |
| [JEP 408](https://openjdk.java.net/jeps/408) |    **_Release_**    | ~~_Not Applicable - Not a language specification change (NA)_~~ | Simple Web Server                                |
| [JEP 416](https://openjdk.java.net/jeps/416) |    **_Release_**    | ~~_Not Applicable - Not a language specification change (NA)_~~ | Reimplement Core Reflection with Method Handles  |
| [JEP 417](https://openjdk.java.net/jeps/417) | **_3rd Incubator_** | ~~_Not Applicable - Not a language specification change (NA)_~~ | Vector API (Third Incubator)                     |
| [JEP 418](https://openjdk.java.net/jeps/418) |    **_Release_**    | ~~_Not Applicable - Not a language specification change (NA)_~~ | Internet-Address Resolution SPI                  |
| [JEP 419](https://openjdk.java.net/jeps/419) | **_2nd Incubator_** | ~~_Not Applicable - Not a language specification change (NA)_~~ | Foreign Function & Memory API (Second Incubator) |
| [JEP 421](https://openjdk.java.net/jeps/421) |    **_Release_**    | ~~_Not Applicable - Not a language specification change (NA)_~~ | Deprecate Finalization for Removal               |



## JDK 19 - _targeted for September 2022_
Source: https://openjdk.java.net/projects/jdk/18/

Note: Unless otherwise stated, the JavaParser implementations of features follows the released behaviour.

### Features

    JEPs targeted to JDK 19, so far
    422: 	Linux/RISC-V Port

    Last update: 2022/3/18 16:38 UTC

