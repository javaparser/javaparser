/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
/**
 *
 *      <p>Random number and random data generators.</p>
 *      <p>Commons-math provides a few pseudo random number generators. The top level interface is RandomGenerator.
 *      It is implemented by three classes:
 *      <ul>
 *        <li>{@link org.apache.commons.math3.random.JDKRandomGenerator JDKRandomGenerator}
 *            that extends the JDK provided generator</li>
 *        <li>AbstractRandomGenerator as a helper for users generators</li>
 *        <li>BitStreamGenerator which is an abstract class for several generators and
 *            which in turn is extended by:
 *            <ul>
 *              <li>{@link org.apache.commons.math3.random.MersenneTwister MersenneTwister}</li>
 *              <li>{@link org.apache.commons.math3.random.Well512a Well512a}</li>
 *              <li>{@link org.apache.commons.math3.random.Well1024a Well1024a}</li>
 *              <li>{@link org.apache.commons.math3.random.Well19937a Well19937a}</li>
 *              <li>{@link org.apache.commons.math3.random.Well19937c Well19937c}</li>
 *              <li>{@link org.apache.commons.math3.random.Well44497a Well44497a}</li>
 *              <li>{@link org.apache.commons.math3.random.Well44497b Well44497b}</li>
 *            </ul>
 *          </li>
 *        </ul>
 *      </p>
 *
 *      <p>
 *      The JDK provided generator is a simple one that can be used only for very simple needs.
 *      The Mersenne Twister is a fast generator with very good properties well suited for
 *      Monte-Carlo simulation. It is equidistributed for generating vectors up to dimension 623
 *      and has a huge period: 2<sup>19937</sup> - 1 (which is a Mersenne prime). This generator
 *      is described in a paper by Makoto Matsumoto and Takuji Nishimura in 1998: <a
 *      href="http://www.math.sci.hiroshima-u.ac.jp/~m-mat/MT/ARTICLES/mt.pdf">Mersenne Twister:
 *      A 623-Dimensionally Equidistributed Uniform Pseudo-Random Number Generator</a>, ACM
 *      Transactions on Modeling and Computer Simulation, Vol. 8, No. 1, January 1998, pp 3--30.
 *      The WELL generators are a family of generators with period ranging from 2<sup>512</sup> - 1
 *      to 2<sup>44497</sup> - 1 (this last one is also a Mersenne prime) with even better properties
 *      than Mersenne Twister. These generators are described in a paper by Fran&ccedil;ois Panneton,
 *      Pierre L'Ecuyer and Makoto Matsumoto <a
 *      href="http://www.iro.umontreal.ca/~lecuyer/myftp/papers/wellrng.pdf">Improved Long-Period
 *      Generators Based on Linear Recurrences Modulo 2</a> ACM Transactions on Mathematical Software,
 *      32, 1 (2006). The errata for the paper are in <a
 *      href="http://www.iro.umontreal.ca/~lecuyer/myftp/papers/wellrng-errata.txt">wellrng-errata.txt</a>.
 *      </p>
 *
 *      <p>
 *      For simple sampling, any of these generators is sufficient. For Monte-Carlo simulations the
 *      JDK generator does not have any of the good mathematical properties of the other generators,
 *      so it should be avoided. The Mersenne twister and WELL generators have equidistribution properties
 *      proven according to their bits pool size which is directly linked to their period (all of them
 *      have maximal period, i.e. a generator with size n pool has a period 2<sup>n</sup>-1). They also
 *      have equidistribution properties for 32 bits blocks up to s/32 dimension where s is their pool size.
 *      So WELL19937c for exemple is equidistributed up to dimension 623 (19937/32). This means a Monte-Carlo
 *      simulation generating a vector of n variables at each iteration has some guarantees on the properties
 *      of the vector as long as its dimension does not exceed the limit. However, since we use bits from two
 *      successive 32 bits generated integers to create one double, this limit is smaller when the variables are
 *      of type double. so for Monte-Carlo simulation where less the 16 doubles are generated at each round,
 *      WELL1024 may be sufficient. If a larger number of doubles are needed a generator with a larger pool
 *      would be useful.
 *      </p>
 *
 *      <p>
 *      The WELL generators are more modern then MersenneTwister (the paper describing than has been published
 *      in 2006 instead of 1998) and fix some of its (few) drawbacks. If initialization array contains many
 *      zero bits, MersenneTwister may take a very long time (several hundreds of thousands of iterations to
 *      reach a steady state with a balanced number of zero and one in its bits pool). So the WELL generators
 *      are better to <i>escape zeroland</i> as explained by the WELL generators creators. The Well19937a and
 *      Well44497a generator are not maximally equidistributed (i.e. there are some dimensions or bits blocks
 *      size for which they are not equidistributed). The Well512a, Well1024a, Well19937c and Well44497b are
 *      maximally equidistributed for blocks size up to 32 bits (they should behave correctly also for double
 *      based on more than 32 bits blocks, but equidistribution is not proven at these blocks sizes).
 *      </p>
 *
 *      <p>
 *      The MersenneTwister generator uses a 624 elements integer array, so it consumes less than 2.5 kilobytes.
 *      The WELL generators use 6 integer arrays with a size equal to the pool size, so for example the
 *      WELL44497b generator uses about 33 kilobytes. This may be important if a very large number of
 *      generator instances were used at the same time.
 *      </p>
 *
 *      <p>
 *      All generators are quite fast. As an example, here are some comparisons, obtained on a 64 bits JVM on a
 *      linux computer with a 2008 processor (AMD phenom Quad 9550 at 2.2 GHz). The generation rate for
 *      MersenneTwister was about 27 millions doubles per second (remember we generate two 32 bits integers for
 *      each double). Generation rates for other PRNG, relative to MersenneTwister:
 *      </p>
 *
 *      <p>
 *        <table border="1" align="center">
 *          <tr BGCOLOR="#CCCCFF"><td colspan="2"><font size="+2">Example of performances</font></td></tr>
 *          <tr BGCOLOR="#EEEEFF"><font size="+1"><td>Name</td><td>generation rate (relative to MersenneTwister)</td></font></tr>
 *          <tr><td>{@link org.apache.commons.math3.random.MersenneTwister MersenneTwister}</td><td>1</td></tr>
 *          <tr><td>{@link org.apache.commons.math3.random.JDKRandomGenerator JDKRandomGenerator}</td><td>between 0.96 and 1.16</td></tr>
 *          <tr><td>{@link org.apache.commons.math3.random.Well512a Well512a}</td><td>between 0.85 and 0.88</td></tr>
 *          <tr><td>{@link org.apache.commons.math3.random.Well1024a Well1024a}</td><td>between 0.63 and 0.73</td></tr>
 *          <tr><td>{@link org.apache.commons.math3.random.Well19937a Well19937a}</td><td>between 0.70 and 0.71</td></tr>
 *          <tr><td>{@link org.apache.commons.math3.random.Well19937c Well19937c}</td><td>between 0.57 and 0.71</td></tr>
 *          <tr><td>{@link org.apache.commons.math3.random.Well44497a Well44497a}</td><td>between 0.69 and 0.71</td></tr>
 *          <tr><td>{@link org.apache.commons.math3.random.Well44497b Well44497b}</td><td>between 0.65 and 0.71</td></tr>
 *        </table>
 *      </p>
 *
 *      <p>
 *      So for most simulation problems, the better generators like {@link
 *      org.apache.commons.math3.random.Well19937c Well19937c} and {@link
 *      org.apache.commons.math3.random.Well44497b Well44497b} are probably very good choices.
 *      </p>
 *
 *      <p>
 *      Note that <em>none</em> of these generators are suitable for cryptography. They are devoted
 *      to simulation, and to generate very long series with strong properties on the series as a whole
 *      (equidistribution, no correlation ...). They do not attempt to create small series but with
 *      very strong properties of unpredictability as needed in cryptography.
 *      </p>
 *
 *
 */
package org.apache.commons.math3.random;
