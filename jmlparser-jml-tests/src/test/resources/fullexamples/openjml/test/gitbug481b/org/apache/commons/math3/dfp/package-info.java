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
 * Decimal floating point library for Java
 *
 * <p>Another floating point class.  This one is built using radix 10000
 * which is 10<sup>4</sup>, so its almost decimal.</p>
 *
 * <p>The design goals here are:
 * <ol>
 *  <li>Decimal math, or close to it</li>
 *  <li>Settable precision (but no mix between numbers using different settings)</li>
 *  <li>Portability.  Code should be keep as portable as possible.</li>
 *  <li>Performance</li>
 *  <li>Accuracy  - Results should always be +/- 1 ULP for basic
 *       algebraic operation</li>
 *  <li>Comply with IEEE 854-1987 as much as possible.
 *       (See IEEE 854-1987 notes below)</li>
 * </ol></p>
 *
 * <p>Trade offs:
 * <ol>
 *  <li>Memory foot print.  I'm using more memory than necessary to
 *       represent numbers to get better performance.</li>
 *  <li>Digits are bigger, so rounding is a greater loss.  So, if you
 *       really need 12 decimal digits, better use 4 base 10000 digits
 *       there can be one partially filled.</li>
 * </ol></p>
 *
 * <p>Numbers are represented  in the following form:
 * <pre>
 * n  =  sign &times; mant &times; (radix)<sup>exp</sup>;</p>
 * </pre>
 * where sign is &plusmn;1, mantissa represents a fractional number between
 * zero and one.  mant[0] is the least significant digit.
 * exp is in the range of -32767 to 32768</p>
 *
 * <p>IEEE 854-1987  Notes and differences</p>
 *
 * <p>IEEE 854 requires the radix to be either 2 or 10.  The radix here is
 * 10000, so that requirement is not met, but  it is possible that a
 * subclassed can be made to make it behave as a radix 10
 * number.  It is my opinion that if it looks and behaves as a radix
 * 10 number then it is one and that requirement would be met.</p>
 *
 * <p>The radix of 10000 was chosen because it should be faster to operate
 * on 4 decimal digits at once instead of one at a time.  Radix 10 behavior
 * can be realized by add an additional rounding step to ensure that
 * the number of decimal digits represented is constant.</p>
 *
 * <p>The IEEE standard specifically leaves out internal data encoding,
 * so it is reasonable to conclude that such a subclass of this radix
 * 10000 system is merely an encoding of a radix 10 system.</p>
 *
 * <p>IEEE 854 also specifies the existence of "sub-normal" numbers.  This
 * class does not contain any such entities.  The most significant radix
 * 10000 digit is always non-zero.  Instead, we support "gradual underflow"
 * by raising the underflow flag for numbers less with exponent less than
 * expMin, but don't flush to zero until the exponent reaches MIN_EXP-digits.
 * Thus the smallest number we can represent would be:
 * 1E(-(MIN_EXP-digits-1)&lowast;4),  eg, for digits=5, MIN_EXP=-32767, that would
 * be 1e-131092.</p>
 *
 * <p>IEEE 854 defines that the implied radix point lies just to the right
 * of the most significant digit and to the left of the remaining digits.
 * This implementation puts the implied radix point to the left of all
 * digits including the most significant one.  The most significant digit
 * here is the one just to the right of the radix point.  This is a fine
 * detail and is really only a matter of definition.  Any side effects of
 * this can be rendered invisible by a subclass.</p>
 *
 */
package org.apache.commons.math3.dfp;
