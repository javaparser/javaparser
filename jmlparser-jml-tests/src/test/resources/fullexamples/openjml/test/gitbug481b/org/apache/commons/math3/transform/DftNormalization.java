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
package org.apache.commons.math3.transform;

/**
 * This enumeration defines the various types of normalizations that can be
 * applied to discrete Fourier transforms (DFT). The exact definition of these
 * normalizations is detailed below.
 *
 * @see FastFourierTransformer
 * @since 3.0
 */
public enum DftNormalization {
    /**
     * Should be passed to the constructor of {@link FastFourierTransformer}
     * to use the <em>standard</em> normalization convention. This normalization
     * convention is defined as follows
     * <ul>
     * <li>forward transform: y<sub>n</sub> = &sum;<sub>k=0</sub><sup>N-1</sup>
     * x<sub>k</sub> exp(-2&pi;i n k / N),</li>
     * <li>inverse transform: x<sub>k</sub> = N<sup>-1</sup>
     * &sum;<sub>n=0</sub><sup>N-1</sup> y<sub>n</sub> exp(2&pi;i n k / N),</li>
     * </ul>
     * where N is the size of the data sample.
     */
    STANDARD,

    /**
     * Should be passed to the constructor of {@link FastFourierTransformer}
     * to use the <em>unitary</em> normalization convention. This normalization
     * convention is defined as follows
     * <ul>
     * <li>forward transform: y<sub>n</sub> = (1 / &radic;N)
     * &sum;<sub>k=0</sub><sup>N-1</sup> x<sub>k</sub>
     * exp(-2&pi;i n k / N),</li>
     * <li>inverse transform: x<sub>k</sub> = (1 / &radic;N)
     * &sum;<sub>n=0</sub><sup>N-1</sup> y<sub>n</sub> exp(2&pi;i n k / N),</li>
     * </ul>
     * which makes the transform unitary. N is the size of the data sample.
     */
    UNITARY;
}
