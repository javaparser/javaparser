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
package org.apache.commons.math3.analysis.interpolation;

import org.apache.commons.math3.analysis.TrivariateFunction;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.NoDataException;
import org.apache.commons.math3.exception.NonMonotonicSequenceException;
import org.apache.commons.math3.exception.OutOfRangeException;
import org.apache.commons.math3.util.MathArrays;

/**
 * Function that implements the
 * <a href="http://en.wikipedia.org/wiki/Tricubic_interpolation">
 * tricubic spline interpolation</a>, as proposed in
 * <blockquote>
 *  Tricubic interpolation in three dimensions,
 *  F. Lekien and J. Marsden,
 *  <em>Int. J. Numer. Meth. Eng</em> 2005; <b>63</b>:455-471
 * </blockquote>
 *
 * @since 3.4.
 */
public class TricubicInterpolatingFunction
    implements TrivariateFunction {
    /**
     * Matrix to compute the spline coefficients from the function values
     * and function derivatives values
     */
    private static final double[][] AINV = {
        { 1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { -3,3,0,0,0,0,0,0,-2,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 2,-2,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-3,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-2,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { -3,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,-2,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,-3,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-2,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 9,-9,-9,9,0,0,0,0,6,3,-6,-3,0,0,0,0,6,-6,3,-3,0,0,0,0,0,0,0,0,0,0,0,0,4,2,2,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { -6,6,6,-6,0,0,0,0,-3,-3,3,3,0,0,0,0,-4,4,-2,2,0,0,0,0,0,0,0,0,0,0,0,0,-2,-2,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 2,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,2,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { -6,6,6,-6,0,0,0,0,-4,-2,4,2,0,0,0,0,-3,3,-3,3,0,0,0,0,0,0,0,0,0,0,0,0,-2,-1,-2,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 4,-4,-4,4,0,0,0,0,2,2,-2,-2,0,0,0,0,2,-2,2,-2,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-3,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-2,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-3,3,0,0,0,0,0,0,-2,-1,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,-2,0,0,0,0,0,0,1,1,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-3,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-2,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-3,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,-2,0,-1,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,-9,-9,9,0,0,0,0,0,0,0,0,0,0,0,0,6,3,-6,-3,0,0,0,0,6,-6,3,-3,0,0,0,0,4,2,2,1,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-6,6,6,-6,0,0,0,0,0,0,0,0,0,0,0,0,-3,-3,3,3,0,0,0,0,-4,4,-2,2,0,0,0,0,-2,-2,-1,-1,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-6,6,6,-6,0,0,0,0,0,0,0,0,0,0,0,0,-4,-2,4,2,0,0,0,0,-3,3,-3,3,0,0,0,0,-2,-1,-2,-1,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,-4,-4,4,0,0,0,0,0,0,0,0,0,0,0,0,2,2,-2,-2,0,0,0,0,2,-2,2,-2,0,0,0,0,1,1,1,1,0,0,0,0 },
        {-3,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-2,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,-3,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-2,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 9,-9,0,0,-9,9,0,0,6,3,0,0,-6,-3,0,0,0,0,0,0,0,0,0,0,6,-6,0,0,3,-3,0,0,0,0,0,0,0,0,0,0,4,2,0,0,2,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { -6,6,0,0,6,-6,0,0,-3,-3,0,0,3,3,0,0,0,0,0,0,0,0,0,0,-4,4,0,0,-2,2,0,0,0,0,0,0,0,0,0,0,-2,-2,0,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-3,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-2,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-3,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-2,0,0,0,-1,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,-9,0,0,-9,9,0,0,0,0,0,0,0,0,0,0,6,3,0,0,-6,-3,0,0,0,0,0,0,0,0,0,0,6,-6,0,0,3,-3,0,0,4,2,0,0,2,1,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-6,6,0,0,6,-6,0,0,0,0,0,0,0,0,0,0,-3,-3,0,0,3,3,0,0,0,0,0,0,0,0,0,0,-4,4,0,0,-2,2,0,0,-2,-2,0,0,-1,-1,0,0 },
        { 9,0,-9,0,-9,0,9,0,0,0,0,0,0,0,0,0,6,0,3,0,-6,0,-3,0,6,0,-6,0,3,0,-3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,2,0,2,0,1,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,9,0,-9,0,-9,0,9,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,0,3,0,-6,0,-3,0,6,0,-6,0,3,0,-3,0,0,0,0,0,0,0,0,0,4,0,2,0,2,0,1,0 },
        { -27,27,27,-27,27,-27,-27,27,-18,-9,18,9,18,9,-18,-9,-18,18,-9,9,18,-18,9,-9,-18,18,18,-18,-9,9,9,-9,-12,-6,-6,-3,12,6,6,3,-12,-6,12,6,-6,-3,6,3,-12,12,-6,6,-6,6,-3,3,-8,-4,-4,-2,-4,-2,-2,-1 },
        { 18,-18,-18,18,-18,18,18,-18,9,9,-9,-9,-9,-9,9,9,12,-12,6,-6,-12,12,-6,6,12,-12,-12,12,6,-6,-6,6,6,6,3,3,-6,-6,-3,-3,6,6,-6,-6,3,3,-3,-3,8,-8,4,-4,4,-4,2,-2,4,4,2,2,2,2,1,1 },
        { -6,0,6,0,6,0,-6,0,0,0,0,0,0,0,0,0,-3,0,-3,0,3,0,3,0,-4,0,4,0,-2,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-2,0,-2,0,-1,0,-1,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,-6,0,6,0,6,0,-6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-3,0,-3,0,3,0,3,0,-4,0,4,0,-2,0,2,0,0,0,0,0,0,0,0,0,-2,0,-2,0,-1,0,-1,0 },
        { 18,-18,-18,18,-18,18,18,-18,12,6,-12,-6,-12,-6,12,6,9,-9,9,-9,-9,9,-9,9,12,-12,-12,12,6,-6,-6,6,6,3,6,3,-6,-3,-6,-3,8,4,-8,-4,4,2,-4,-2,6,-6,6,-6,3,-3,3,-3,4,2,4,2,2,1,2,1 },
        { -12,12,12,-12,12,-12,-12,12,-6,-6,6,6,6,6,-6,-6,-6,6,-6,6,6,-6,6,-6,-8,8,8,-8,-4,4,4,-4,-3,-3,-3,-3,3,3,3,3,-4,-4,4,4,-2,-2,2,2,-4,4,-4,4,-2,2,-2,2,-2,-2,-2,-2,-1,-1,-1,-1 },
        { 2,0,0,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,2,0,0,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { -6,6,0,0,6,-6,0,0,-4,-2,0,0,4,2,0,0,0,0,0,0,0,0,0,0,-3,3,0,0,-3,3,0,0,0,0,0,0,0,0,0,0,-2,-1,0,0,-2,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 4,-4,0,0,-4,4,0,0,2,2,0,0,-2,-2,0,0,0,0,0,0,0,0,0,0,2,-2,0,0,2,-2,0,0,0,0,0,0,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-6,6,0,0,6,-6,0,0,0,0,0,0,0,0,0,0,-4,-2,0,0,4,2,0,0,0,0,0,0,0,0,0,0,-3,3,0,0,-3,3,0,0,-2,-1,0,0,-2,-1,0,0 },
        { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,-4,0,0,-4,4,0,0,0,0,0,0,0,0,0,0,2,2,0,0,-2,-2,0,0,0,0,0,0,0,0,0,0,2,-2,0,0,2,-2,0,0,1,1,0,0,1,1,0,0 },
        { -6,0,6,0,6,0,-6,0,0,0,0,0,0,0,0,0,-4,0,-2,0,4,0,2,0,-3,0,3,0,-3,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-2,0,-1,0,-2,0,-1,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,-6,0,6,0,6,0,-6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-4,0,-2,0,4,0,2,0,-3,0,3,0,-3,0,3,0,0,0,0,0,0,0,0,0,-2,0,-1,0,-2,0,-1,0 },
        { 18,-18,-18,18,-18,18,18,-18,12,6,-12,-6,-12,-6,12,6,12,-12,6,-6,-12,12,-6,6,9,-9,-9,9,9,-9,-9,9,8,4,4,2,-8,-4,-4,-2,6,3,-6,-3,6,3,-6,-3,6,-6,3,-3,6,-6,3,-3,4,2,2,1,4,2,2,1 },
        { -12,12,12,-12,12,-12,-12,12,-6,-6,6,6,6,6,-6,-6,-8,8,-4,4,8,-8,4,-4,-6,6,6,-6,-6,6,6,-6,-4,-4,-2,-2,4,4,2,2,-3,-3,3,3,-3,-3,3,3,-4,4,-2,2,-4,4,-2,2,-2,-2,-1,-1,-2,-2,-1,-1 },
        { 4,0,-4,0,-4,0,4,0,0,0,0,0,0,0,0,0,2,0,2,0,-2,0,-2,0,2,0,-2,0,2,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0 },
        { 0,0,0,0,0,0,0,0,4,0,-4,0,-4,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,2,0,-2,0,-2,0,2,0,-2,0,2,0,-2,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0 },
        { -12,12,12,-12,12,-12,-12,12,-8,-4,8,4,8,4,-8,-4,-6,6,-6,6,6,-6,6,-6,-6,6,6,-6,-6,6,6,-6,-4,-2,-4,-2,4,2,4,2,-4,-2,4,2,-4,-2,4,2,-3,3,-3,3,-3,3,-3,3,-2,-1,-2,-1,-2,-1,-2,-1 },
        { 8,-8,-8,8,-8,8,8,-8,4,4,-4,-4,-4,-4,4,4,4,-4,4,-4,-4,4,-4,4,4,-4,-4,4,4,-4,-4,4,2,2,2,2,-2,-2,-2,-2,2,2,-2,-2,2,2,-2,-2,2,-2,2,-2,2,-2,2,-2,1,1,1,1,1,1,1,1 }
    };

    /** Samples x-coordinates */
    private final double[] xval;
    /** Samples y-coordinates */
    private final double[] yval;
    /** Samples z-coordinates */
    private final double[] zval;
    /** Set of cubic splines patching the whole data grid */
    private final TricubicFunction[][][] splines;

    /**
     * @param x Sample values of the x-coordinate, in increasing order.
     * @param y Sample values of the y-coordinate, in increasing order.
     * @param z Sample values of the y-coordinate, in increasing order.
     * @param f Values of the function on every grid point.
     * @param dFdX Values of the partial derivative of function with respect to x on every grid point.
     * @param dFdY Values of the partial derivative of function with respect to y on every grid point.
     * @param dFdZ Values of the partial derivative of function with respect to z on every grid point.
     * @param d2FdXdY Values of the cross partial derivative of function on every grid point.
     * @param d2FdXdZ Values of the cross partial derivative of function on every grid point.
     * @param d2FdYdZ Values of the cross partial derivative of function on every grid point.
     * @param d3FdXdYdZ Values of the cross partial derivative of function on every grid point.
     * @throws NoDataException if any of the arrays has zero length.
     * @throws DimensionMismatchException if the various arrays do not contain the expected number of elements.
     * @throws NonMonotonicSequenceException if {@code x}, {@code y} or {@code z} are not strictly increasing.
     */
    public TricubicInterpolatingFunction(double[] x,
                                         double[] y,
                                         double[] z,
                                         double[][][] f,
                                         double[][][] dFdX,
                                         double[][][] dFdY,
                                         double[][][] dFdZ,
                                         double[][][] d2FdXdY,
                                         double[][][] d2FdXdZ,
                                         double[][][] d2FdYdZ,
                                         double[][][] d3FdXdYdZ)
        throws NoDataException,
               DimensionMismatchException,
               NonMonotonicSequenceException {
        final int xLen = x.length;
        final int yLen = y.length;
        final int zLen = z.length;

        if (xLen == 0 || yLen == 0 || z.length == 0 || f.length == 0 || f[0].length == 0) {
            throw new NoDataException();
        }
        if (xLen != f.length) {
            throw new DimensionMismatchException(xLen, f.length);
        }
        if (xLen != dFdX.length) {
            throw new DimensionMismatchException(xLen, dFdX.length);
        }
        if (xLen != dFdY.length) {
            throw new DimensionMismatchException(xLen, dFdY.length);
        }
        if (xLen != dFdZ.length) {
            throw new DimensionMismatchException(xLen, dFdZ.length);
        }
        if (xLen != d2FdXdY.length) {
            throw new DimensionMismatchException(xLen, d2FdXdY.length);
        }
        if (xLen != d2FdXdZ.length) {
            throw new DimensionMismatchException(xLen, d2FdXdZ.length);
        }
        if (xLen != d2FdYdZ.length) {
            throw new DimensionMismatchException(xLen, d2FdYdZ.length);
        }
        if (xLen != d3FdXdYdZ.length) {
            throw new DimensionMismatchException(xLen, d3FdXdYdZ.length);
        }

        MathArrays.checkOrder(x);
        MathArrays.checkOrder(y);
        MathArrays.checkOrder(z);

        xval = x.clone();
        yval = y.clone();
        zval = z.clone();

        final int lastI = xLen - 1;
        final int lastJ = yLen - 1;
        final int lastK = zLen - 1;
        splines = new TricubicFunction[lastI][lastJ][lastK];

        for (int i = 0; i < lastI; i++) {
            if (f[i].length != yLen) {
                throw new DimensionMismatchException(f[i].length, yLen);
            }
            if (dFdX[i].length != yLen) {
                throw new DimensionMismatchException(dFdX[i].length, yLen);
            }
            if (dFdY[i].length != yLen) {
                throw new DimensionMismatchException(dFdY[i].length, yLen);
            }
            if (dFdZ[i].length != yLen) {
                throw new DimensionMismatchException(dFdZ[i].length, yLen);
            }
            if (d2FdXdY[i].length != yLen) {
                throw new DimensionMismatchException(d2FdXdY[i].length, yLen);
            }
            if (d2FdXdZ[i].length != yLen) {
                throw new DimensionMismatchException(d2FdXdZ[i].length, yLen);
            }
            if (d2FdYdZ[i].length != yLen) {
                throw new DimensionMismatchException(d2FdYdZ[i].length, yLen);
            }
            if (d3FdXdYdZ[i].length != yLen) {
                throw new DimensionMismatchException(d3FdXdYdZ[i].length, yLen);
            }

            final int ip1 = i + 1;
            final double xR = xval[ip1] - xval[i];
            for (int j = 0; j < lastJ; j++) {
                if (f[i][j].length != zLen) {
                    throw new DimensionMismatchException(f[i][j].length, zLen);
                }
                if (dFdX[i][j].length != zLen) {
                    throw new DimensionMismatchException(dFdX[i][j].length, zLen);
                }
                if (dFdY[i][j].length != zLen) {
                    throw new DimensionMismatchException(dFdY[i][j].length, zLen);
                }
                if (dFdZ[i][j].length != zLen) {
                    throw new DimensionMismatchException(dFdZ[i][j].length, zLen);
                }
                if (d2FdXdY[i][j].length != zLen) {
                    throw new DimensionMismatchException(d2FdXdY[i][j].length, zLen);
                }
                if (d2FdXdZ[i][j].length != zLen) {
                    throw new DimensionMismatchException(d2FdXdZ[i][j].length, zLen);
                }
                if (d2FdYdZ[i][j].length != zLen) {
                    throw new DimensionMismatchException(d2FdYdZ[i][j].length, zLen);
                }
                if (d3FdXdYdZ[i][j].length != zLen) {
                    throw new DimensionMismatchException(d3FdXdYdZ[i][j].length, zLen);
                }

                final int jp1 = j + 1;
                final double yR = yval[jp1] - yval[j];
                final double xRyR = xR * yR;
                for (int k = 0; k < lastK; k++) {
                    final int kp1 = k + 1;
                    final double zR = zval[kp1] - zval[k];
                    final double xRzR = xR * zR;
                    final double yRzR = yR * zR;
                    final double xRyRzR = xR * yRzR;

                    final double[] beta = new double[] {
                        f[i][j][k], f[ip1][j][k],
                        f[i][jp1][k], f[ip1][jp1][k],
                        f[i][j][kp1], f[ip1][j][kp1],
                        f[i][jp1][kp1], f[ip1][jp1][kp1],

                        dFdX[i][j][k] * xR, dFdX[ip1][j][k] * xR,
                        dFdX[i][jp1][k] * xR, dFdX[ip1][jp1][k] * xR,
                        dFdX[i][j][kp1] * xR, dFdX[ip1][j][kp1] * xR,
                        dFdX[i][jp1][kp1] * xR, dFdX[ip1][jp1][kp1] * xR,

                        dFdY[i][j][k] * yR, dFdY[ip1][j][k] * yR,
                        dFdY[i][jp1][k] * yR, dFdY[ip1][jp1][k] * yR,
                        dFdY[i][j][kp1] * yR, dFdY[ip1][j][kp1] * yR,
                        dFdY[i][jp1][kp1] * yR, dFdY[ip1][jp1][kp1] * yR,

                        dFdZ[i][j][k] * zR, dFdZ[ip1][j][k] * zR,
                        dFdZ[i][jp1][k] * zR, dFdZ[ip1][jp1][k] * zR,
                        dFdZ[i][j][kp1] * zR, dFdZ[ip1][j][kp1] * zR,
                        dFdZ[i][jp1][kp1] * zR, dFdZ[ip1][jp1][kp1] * zR,

                        d2FdXdY[i][j][k] * xRyR, d2FdXdY[ip1][j][k] * xRyR,
                        d2FdXdY[i][jp1][k] * xRyR, d2FdXdY[ip1][jp1][k] * xRyR,
                        d2FdXdY[i][j][kp1] * xRyR, d2FdXdY[ip1][j][kp1] * xRyR,
                        d2FdXdY[i][jp1][kp1] * xRyR, d2FdXdY[ip1][jp1][kp1] * xRyR,

                        d2FdXdZ[i][j][k] * xRzR, d2FdXdZ[ip1][j][k] * xRzR,
                        d2FdXdZ[i][jp1][k] * xRzR, d2FdXdZ[ip1][jp1][k] * xRzR,
                        d2FdXdZ[i][j][kp1] * xRzR, d2FdXdZ[ip1][j][kp1] * xRzR,
                        d2FdXdZ[i][jp1][kp1] * xRzR, d2FdXdZ[ip1][jp1][kp1] * xRzR,

                        d2FdYdZ[i][j][k] * yRzR, d2FdYdZ[ip1][j][k] * yRzR,
                        d2FdYdZ[i][jp1][k] * yRzR, d2FdYdZ[ip1][jp1][k] * yRzR,
                        d2FdYdZ[i][j][kp1] * yRzR, d2FdYdZ[ip1][j][kp1] * yRzR,
                        d2FdYdZ[i][jp1][kp1] * yRzR, d2FdYdZ[ip1][jp1][kp1] * yRzR,

                        d3FdXdYdZ[i][j][k] * xRyRzR, d3FdXdYdZ[ip1][j][k] * xRyRzR,
                        d3FdXdYdZ[i][jp1][k] * xRyRzR, d3FdXdYdZ[ip1][jp1][k] * xRyRzR,
                        d3FdXdYdZ[i][j][kp1] * xRyRzR, d3FdXdYdZ[ip1][j][kp1] * xRyRzR,
                        d3FdXdYdZ[i][jp1][kp1] * xRyRzR, d3FdXdYdZ[ip1][jp1][kp1] * xRyRzR,
                    };

                    splines[i][j][k] = new TricubicFunction(computeCoefficients(beta));
                }
            }
        }
    }

    /**
     * {@inheritDoc}
     *
     * @throws OutOfRangeException if any of the variables is outside its interpolation range.
     */
    public double value(double x, double y, double z)
        throws OutOfRangeException {
        final int i = searchIndex(x, xval);
        if (i == -1) {
            throw new OutOfRangeException(x, xval[0], xval[xval.length - 1]);
        }
        final int j = searchIndex(y, yval);
        if (j == -1) {
            throw new OutOfRangeException(y, yval[0], yval[yval.length - 1]);
        }
        final int k = searchIndex(z, zval);
        if (k == -1) {
            throw new OutOfRangeException(z, zval[0], zval[zval.length - 1]);
        }

        final double xN = (x - xval[i]) / (xval[i + 1] - xval[i]);
        final double yN = (y - yval[j]) / (yval[j + 1] - yval[j]);
        final double zN = (z - zval[k]) / (zval[k + 1] - zval[k]);

        return splines[i][j][k].value(xN, yN, zN);
    }

    /**
     * Indicates whether a point is within the interpolation range.
     *
     * @param x First coordinate.
     * @param y Second coordinate.
     * @param z Third coordinate.
     * @return {@code true} if (x, y, z) is a valid point.
     */
    public boolean isValidPoint(double x, double y, double z) {
        if (x < xval[0] ||
            x > xval[xval.length - 1] ||
            y < yval[0] ||
            y > yval[yval.length - 1] ||
            z < zval[0] ||
            z > zval[zval.length - 1]) {
            return false;
        } else {
            return true;
        }
    }

    /**
     * @param c Coordinate.
     * @param val Coordinate samples.
     * @return the index in {@code val} corresponding to the interval containing {@code c}, or {@code -1}
     *   if {@code c} is out of the range defined by the end values of {@code val}.
     */
    private int searchIndex(double c, double[] val) {
        if (c < val[0]) {
            return -1;
        }

        final int max = val.length;
        for (int i = 1; i < max; i++) {
            if (c <= val[i]) {
                return i - 1;
            }
        }

        return -1;
    }

    /**
     * Compute the spline coefficients from the list of function values and
     * function partial derivatives values at the four corners of a grid
     * element. They must be specified in the following order:
     * <ul>
     *  <li>f(0,0,0)</li>
     *  <li>f(1,0,0)</li>
     *  <li>f(0,1,0)</li>
     *  <li>f(1,1,0)</li>
     *  <li>f(0,0,1)</li>
     *  <li>f(1,0,1)</li>
     *  <li>f(0,1,1)</li>
     *  <li>f(1,1,1)</li>
     *
     *  <li>f<sub>x</sub>(0,0,0)</li>
     *  <li>... <em>(same order as above)</em></li>
     *  <li>f<sub>x</sub>(1,1,1)</li>
     *
     *  <li>f<sub>y</sub>(0,0,0)</li>
     *  <li>... <em>(same order as above)</em></li>
     *  <li>f<sub>y</sub>(1,1,1)</li>
     *
     *  <li>f<sub>z</sub>(0,0,0)</li>
     *  <li>... <em>(same order as above)</em></li>
     *  <li>f<sub>z</sub>(1,1,1)</li>
     *
     *  <li>f<sub>xy</sub>(0,0,0)</li>
     *  <li>... <em>(same order as above)</em></li>
     *  <li>f<sub>xy</sub>(1,1,1)</li>
     *
     *  <li>f<sub>xz</sub>(0,0,0)</li>
     *  <li>... <em>(same order as above)</em></li>
     *  <li>f<sub>xz</sub>(1,1,1)</li>
     *
     *  <li>f<sub>yz</sub>(0,0,0)</li>
     *  <li>... <em>(same order as above)</em></li>
     *  <li>f<sub>yz</sub>(1,1,1)</li>
     *
     *  <li>f<sub>xyz</sub>(0,0,0)</li>
     *  <li>... <em>(same order as above)</em></li>
     *  <li>f<sub>xyz</sub>(1,1,1)</li>
     * </ul>
     * where the subscripts indicate the partial derivative with respect to
     * the corresponding variable(s).
     *
     * @param beta List of function values and function partial derivatives values.
     * @return the spline coefficients.
     */
    private double[] computeCoefficients(double[] beta) {
        final int sz = 64;
        final double[] a = new double[sz];

        for (int i = 0; i < sz; i++) {
            double result = 0;
            final double[] row = AINV[i];
            for (int j = 0; j < sz; j++) {
                result += row[j] * beta[j];
            }
            a[i] = result;
        }

        return a;
    }
}

/**
 * 3D-spline function.
 *
 */
class TricubicFunction
    implements TrivariateFunction {
    /** Number of points. */
    private static final short N = 4;
    /** Coefficients */
    private final double[][][] a = new double[N][N][N];

    /**
     * @param aV List of spline coefficients.
     */
    TricubicFunction(double[] aV) {
        for (int i = 0; i < N; i++) {
            for (int j = 0; j < N; j++) {
                for (int k = 0; k < N; k++) {
                    a[i][j][k] = aV[i + N * (j + N * k)];
                }
            }
        }
    }

    /**
     * @param x x-coordinate of the interpolation point.
     * @param y y-coordinate of the interpolation point.
     * @param z z-coordinate of the interpolation point.
     * @return the interpolated value.
     * @throws OutOfRangeException if {@code x}, {@code y} or
     * {@code z} are not in the interval {@code [0, 1]}.
     */
    public double value(double x, double y, double z)
        throws OutOfRangeException {
        if (x < 0 || x > 1) {
            throw new OutOfRangeException(x, 0, 1);
        }
        if (y < 0 || y > 1) {
            throw new OutOfRangeException(y, 0, 1);
        }
        if (z < 0 || z > 1) {
            throw new OutOfRangeException(z, 0, 1);
        }

        final double x2 = x * x;
        final double x3 = x2 * x;
        final double[] pX = { 1, x, x2, x3 };

        final double y2 = y * y;
        final double y3 = y2 * y;
        final double[] pY = { 1, y, y2, y3 };

        final double z2 = z * z;
        final double z3 = z2 * z;
        final double[] pZ = { 1, z, z2, z3 };

        double result = 0;
        for (int i = 0; i < N; i++) {
            for (int j = 0; j < N; j++) {
                for (int k = 0; k < N; k++) {
                    result += a[i][j][k] * pX[i] * pY[j] * pZ[k];
                }
            }
        }

        return result;
    }
}
