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
 * Classes to perform curve fitting.
 *
 * Curve fitting is a special case of a least-squares problem
 * where the parameters are the coefficients of a function \( f \)
 * whose graph \( y = f(x) \) should pass through sample points, and
 * were the objective function is the squared sum of the residuals
 * \( f(x_i) - y_i \) for observed points \( (x_i, y_i) \).
 */
package org.apache.commons.math3.fitting;
