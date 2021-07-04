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

package org.apache.commons.math3.random;

/**
 * This interface represent a normalized random generator for
 * scalars.
 * Normalized generator provide null mean and unit standard deviation scalars.
 * @since 1.2
 */
public interface NormalizedRandomGenerator {

  /** Generate a random scalar with null mean and unit standard deviation.
   * <p>This method does <strong>not</strong> specify the shape of the
   * distribution, it is the implementing class that provides it. The
   * only contract here is to generate numbers with null mean and unit
   * standard deviation.</p>
   * @return a random scalar with null mean and unit standard deviation
   */
  double nextNormalizedDouble();

}
