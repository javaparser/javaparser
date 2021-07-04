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
 * This package contains implementations of the
 * {@link org.apache.commons.collections4.BidiMap BidiMap},
 * {@link org.apache.commons.collections4.OrderedBidiMap OrderedBidiMap} and
 * {@link org.apache.commons.collections4.SortedBidiMap SortedBidiMap} interfaces.
 * A BidiMap is an extension to Map that allows keys and values to be looked up with equal ease.
 * One example usage is a system communicating to a legacy datasource that must convert codes
 * from the new format to the old format and vice versa.
 * <p>
 * The following implementations are provided in the package:
 * <ul>
 *   <li>DualHashBidiMap - uses two HashMaps to implement BidiMap
 *   <li>DualLinkedHashBidiMap - uses two LinkedHashMaps to implement BidiMap
 *   <li>DualTreeBidiMap - uses two TreeMaps to implement SortedBidiMap
 *   <li>TreeBidiMap - red-black tree implementation of OrderedBidiMap
 * </ul>
 * <p>
 * The following decorators are provided in the package:
 * <ul>
 *   <li>Unmodifiable - ensures the map cannot be altered
 * </ul>
 *
 */
package org.apache.commons.collections4.bidimap;
