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
 * {@link org.apache.commons.collections4.Closure Closure},
 * {@link org.apache.commons.collections4.Predicate Predicate},
 * {@link org.apache.commons.collections4.Transformer Transformer} and
 * {@link org.apache.commons.collections4.Factory Factory} interfaces.
 * These provide simple callbacks for processing with collections.
 * <p>
 * <b>WARNING:</b> from v4.1 onwards several unsafe classes in this package
 * will not be serializable anymore in order to prevent potential remote
 * code execution exploits.
 * <p>
 * Classes considered to be unsafe are:
 * <ul>
 * <li>CloneTransformer</li>
 * <li>ForClosure</li>
 * <li>InstantiateFactory</li>
 * <li>InstantiateTransformer</li>
 * <li>InvokerTransformer</li>
 * <li>PrototypeFactory$PrototypeCloneFactory</li>
 * <li>PrototypeFactory$PrototypeSerializationFactory</li>
 * <li>WhileClosure</li>
 * </ul>
 *
 */
package org.apache.commons.collections4.functors;
