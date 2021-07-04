/**************************************************************************
 * File name  : StorageParameters.java
 * 
 * This file is part a SCJ Level 0 and Level 1 implementation, 
 * based on SCJ Draft, Version 0.94 25 June 2013.
 *
 * It is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as  
 * published by the Free Software Foundation, either version 3 of the 
 * License, or (at your option) any later version.
 *
 * This SCJ Level 0 and Level 1 implementation is distributed in the hope 
 * that it will be useful, but WITHOUT ANY WARRANTY; without even the  
 * implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  
 * See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this SCJ Level 0 and Level 1 implementation.  
 * If not, see <http://www.gnu.org/licenses/>.
 *
 * Copyright 2012 
 * @authors  Anders P. Ravn, Aalborg University, DK
 *           Stephan E. Korsholm and Hans S&oslash;ndergaard, 
 *             VIA University College, DK
 *************************************************************************/
package javax.safetycritical;

import javax.safetycritical.annotate.SCJAllowed;

/**
 * @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 * 
 * @scjComment
 *  - The suggested arguments <code>messageLength</code> and <code>stackTraceLength</code>
 *    are vendor specific, thus might be included in <code>sizes</code>. 
 */
@SCJAllowed
public final class StorageParameters extends javax.realtime.MemoryParameters {
	
	long totalBackingStore;
	long[] configurationSizes;
	int messageLength;
	int stackTraceLength;
	long maxMissionMemory;

	/**
	 * 
	 * @param totalBackingStore size of the backing store reservation for 
	 *   worst-case scope usage by the associated <code> ManagedSchedulable</code> object, in bytes
	 * 
	 * @param sizes is an array of parameters for configuring VM resources 
	 *   such as native stack or java stack size. The meanings of the entries
	 *   in the array are vendor specific.
	 *   The array passed in is not stored in the object. <p>
	 */
	@SCJAllowed
	public StorageParameters(long totalBackingStore, long[] sizes,
			int messageLength, int stackTraceLength, long maxMemoryArea,
			long maxImmortal, long maxMissionMemory) 
	{
		super (maxMemoryArea, maxImmortal);
		this.totalBackingStore = totalBackingStore;
		this.configurationSizes = sizes;
		this.messageLength = messageLength;
		this.stackTraceLength = stackTraceLength;
		this.maxMissionMemory = maxMissionMemory;
	}

	/**
	 * 
	 * @param totalBackingStore size of the backing store reservation for 
	 *   worst-case scope usage by the associated <code> ManagedSchedulable</code> object, in bytes
	 * 
	 * @param sizes is an array of parameters for configuring VM resources 
	 *   such as native stack or java stack size. The meanings of the entries
	 *   in the array are vendor specific.
	 *   The array passed in is not stored in the object. <p>
	 */
	@SCJAllowed
	public StorageParameters(long totalBackingStore, long[] sizes,
			long maxMemoryArea, long maxImmortal, long maxMissionMemory) 
	{
		super (maxMemoryArea, maxImmortal);
		
		this.totalBackingStore = totalBackingStore;
		this.configurationSizes = sizes;
		this.messageLength = 0; // or a default value like 128?
		this.stackTraceLength = 0; // or a default value ?
		this.maxMissionMemory = maxMissionMemory;
	}

	long getMaxMemoryArea() {
		return maxMemoryArea;
	}
	
	long getMaxImmortal() {
		return maxImmortal;
	}
	
	//used in JML annotation only (not public)
	long getBackingStoreSize() {
		return totalBackingStore;
	}
	
//	//used in JML annotation only (not public)
//	long[] getConfigurationSizes() {
//		return configurationSizes;
//	}
}
