/**************************************************************************
 * File name  : SleepingQueue.java
 * 
 * This file is part of our SCJ Level 0 and Level 1 implementation, 
 * based on SCJ Draft, Version 0.79. 16 May 2011.
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
 *   
 * Description: 
 * 
 * Revision history:
 *  date    init  comment
 *  31Jan12 HSO   In this impl., the place with index 0 (zero) is not used.
 *                The methods and algorithms are from Cormen et al.
 *                Introduction to Algorithms. MIT Press. 1990.
 *  29Jan13 HSO   Uses indexes instead of references to ScjProcesses
 *************************************************************************/

package javax.safetycritical;

import icecaptools.IcecapCompileMe;

import javax.safetycritical.annotate.Level;
import javax.safetycritical.annotate.SCJAllowed;
import javax.scj.util.Const;

/**
 * This <code>SleepingQueue</code> class holds the sleeping processes
 * in the <code>PriorityScheduler</code>. <br>
 * Time complexity of the methods <code>insert</code> and 
 * <code>extractMin</code> are O(log n).<br>
 * The class is package protected because it is not part of the SCJ 
 * specification.
 * 
 * @version 1.0; - May 2012
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@viauc.dk</A>
 * 
 * @scjComment 
 *  - implementation issue: infrastructure class; not part of the SCJ specification.
 */
@SCJAllowed(Level.INFRASTRUCTURE)
class SleepingQueue {
	int heapSize;

	protected int[] tree; // index to ScjProcesses

	public SleepingQueue(int size) {
		heapSize = 0;
		tree = new int[size + 1];
		makeEmptyTree(this.tree);
	}

	private void makeEmptyTree(int[] tree) {
		for (int i = 0; i < tree.length; i++)
			tree[i] = -999;
	}

	int parent(int i) {
		return i / 2;
	}

	int left(int i) {
		return 2 * i;
	}

	int right(int i) {
		return 2 * i + 1;
	}

	void exchange(int a, int b) {
		int temp = tree[a];
		tree[a] = tree[b];
		tree[b] = temp;
	}

	void heapify(int i) {
		int l = left(i);
		int r = right(i);

		int smallest;

		if (l <= heapSize
				&& getScjProcess(tree[l]).next
						.compareTo(getScjProcess(tree[r]).next) < 0)
			smallest = l;
		else
			smallest = i;

		if (r <= heapSize
				&& getScjProcess(tree[r]).next
						.compareTo(getScjProcess(tree[smallest]).next) < 0)
			smallest = r;

		if (smallest != i) {
			exchange(i, smallest);
			heapify(smallest);
		}
	}

	public void insert(ScjProcess obj) {
		if (heapSize + 1 == tree.length)
			throw new IndexOutOfBoundsException();

		heapSize++;
		int i = heapSize;
		while (i > 1
				&& getScjProcess(tree[parent(i)]).next.compareTo(obj.next) > 0) {
			tree[i] = tree[parent(i)];
			i = parent(i);
		}
		tree[i] = obj.index;
	}

	@IcecapCompileMe
	public ScjProcess minimum() {
		if (heapSize > 0)
			return getScjProcess(tree[1]);
		else
			return null;
	}

	@IcecapCompileMe
	public ScjProcess extractMin() {
		if (heapSize < 1)
			return null;

		ScjProcess min = getScjProcess(tree[1]);
		tree[1] = tree[heapSize];
		heapSize--;
		heapify(1);

		return min;
	}
	
	@IcecapCompileMe
	private ScjProcess getScjProcess(int processIdx) {
		if (processIdx == -999) {
			return null;
		}
		if (processIdx == -2) {
			return MissionSequencer.missSeqProcess;
		}
		if (processIdx == -1) {
			return ScjProcess.idleProcess;
		}
		
		int missionIndex = processIdx / 20;
		int scjProcessIndex = processIdx % 20;
		return Mission.missionSet[missionIndex].msSetForMission.scjProcesses[scjProcessIndex];
	}
	
	public void remove(ScjProcess obj) {
		if (obj == null)
			return;
		int i = find(obj.index);
		if (i != -999) {
			tree[i] = tree[heapSize];
			heapSize--;
			heapify(i);
		}
	}

	private int find(int value) {
		for (int i = 1; i <= heapSize; i++) {
			if (tree[i] == value)
				return i;
		}
		return -999;
	}

	/**
	 * Print out the contents of the priority queue. For testing only.
	 */
	public void print() {
		devices.Console.println("sQueue size = " + heapSize);
		for (int i = 1; i <= heapSize; i++) {
			//devices.Console.println(tree[i].toString());
			devices.Console.println(getScjProcess(tree[i]).toString());
			//System.out.println(tree[i].toString());
		}
		
		//System.out.println("Count is: " + heapSize);
	}

	// For testing only; old
	public static void main(String[] args) {
		System.out.println("Main to SleepingQueue begin");

		SleepingQueue queue = new SleepingQueue(
				Const.DEFAULT_SLEEPING_QUEUE_SIZE);

		int n = 5;
		// int id = 1;
		for (int i = 0; i < n; i++) {
			// queue.insert(new ScjProcess (id++, new AbsoluteTime (i,0)));
			// queue.insert(new ScjProcess (id++, new AbsoluteTime (i,0)));
		}

		queue.print();

		for (int i = 0; i < 2 * n; i++) {
			System.out.println("====== remove ======");
			ScjProcess process = queue.extractMin();
			System.out.println("Removed: " + process);
			// queue.print();
		}
	}
}
