// Copyright (C) 2011 Daniel Bruns
// Published under Modified BSD License
// See LICENSE for details.


package vacid0.redblacktree;

/**
 * Implementation of a red-black tree.
 * A red-black tree is defined as a binary search tree with the properties:
 * <ul><li>Every node is either red or black.
 * <li>The root is black.
 * <li>Every leaf is black.
 * <li>If a node is red, then both its children are black.
 * <li>For each node, all path from the node to descendant leaves contain the same number of black nodes.
 * </ul>
 * Specification uses a ghost field of type \seq to have an abstract view on the tree.
 * @author bruns
 *
 */
public class RedBlackTree implements AbstractMap {

    final private int deefolt;
    //@ private represents defaultValue = deefolt;

    private Node root;
    /*@ private invariant !root.isRed;
      @ private invariant root.parent == Node.NIL;
      @ private invariant root.redBlackInvariant;
      @ private invariant Node.NIL.staticInv;
      @*/

    //@ private ghost \seq theNodes;
    //@ private invariant (\forall Node x; \contains(theNodes,x) <==> \contains(root.subtree,x));

    /*@ private represents contents \such_that (\forall int i; 0 <= i && i < contents.length;
      @            contents[i] == (get(i) == Node.NIL ? deefolt : get(i).value));
      @ private represents footprint = theNodes, root, root.treeFootprint;
      @ accessible contents : \singleton(theNodes);
      @ accessible \inv : footprint;
      @ accessible footprint : footprint;
      @*/
    
    
    /** Constructs RB tree with default value.
     * @param d default value */
    /*@ normal_behavior
      @ requires Node.NIL.staticInv;
      @ ensures deefolt == d && root == Node.NIL;
      @ ensures theNodes == \seq_empty;
      @ ensures \fresh(footprint);
      @*/
    public /*@ pure @*/ RedBlackTree (int d){
        deefolt = d;
        //@ set theNodes = \seq_empty;
        root = Node.NIL;
    }
    

    /*@ normal_behavior
      @ requires \contains(theNodes,z);
      @ ensures theNodes == \old(\seq_concat(\seq_sub(theNodes, 0, \indexOf(theNodes,z)-1),\seq_sub(theNodes, \indexOf(theNodes,z)+1, theNodes.length-1)));
      @ ensures footprint == \old(\set_minus(footprint, z.footprint));
      @ assignable footprint;
      @*/
    private void delete(Node z) {
        Node y = (z.left == Node.NIL || z.right == Node.NIL) ? z : treeSuccessor(z);
        Node x = (y.left != Node.NIL) ? y.left : y.right;
        x.parent = y.parent;
        if (y.parent == Node.NIL) {
            root = x;
        } else if (y == y.parent.left) {
            y.parent.left = x;
        } else {
            y.parent.right = x;
        }
        if (y != z) {
            z.key = y.key;
        }
        //TODO set height
        /*@ ghost int idx;
          @ set idx = \indexOf(theNodes,z);
          @ set theNodes = \seq_concat(\seq_sub(theNodes, 0, idx-1),\seq_sub(theNodes, idx+1, \seq_length(theNodes)-1));
          @*/
        if (!y.isRed){
            deleteFix(x);
        }
    }

    /*@ normal_behavior
      @ requires !x.parent.isRed && x.parent != Node.NIL;
      @ requires \invariant_for(x.parent) && x.redBlackInvariant;
      @ ensures \invariant_for(this);
      @ ensures footprint == \old(footprint);
      @ ensures theNodes == \old(theNodes);
      @ assignable footprint;
      @*/
    private /*@ helper @*/ void deleteFix(Node x) {
        Node w;
        /*@ maintaining x.redBlackInvariant;
          @ maintaining \invariant_for(root);
          @ maintaining footprint == \old(footprint);
          @ decreasing root.height - x.height;
          @*/
        while (x != root && !x.isRed){
            if (x == x.parent.left) {
               w = x.parent.right;
               if (w.isRed) {
                   w.isRed = false;
                   x.parent.isRed = true;
                   leftRotate(x.parent);
                   w = x.parent.right;
               }
               if (!w.left.isRed && !w.right.isRed){
                   w.isRed = true;
                   x = x.parent;
               } else {
                   if (!w.right.isRed) {
                   w.right.isRed = false;
                   w.isRed = true;
                   rightRotate(w);
                   w = x.parent.right;
                   }
                   w.isRed = x.parent.isRed;
                   x.parent.isRed = false;
                   w.right.isRed = false;
                   leftRotate(x.parent);
                   x = root;
               }
            } else {
                w = x.parent.left;
                if (w.isRed) {
                    w.isRed = false;
                    x.parent.isRed = true;
                    rightRotate(x.parent);
                    w = x.parent.left;
                }
                if (!w.right.isRed && !w.left.isRed){
                    w.isRed = true;
                    x = x.parent;
                } else {
                    if (!w.left.isRed) {
                    w.left.isRed = false;
                    w.isRed = true;
                    leftRotate(w);
                    w = x.parent.left;
                    }
                    w.isRed = x.parent.isRed;
                    x.parent.isRed = false;
                    w.left.isRed = false;
                    rightRotate(x.parent);
                    x = root;
                }
            }
        }
        x.isRed = false;
    }



    /*@ normal_behavior
      @ ensures (\exists Node n; \contains(theNodes,n) && n.key == key ==> \result == n);
      @ ensures !(\exists Node n; \contains(theNodes,n) && n.key == key) ==> \result == Node.NIL; 
      @*/
    private /*@ pure @*/ Node get(int key){
        Node x = root;
        //@ ghost \seq visited = \seq_empty;
        
        /*@ maintaining 0 <= x.height && x.height <= root.height;
          @ maintaining (\forall int i; 0 <= i && i < visited.length; ((Node)visited[i]).key != key);
          @ maintaining (\forall Node n; \contains(visited,n); \contains(theNodes,n));
          @ maintaining \invariant_for(x);
          @ decreasing x.height;
          @*/
        // XXX still to weak, need to say something about ordering of keys
        while (x != Node.NIL && x.key != key){
            //@ set visited = \seq_concat(visited,\singleton(x));
            if (key < x.key)
                x = x.left;
            else x = x.right;
        }
        return x;
    }


    /** Inserts a node into the tree.
     * The node is first inserted in an appropriate position (according to its key)
     * and colored red. In a second step, the red-black properties are restored
     * by method <code>insertFix()</code>.
     * @param z node to be inserted
     */
    /*@ normal_behavior
      @ requires z != Node.NIL && z.staticInv && z != null && z.key >= 0;
      @ requires !\contains(theNodes,z);
      @ ensures theNodes == \seq_concat(\old(theNodes),\seq_singleton(z));
      @ assignable root, z.parent, z.isRed, theNodes;
      @*/
    private void insert (Node z){
        Node x = root;
        Node y = Node.NIL;
        /*@ maintaining y == Node.NIL || (y == x.parent && (y.left == x ? z.key < y.key : z.key > y.key));
          @ decreasing x.height;
          @*/
        while (x != Node.NIL){
            y = x;
            if (z.key < x.key)
                x = x.left;
            else x = x.right;
        }
        //@ set z.height = 1;
        z.parent = y;
        if (y == Node.NIL)
            root = z;
        else if (z.key < y.key)
            y.left = z;
        else y.right = z;
        z.isRed = true;
        //@ set theNodes = \seq_concat(theNodes,\seq_singleton(z));
        insertFix(z);
    }


    /** &quot;Repairs&quot; the tree so red-black properties hold again; */
    /*@ normal_behavior
      @   requires z != Node.NIL && z.redBlackInvariant;
      @   requires \invariant_for(z.parent);
      @   requires z.isRed;
      @   requires root == z <==> root.isRed;
      @   assignable footprint;
      @   ensures footprint == \old(footprint);
      @   ensures \invariant_for(this);
      @   ensures theNodes == \old(theNodes);
      @ helper
      @*/
    private void insertFix(Node z) {
        /*@ maintaining z.isRed;
          @ maintaining z.parent == root ==> !z.parent.isRed;
          @ maintaining z.redBlackInvariant;
          @ maintaining z.parent == z.parent.parent.left ? z.parent.parent.right.redBlackInvariant : z.parent.parent.left.redBlackInvariant;
          @ maintaining footprint == \old(footprint);
          @ decreasing root.height - z.height;
          @*/
        while (z.parent.isRed) {
            if (z.parent == z.parent.parent.left) {
                Node y = z.parent.parent.right;
                if (y.isRed) {
                    z.parent.isRed = false;
                    y.isRed = false;
                    z.parent.parent.isRed = true;
                    z = z.parent.parent;
                } else {
                    if (z == z.parent.right) {
                        z = z.parent;
                        leftRotate(z);
                    }
                    z.parent.isRed = false;
                    z.parent.parent.isRed = true;
                    rightRotate(z.parent.parent);
                }
            } else {
                Node y = z.parent.parent.left;
                if (y.isRed) {
                    z.parent.isRed = false;
                    y.isRed = false;
                    z.parent.parent.isRed = true;
                    z = z.parent.parent;
                } else {
                    if (z == z.parent.left) {
                        z = z.parent;
                        rightRotate(z);
                    }
                    z.parent.isRed = false;
                    z.parent.parent.isRed = true;
                    leftRotate(z.parent.parent);
                }
            }
        }
        root.isRed = false;
    }


    /*@ normal_behavior
      @   requires x != Node.NIL && x.right != Node.NIL && \invariant_for(x);
      @   ensures x.parent == \old(x.right) && x.right == \old(x.right.left);
      @   ensures x.parent.left == x;     
      @   ensures \old(root) == x || (\exists Node y; y == \old(x.parent); \old(x.parent.left) == x ? (y.left == x.parent && y.right == \old(x.parent.right)) : (y.left == \old(x.parent.left) && y.right == x.parent)); 
      @   ensures root == (\old(root) == x ? x.parent : \old(root));
      @   ensures \invariant_for(x.parent);
      @   assignable root, x.parent, x.parent.left, x.parent.right, x.right, x.right.parent, x.right.left, x.height, x.right.height;
      @ also normal_behavior
      @   requires x != Node.NIL && x.right == Node.NIL;
      @   assignable \nothing;
      @*/
    private /*@ spec_public helper @*/ void leftRotate (Node x){
        Node y = x.right;
        Node p = x.parent;
        if (y != Node.NIL) {
            //@ set y.height = x.height;
            //@ set x.height = x.height -1;
            y.parent = p;
            x.right = y.left;
            y.left = x;

            if (p == Node.NIL){
                root = y; 
            } else {
                if (p.left == x)
                    p.left = y;
                else p.right = y;
            }
        }
    }
    
    // specified by interface
    public int lookup (int key){
        Node x = get(key);
        if (x == Node.NIL)
            return deefolt;
        else return x.value;
    }
   
    // specified by interface
    public void remove (int key){
        final Node n = get(key);
        if (n != Node.NIL) {
            delete(n);
        }
    }


    // specified by interface
    public void replace (int key, int value){
        Node x = get(key);
        if (x == Node.NIL) {
            final  Node n = new Node(key,value);
            insert(n);
        }
        else x.value = value;  
    }

    /*@ normal_behavior
      @   requires x != Node.NIL && \invariant_for(x);
      @   requires x.left != Node.NIL;
      @   ensures \invariant_for(x.parent);
      @   ensures x.parent == \old(x.left) && x.left == \old(x.left.right);
      @   ensures x.parent.left == x;
      @   ensures \old(root) == x || (\exists Node y; y == \old(x.parent); \old(x.parent.left) == x ? (y.left == x.parent && y.right == \old(x.parent.right)) : (y.left == \old(x.parent.left) && y.right == x.parent)); 
      @   ensures root == (\old(root) == x ? x.parent : \old(root));
      @   assignable root, x.parent, x.parent.left, x.parent.right, x.left, x.left.parent, x.left.right, x.height, x.left.height;
      @ also normal_behavior
      @   requires x != Node.NIL && x.left == Node.NIL;
      @   assignable \nothing;
      @*/
    private /*@ helper @*/ void rightRotate (Node x){
        Node y = x.left;
        Node p = x.parent;
        if (y != Node.NIL){
            //@ set y.height = x.height;
            //@ set x.height = x.height -1;
            y.parent = p;
            x.left = y.right;
            y.right = x;
            if (p == Node.NIL)
                root = y;
            else
                if (p.left == x)
                    p.left = y;
                else p.right = y;
        }
    }
    
    /** Returns the left-most node of the right subtree. */
    /*@ normal_behavior
      @   requires z != Node.NIL && \invariant_for(z);
      @   requires z.left != Node.NIL && z.right != Node.NIL;
      @   ensures \result != Node.NIL && \result.left == Node.NIL;
      @   ensures z.key < \result.key && \result.key <= z.right.key;
      @   ensures \contains(z.right.subtree, \result);
      @*/
    private /*@ pure helper @*/ Node treeSuccessor(Node z) {
      Node x = z.right;
      /*@ maintaining z.key < x.key;
        @ maintaining x != Node.NIL;
        @ maintaining z == \old(z);
        @ maintaining \invariant_for(x);
        @ decreasing x.height;
        @*/
      while (x.left != Node.NIL){
          x = x.left;
      }
      return x;
    }
    
    

    // Standard methods (not relevant for verification)
    
    public boolean equals (Object o){
        try {
            RedBlackTree t = (RedBlackTree)o;
            boolean b = (t.deefolt == this.deefolt);
            return b && root.equalSubtree(t.root);
        } catch (Exception e){
            return false;
        }
    }

    public String toString(){
        return new String(root.subtreeToString(0));
    }
 

}
