class SITA3{
   /*@ public normal_behaviour
     @  ensures  
     @    a[pos1]  == \old(a[pos2]) &&
     @    a[pos2]  == \old(a[pos1]);
     @*/
    public void  swap(int[] a,int pos1, int pos2) {
	int temp;
        temp = a[pos1]; a[pos1] = a[pos2] ; a[pos2] = temp;
    }
}