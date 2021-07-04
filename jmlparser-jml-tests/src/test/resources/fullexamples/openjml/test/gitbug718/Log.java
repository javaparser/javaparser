public class Log {


/*@ 
 	requires 0 < ii <= 1024 < Integer.MAX_VALUE/2;
      //  ensures 0 <= \result < ii;
 //	ensures (ii >> \result) == 1;
        ensures (1 << \result) <= ii < (1 << (\result+1));
 @*/
public static final /*@ pure function @*/ int log2(int ii) {
	int log = 0;
	/*@
	 decreasing ii-1;
         loop_invariant log == \count;
	 loop_invariant ii == (\old(ii)>>log);
	 loop_invariant 1 <= ii;
	 loop_invariant ii*(1<<log) <= \old(ii) < ii*(1<<(log+1));
         loop_writes ii, log;
	 @*/
	while(ii > 1) {
		ii = ii>>1;
		log++;
	}
        //@ assert ii == 1;
	//@ assert ii*(1<<log) <= \old(ii) < ii*(1<<(log+1));
	return log;
}


}
