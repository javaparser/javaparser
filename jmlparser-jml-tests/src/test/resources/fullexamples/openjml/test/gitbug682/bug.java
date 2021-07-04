class bug { 
    //@ forall int oldarr;  
    // want forall int[] oldarr;
    // requires oldarr != arr;
    //  requires oldarr.length == arr.length;
    void demo(int arr[]) 
    { 
 //       ;
    } 
}
