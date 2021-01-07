
/*@ predicate Swap{L1,L2}(int *a, integer l, integer i, integer j) =
     \at(a[i],L1) == \at(a[j],L2) &&
     \at(a[j],L1) == \at(a[i],L2) &&
     \forall integer k; k != i && k != j
         ==> \at(a[k],L1) == \at(a[k],L2);
  */
/*@
    predicate Sorted{L}(int* arr, integer length) =
    \forall integer i,j;
        0 <= i <= j < length ==> arr[i] <= arr[j];
*/
/*@
    predicate Permut{L}(int* arr, integer length) =
    \forall integer i;
        0 <= i < length ==> arr[i] == 0;
*/
/*@
     predicate isOkay{L}(int* arr, integer length) =
    \forall integer i;
        0 <= i < length ==> arr[i] >=0 && arr[i] <=2;
*/
//---------------------------------------------------

/*@
   
    assigns t[i],t[j];
    ensures t[j] == \old(t[i])&& t[i] == \old(t[j]);
    ensures Swap{Old,Here}(t,n,i,j);
*/
void swap(int *t, int n, int i,int j){
  int tmp;
  tmp = t[i];
  t[i] = t[j];
  t[j] = tmp;
  return;
}

 

/*@	requires n>0;

    requires valid: \valid_read(t+(0..n-1));
     
    behavior sorted:
    	
      assigns t[0..n-1];
        ensures Sorted(t,n) && isOkay(t,n);
       
    behavior permutation:
      assigns t[0..n-1];
        ensures Permut(t,n);
     
    complete behaviors;                                                         
    disjoint behaviors;
  */

 

void sort(int *t, int n){
  int i;
  int ok = 1;
//@assert ok == 1;
 

/*@
    loop invariant bound: 0 <= i <= n;
   
    loop invariant \exists integer p; 0 <= p <i &&  t[p]>2 ==> ok == 0;
    loop invariant \exists integer q; 0 <= q <i &&  t[q]<0 ==> ok == 0;
    loop invariant \forall integer b; 0 <= b <i &&  (t[b] <0 && t[b] > 2) ==> ok == 0;
    loop invariant \exists integer x; 0 <= x <i &&  t[x]==0 ==> ok == 1;
    loop invariant \exists integer y; 0 <= y <i &&  t[y]==1 ==> ok == 1;
    loop invariant \exists integer z; 0 <= z <i &&  t[z]==2 ==> ok == 1;
    
    loop invariant check_ok: \exists integer k; 0 <= k <i ==>  (t[k] != 0 && t[k] != 1 && t[k] != 2) && ok == 0 ||(t[k] == 0 && t[k] == 1 && t[k] == 2) && ok == 1;  
    
    loop invariant \forall integer i ; t[i] == 0||1||2 && ok == 1;
    
    loop assigns i,ok;
    loop variant n-i;
*/

 

  for(i=0;i<n;i++){
  
    if (t[i] != 0 && t[i] != 1 && t[i] != 2) {
      ok = 0;
      //@ assert ok==0;
    }
  }
  
   

 

  if (ok == 0) {
   //@ assert ok==0;
/*@
    loop invariant bound: 0 <= i <= n;
    loop invariant belong_3_values: \forall integer k; 0 <= k < i ==> t[k] == 0;
    loop assigns i,t[0..n-1];
    loop variant n-i;
*/

 

    for(i=0;i<n;i++){
      t[i] = 0;
      
/*
      @assert t[i]==0;
     
*/

 

    }
// @assert \forall integer i; t[i] == 0;
 

  } else {
   //@assert ok == 1;
    int zeros = 0;
    int twos = n-1;
    i = 0;
/*@
loop invariant 0 <= i <= twos+1;
	loop invariant \exists integer j; 0 <=  j <= twos ==>  t[j] ==1;
	
	loop invariant \exists integer k; 0 <=  k <= twos ==>  t[k] ==0;
	 
	  loop invariant \exists integer k; 0 <=  k <= twos ==>  t[k] !=0 && t[k]!=2;
    loop invariant \exists integer l; 0 <=  l <= twos ==>  t[l] ==2;
    
   loop invariant \exists integer p; 0<= p <= twos ==> t[p]!=0 && ok == 1;
  
	 loop assigns i,zeros,twos, t[0..n-1];
	loop variant twos - i + 1;
   
*/

 


    while (i <= twos) {
      if (t[i] == 0) {

 

    swap(t,n,zeros,i);
    //@assert t[zeros]==0;
    
    zeros++;
  
    i++;
      }
       else if (t[i] == 2) {

    swap(t,n,twos,i);
    //@assert t[twos]==2;
   
    
    
    twos--;
      }
      else {
        i++;
 	}
    }
  }
  return;
}

 


