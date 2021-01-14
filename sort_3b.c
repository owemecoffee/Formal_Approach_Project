/*@
    assigns t[i],t[j];
    ensures t[j] == \old(t[i])&& t[i] == \old(t[j]);
*/
void swap(int *t, int n, int i,int j){
  int tmp;
  tmp = t[i];
  t[i] = t[j];
  t[j] = tmp;
  return;
}
/*@
    predicate Sorted{L}(int* arr, integer head, integer tail) =
    \forall integer i;  \forall integer j;
      (head <= i < tail-1 && i < j < tail) ==> ( (arr[i] == 0 ||arr[i] == 1 || arr[i] == 2)  && (arr[j] == 0 ||arr[j] == 1 || arr[j] == 2) && arr[i] <= arr[j]);
*/
/*@
    predicate AllZero{L}(int* arr, integer length) =
    \forall integer i;
        0 <= i < length ==> arr[i] == 0;
*/

 

/*@
    requires valid: \valid_read(t+(0..n-1));
    requires n >= 0;
    behavior Is_Sorted:
        assumes \forall integer k; 0 <= k <n ==> (t[k] == 0 ||t[k] == 1 || t[k] == 2);
        assigns t[0..n-1];
        ensures Sorted(t,0,n);
    behavior All_Zero:
        assumes \exists integer k; 0 <= k <n && (t[k] != 0 && t[k] != 1 && t[k] != 2);    
        assigns t[0..n-1];
        ensures AllZero(t,n);
    complete behaviors;                                                         
    disjoint behaviors;
  */

 

void sort(int *t, int n){
  int i;
  int ok = 1;
//@ assert ok==1;

/*@
    loop invariant bound: 0 <= i <= n;
    loop invariant one_zero: ok==0 || ok==1;
    loop invariant ok == 1 ==> (\forall integer k; 0 <= k < i ==> (t[k] == 0 ||t[k] == 1 || t[k] == 2));
    loop assigns i,ok;
    loop variant n-i;
*/

 
  for(i=0;i<n;i++){
	//@assert (ok==0 || ok==1);
    if (t[i] != 0 && t[i] != 1 && t[i] != 2) {
      ok = 0;
      //@assert ok==0;
    }
  }

//@assert (ok==0 || ok==1);

  if (ok == 0) {
  
/*@
    loop invariant bound: 0 <= i <= n;
    loop invariant is_zero: \forall integer k; 0 <= k < i ==> t[k] == 0;
    loop assigns i,t[0..n-1];
    loop variant n-i;
*/

 

    for(i=0;i<n;i++){
      t[i] = 0;
      
/*@
      assert t[i]==0;
*/

 

    }
//@ assert AllZero(t,n);
 

  } else {
//@assert  ok==1;
//@assert \forall integer k; 0 <= k < n==>(t[k] == 0 ||t[k] == 1 || t[k] == 2);

    int zeros = 0;
    int twos = n-1;
    i = 0;
/*@
	loop invariant 0 <= i <= twos+1;
	loop invariant Sorted(t,0,i);
	loop invariant zeros > 0 ==> \forall integer j; 0 <=  j < zeros ==>  t[j] == 0;
    loop invariant \forall integer l; zeros <=  l < i ==>  t[l] == 1;
    loop invariant \forall integer m; twos <  m < n ==>  t[m] == 2;
	loop assigns i,zeros,twos, t[0..n-1];
	loop variant twos - i + 1;
*/

 


    while (i <= twos) {

      if (t[i] == 0) {

 

    swap(t,n,zeros,i);
    //@assert t[zeros] == 0;
    
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

 

