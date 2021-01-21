/*@
	assigns t[i], t[j];
	ensures t[i] == \old(t[j]) && t[j] == \old(t[i]);
	ensures \forall integer k; 0 <= k < n && k != i && k != j ==> \old(t[k]) == t[k];
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
      (head <= i < tail-1 && i < j < tail) ==> arr[i] <= arr[j];
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
    loop invariant ok == 0 ==> (\exists integer j; 0 <= j < i ==> (t[j] != 0 && t[j] != 1 && t[j] != 2));
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
//@assert \forall integer k; 0 <= k < n==> (t[k] == 0 ||t[k] == 1 || t[k] == 2);

    int zeros = 0;
    int twos = n-1;
    i = 0;
    
/*@
	loop assigns i,zeros,twos, t[0..n-1];
	loop invariant 0 <= i <= twos+1;
	loop invariant 0<=zeros <= i;
  	loop invariant (i-1)<=twos<n;
  	loop invariant \forall integer a; 0 <= a < zeros ==> t[a] == 0;
  	loop invariant \forall integer a; zeros <= a < i ==> t[a] == 1;
  	loop invariant \forall integer a; twos < a < n ==> t[a] == 2;
  	loop invariant \forall integer a; zeros <= a <= twos ==> (t[a] == 0 ||t[a] == 1 || t[a] == 2);
  	loop variant twos-i ;
*/

    while (i <= twos) {
    
//@assert (t[i] == 0 ||t[i] == 1 || t[i] == 2);

      if (t[i] == 0) {
      
//@assert (t[zeros] == 0 ||t[zeros] == 1 || t[zeros] == 2);

    swap(t,n,zeros,i);
    
//@assert t[zeros] == 0;
//@assert (t[i] == 0 ||t[i] == 1 || t[i] == 2);

    zeros++;
    i++;
      }
       else if (t[i] == 2) {
       
//@assert (t[twos] == 0 ||t[twos] == 1 || t[twos] == 2);

    swap(t,n,twos,i);
    
//@assert t[twos]==2;
//@assert (t[i] == 0 ||t[i] == 1 || t[i] == 2);
   
    twos--;
      }
      else {
      
//@assert (t[i] == 1);

        i++;
        
//assert (t[i] == 0 ||t[i] == 1 || t[i] == 2);

 	}
    }
    
//@assert \forall integer k; 0 <= k < n==>(t[k] == 0 ||t[k] == 1 || t[k] == 2);
    
  }
  return;
}

#include <stdio.h>

/*@
	requires valid: \valid_read(t+(0..l-1));
	requires l>=0;
	assigns \nothing;
*/

void display(int *t, int l) {
  int i;
  
/*@
   	assigns \nothing;
*/

  printf("{ ");

/*@
  	loop invariant bound: 0 <= i <= l;
  	loop assigns i;
  	loop variant l-i-1;
*/
  
  for(i=0;i<l-1;i++) {
  
/*@
  	assigns \nothing;
*/

    printf("%d, ",t[i]);

  }

/*@
  	assigns \nothing;
*/

  printf("%d}\n",t[i]);
  return;
}

/* always test    *
 * before proving */
int main() {
  int t[10] = {2,1,0,2,1,1,2,1,1,0};
  sort(t,10);
  display(t,10);
  return 0;
}


