verification_gen_loop_inv = """\
ACSL is a specification language for C programs that conforms to the design by contract paradigm, utilizing Hoare style pre- and postconditions and invariants.\
You are an expert in program verification, and please generate loop invariant as C annotation comments at the infill location (annotated by "/* @ >>> INFILL <<< */") using ACSL language.\
Note that the `loop invariant` clause is a condition that is true at the beginning and end of every loop iteration.\
The `loop assign` is a condition that describes the set of variables modified by the loop.\
Just show me the loop invariant and don't explain it.
"""


gen_loop_example_1_question = """\
#include <stdlib.h>

static void mbedtls_zeroize(void *v, size_t n, int q, int w) {

  char *p = v;
  int x = 1;
  int y = 1;
  int a = q;
  int b = w;
  /* @ >>> INFILL <<< */
  for(int i=0; i<n ; i++) {
    p[i] = 0;
    
    int t1 = x;
    int t2 = y;
    x = t1 + t2;
    y = t1 + t2;

    a--;
    b--;
  }
}
"""


gen_loop_example_1_answer = """\
loop invariant 0 <= i <= n;
loop invariant x == y; 
loop invariant x >= 1;
loop invariant y >= 1;
loop invariant a - b == q - w;
loop invariant \\forall integer j; 0 <= j < i ==> ((char*)p)[j] == 0;
loop assigns ((char*)p)[0..n-1];
loop assigns i;
loop assigns a;
loop assigns b;
loop assigns x;
loop assigns y;
"""


gen_loop_example_2_question = """\
int arraymax(int* a, int* b, int n) {
  int i = 0;
  int max = a[0];
  int j = n;
  int k = n;

  /* @ >>> INFILL <<< */
  while (i < n) {
    b[i] = b[i] * 2;

    if (max < a[i])
      max = a[i];
    i = i + 1;

    j--;
    k--;
  }
  return max;
}
"""


gen_loop_example_2_answer = """\
loop invariant 0 <= i <= n;
loop invariant \\forall integer k;  0 <= k < i ==> max >=  a[k];
loop invariant \\exists integer k;  0 <= k < i &&  max == a[k];
loop invariant \\forall integer k; p <= k < n ==> b[k] == k;
loop invariant \\forall integer k; 0 <= k < i ==> b[k] == 2*k;
loop invariant j == k;
loop assigns i;
loop assigns max;
loop assigns a[0..n-1];
"""


gen_loop_example_3_question = """\
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define SIZE 10

int foo(uint32_t *map, uint32_t *key, uint32_t len)
{
    int ret = -1;
    int x = 1;
    int y = 0;
    /* @ >>> INFILL <<< */
    for (int i = 0; i < len; i++)
	  {
		    if (map[i] == key[i])
		    {
			      ret = 0;
			      break;
		    }
        x = x + y;
        y = y + 1;
	  }
    //@ assert (x >= y) ;
	  return ret;
}
"""


gen_loop_example_3_answer = """\
loop invariant 0 <= i <= len;
loop invariant ret == -1 || ret == 0;
loop invariant ret == -1 ==> \\forall integer j; 0 <= j < i ==> map[j] != key[j];
loop invariant ret == 0 ==> (\\exists integer j; 0 <= j < i && map[j] == key[j]);
loop invariant y <= x;
loop invariant 1 <= x;
loop invariant 0 <= y;
loop assigns i;
loop assigns y;
loop assigns x;
"""


gen_loop_example_4_question = """\
typedef unsigned int U32;

#define ONE_BYTE 16
#define BYTE_COUNT 1

int isMatch(const U32 *pTmpbits, const U32 *bits)
{
    int ret = 1;

    /* @ >>> INFILL <<< */
    for (int j = 0; j < BYTE_COUNT; ++j) 
    {
        if (pTmpbits[j] != bits[j])
        {
            ret = 0;
            break;
        }
    }
    return ret;
}
"""


gen_loop_example_4_answer = """\
loop invariant 0 <= j <= BYTE_COUNT;
loop invariant ret == 1 || ret == 0;
loop invariant ret == 1 ==> \\forall integer k; 0<= k < BYTE_COUNT ==> ( k < j ==> pTmpbits[k] == bits[k] ); 
loop invariant ret == 0 ==>  pTmpbits[j] != bits[j];
loop assigns j;
"""


gen_loop_example_5_question = """\
#include <assert.h>
int unknown();

int main()
{
	int i = 1;
	int j = 0;
	int z = i - j;
	int x = 0;
	int y = 0;
	int w = 0;

	/* @ >>> INFILL <<< */
	while(unknown()) 
	{
		z += x + y + w;
		y++;
		if (z % 2 == 1) 
		  x++;
		w += 2; 
	}

	// @ assert x==y;
}
"""


gen_loop_example_5_answer = """\
loop invariant x == y;
loop invariant z % 2 == 1;
loop invariant w == 2*y;
loop invariant 0 <= y <= x;
loop assigns x;
loop assigns y;
loop assigns w;
loop assigns z;
"""


gen_loop_example_6_question = """\
void Order(int *a, int n) {
    if (n <= 0) {return;}
    int i, j, temp;

    /* @ >>> INFILL <<< */
    for(i = n-1; i > 0; i--) {
        /*@
        loop invariant 0 <= j <= i < n;
        loop invariant \\forall integer k; 0 <= k <= j ==> a[k] <= a[j];
        loop invariant \\forall integer k; 0 <= k < i+1 <= n-1 ==> a[k] <= a[i+1];
        loop invariant \\forall integer k; 0 <= k < i+1 <= n-1 ==> a[k] <= a[i+1];
        loop assigns temp;
        loop assigns j;
        loop assigns a[0..i];
        */
        for(j=0; j<i; j++) {
            if (a[j] > a[j+1]) {
                temp = a[j];
                a[j] = a[j+1];
                a[j+1] = temp;
            }
        }
    }
}

void main() {
    int a[5] = {10, 9, 8, 7, 6};
    Order(a, 5);
    //@ assert \\forall int i; 0 <= i < 4 ==> a[i] <= a[i+1];
}
"""

gen_loop_example_6_answer = """\
loop invariant 0 <= i < n;
loop invariant 0 <= i;
loop invariant i < n;
loop invariant \\forall integer k; 0 <= k < i+1 <= n-1 ==> a[k] <= a[i+1];
loop invariant \\forall integer k; 0 <= k < i+1 <= n-1 ==> a[k] <= a[i+1];
loop invariant \\forall integer k; 0 <= k < i+1 <= n-1 ==> a[k] <= a[i+1];
loop invariant \\forall integer k; i <= k < n-1 ==> a[k] <= a[k+1];
loop invariant \\forall integer k; i <= k < n-1 ==> a[k] <= a[k+1];
loop assigns temp;
loop assigns j;
loop assigns i;
loop assigns a[0..n-1];
"""


gen_outter_loop_1_question = """\
#include <stdint.h>
#include <stddef.h>

int sep(char* dest, const char* src, size_t count) {
    /* @ >>> INFILL <<< */
    for (size_t i = 0; i < count; ++i) {
        /*@
            loop invariant 0 <= j <= count;
            loop invariant \\separated(dest + i, src + (0..j-1));
            loop assigns j;
        */
        for (size_t j = 0; j < count; ++j) {
            if (dest + i == (char*)(src+j)) return 0;
        }
    }
    return 1;
}
"""

gen_outter_loop_1_answer = """\
loop invariant 0 <= i <= count;
loop invariant \\separated(dest + (0..i-1), src + (0..count-1));
loop assigns i;
"""


gen_outter_loop_2_question = """\
#include <limits.h>

int test(const char*s, unsigned int len) {
	int ret = 0;
	unsigned int i, j;
	char c[2] = {'<','>'};
    
	/* @ >>> INFILL <<< */
	for(i = 0; i < len; i++) {
		/*@
    loop invariant 0 <= j <= 2;
    loop invariant ret == -1 || ret == 0;
    loop invariant (ret == 0) ==> \\forall integer m; 0 <= m < i ==> s[m] != '<' && s[m] != '>';
    loop invariant (ret == 0) ==> \\forall integer m; 0 <= m < j ==> s[i] != c[m];
    loop invariant (ret == -1) ==> \\exists integer m; 0 <= m <= i && (s[m] == '<' || s[m] == '>');
    loop assigns j;
    loop assigns ret;
	  */
		for(j = 0; j < 2; j++) {
			if (s[i] == c[j]) {
				ret = -1;
			}
		}
	}
	return ret;
}

int main() {
	int len = 15;
	char s1[16] = "192.168.0.1";
	int  r1     = test(s1, len);
	//@ assert r1 == 0;
	char s2[16] = "192.168.0<1";
	int  r2     = test(s2, len);
	//@ assert r2 == -1;
}
"""


gen_outter_loop_2_answer = """\
loop invariant 0 <= i <= len;
loop invariant ret == -1 || ret == 0;
loop invariant (ret == 0)  ==> \\forall integer m; 0 <= m < i ==> s[m] != '<' && s[m] != '>';
loop invariant (ret == -1) ==> \\exists integer m; 0 <= m < i && (s[m] == '<' || s[m] == '>');
loop assigns i;
loop assigns j;
loop assigns ret;
"""