infill_contract_example_1_question = """\
#include <limits.h>

/* @ >>> INFILL <<< */
int abs(int val) {
    if(val < 0) return -val;
    return val;
}

void foo(int a) {
    int b = abs(-42);
    //@ assert b == 42;
    int c = abs(42);
    //@ assert c == 42;
    int d = abs(a);
    int e = abs(INT_MIN);
}
"""


infill_contract_example_1_answer = """\
requires INT_MIN < val <= INT_MAX;    
ensures \\result >= 0;
behavior positive:
    assumes val >= 0;
    ensures \\result == val;
behavior negative:
    assumes val < 0;
    ensures \\result == -val;
assigns \\nothing;
"""


infill_contract_example_2_question = """\
#include <stdio.h>
#include <stdlib.h>

/* @ >>> INFILL <<< */
static void mbedtls_zeroize(void *v, size_t n) {

  char *p = v;
  /*@
    loop invariant 0 <= i <= n;
    loop invariant \forall integer j; 0 <= j < i ==> ((char*)p)[j] == 0;
    loop assigns ((char*)p)[0..n-1];
    loop assigns i;
  */
  for(int i=0; i<n ; i++)
    p[i] = 0;
}
"""


infill_contract_example_2_answer = """\
requires \\valid((char *)(v+(0..n-1)));
requires n > 0;
assigns ((char*)v)[0..n - 1];
ensures \\forall integer i; 0 <= i < n ==> ((char*)v)[i] == 0;
"""


infill_contract_example_3_question = """\
#include <string.h>
#include <stdint.h>
#include <assert.h>

#define SIZE 10

/* @ >>> INFILL <<< */
int foo(uint32_t *map, uint32_t *key, uint32_t len)
{
	int ret = -1;
    /*@
    loop invariant 0 <= i <= len;
    loop invariant ret == -1 || ret == 0;
	loop invariant ret == -1 ==> \forall integer j; 0 <= j < len ==> (j < i ==> map[j] != key[j]);
	loop invariant ret == 0 ==> map[i] == key[i];
    loop assigns i;
	*/
	for (int i = 0; i < len; i++)
	{
		if (map[i] == key[i])
		{
			ret = 0;
			break;
		}
	}
	return ret;
}

int main()
{
    uint32_t *map = malloc(sizeof(uint32_t)*SIZE);
	uint32_t *key = malloc(sizeof(uint32_t)*SIZE);
    memset(map, 0, sizeof(uint32_t)*SIZE);
	memset(key, 0, sizeof(uint32_t)*SIZE);
    key[0] = 1;
	map[0] = 2;

    int ret;
    for (int i = 1; i < SIZE; i++) {
        ret = foo(map, key, i);
    }
    //@ assert ret == 0;
    //@ assert ret == -1;
}
"""


infill_contract_example_3_answer = """\
requires \\valid((uint32_t *)(map+(0..len-1)));
requires \\valid((uint32_t *)(key+(0..len-1)));
requires len <= SIZE;
ensures \\result == -1 ==> \\forall integer i; 0 <= i < len ==> map[i] != key[i];
ensures \\result == 0 ==> \\exists integer i; 0 <= i < len && map[i] == key[i];
assigns \\nothing;
"""


infill_contract_example_4_question = """\
#include <stdint.h>
#include <stddef.h>

/* @ >>> INFILL <<< */
int sep(char* dest, const char* src, size_t count) {
    /*@
    loop invariant 0 <= i <= count;
    loop invariant \\separated(dest + (0..i-1), src + (0..count-1));
    loop assigns i;
    */
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


infill_contract_example_4_answer = """\
ensures \\result <==> \\separated(dest + (0..count-1), src + (0..count-1));
assigns \\nothing;
"""


infill_contract_example_5_question = """\
/* @ >>> INFILL <<< */
void surplus_removal(unsigned x, unsigned y, unsigned* q, unsigned* r) {
    *q = x / y;
    *r = x % y;
}

void main() {
    unsigned a, b;
    surplus_removal(10, 3, &a, &b);
    //@ assert a == 3;
    //@ assert b == 1;
}
"""


infill_contract_example_5_answer = """\
requires \\valid(q) 
requires \\valid(r);
requires \\separated(q, r);
requires y != 0;
assigns *q, *r;
ensures x == *q * y + *r;
ensures *r < y;
"""


infill_contract_example_6_question = """\
#include <stdio.h>

/* @ >>> INFILL <<< */
int func(int c) {
    int x = c;
    int y = 0;
    /*@
    loop invariant c == x + y;
	loop invariant c < 0 ==> x < 0;
	loop invariant x >= 0 || x == c;
    loop assigns x, y;
    */
    while(x > 0) {
        x = x - 1;
        y = y + 1;
    }
    return y;
}

void main() {
    int t = func(5);
    //@ assert t == 5;
    int b = func(-1);
    //@ assert b == 0;
}
"""


infill_contract_example_6_answer = """\
ensures c > 0 ==> \\result == c;
ensures c == 0 ==> \\result == 0;
ensures c < 0 ==> \\result == 0;
ensures \\result == 0 ==> c <= 0;
assigns \\nothing;
"""