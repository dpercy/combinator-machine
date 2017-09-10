#include <stdint.h>
#include <assert.h>
#include <stdio.h>


#define array_end(arr) (arr + (sizeof(arr)/sizeof(arr[0])))



//   Data Model
//
/////////////////////////

union Word {
  struct {
    int low_order_bit:1;
    int upper_31_bits:31;
  };
  void* pointer;
};

struct App {
  union Word fun;
  union Word arg;
};

typedef struct App App;
typedef union Word Word;

_Static_assert(sizeof(void*) == 4, "32-bit pointers");
_Static_assert(sizeof(Word) == sizeof(void*), "Word is packed");
_Static_assert(sizeof(App) == 2*sizeof(Word), "App is packed");

// Allocate some addresses to use as constants.
// The contents don't matter.
// But the size must be at least 2 bytes, to ensure
// the low-order bit is 0, so these pointers don't look like tagged ints.
int consts[100];

int is_word_int(Word w) {
  return w.low_order_bit;
}
int is_word_const(Word w) {
  return !is_word_int(w)
    && w.pointer >= ((void*)consts)
    && w.pointer < ((void*)array_end(consts));
}
int is_word_app(Word w) {
  return !is_word_int(w) && !is_word_const(w);
}

Word make_int(int x) {
  Word w;
  w.low_order_bit = 1;
  w.upper_31_bits = x;
  assert(is_word_int(w));
  return w;
}
Word make_app(Word f, Word a) {
  Word w;

  // TODO slab allocator instead of malloc
  w.pointer = malloc(sizeof(App));
  w.pointer->f = f;
  w.pointer->a = a;
    
  assert(is_word_app(w));
  return w;
}

int as_int(Word w) {
  assert(is_word_int(w));
  return w.upper_31_bits;
}
App* as_app(Word w) {
  assert(is_word_app(w));
  return w.pointer;
}
int eq(Word x, Word y) {
  return x.pointer == y.pointer;
}

// Statically allocate the constants.
const Word S = { .pointer = &consts[0] };
const Word K = { .pointer = &consts[1] };
const Word I = { .pointer = &consts[2] };
const Word B = { .pointer = &consts[3] };
const Word C = { .pointer = &consts[4] };
const Word U = { .pointer = &consts[5] };
const Word P = { .pointer = &consts[6] };
const Word add = { .pointer = &consts[7] };


////////////////////
// 
//   Machine Model
// 
////////////////////

Word stack_buf[1024];
Word* stack = array_end(stack_buf);

void push(Word w) {
  // TODO these assertions are different: they depend on the input program
  assert(stack > stack_buf && "stack_buf overflow");
  stack--;
  stack[0] = w;
}
Word pop() {
  // This assertion is a true invariant: no user program should be able to trigger this.
  assert(stack < array_end(stack_buf));
  Word w = stack[0];
  stack++;
  return w;
}



int main() {

  printf("%x\n", (array_end(stack_buf) - stack));
  
  return 0;
}
