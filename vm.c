#include <stdlib.h>
#include <stdint.h>
#include <ctype.h>
#include <assert.h>
#include <stdio.h>


#define array_end(arr) (arr + (sizeof(arr)/sizeof(arr[0])))


/******  Data Model  ********************************************************/

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
    // TODO slab allocator instead of malloc
    App* app = malloc(sizeof(App));
    app->fun = f;
    app->arg = a;
    
    Word w;
    w.pointer = app;
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

const char* const_name(Word w) {
    assert(is_word_const(w));
    if (eq(w, S)) return "S";
    if (eq(w, K)) return "K";
    if (eq(w, I)) return "I";
    if (eq(w, B)) return "B";
    if (eq(w, C)) return "C";
    if (eq(w, U)) return "U";
    if (eq(w, P)) return "P";
    if (eq(w, add)) return "add";
    return "#<unknown>";
}
    


/******  Parsing and printing  **********************************************/


/*

  expr :=
  | integer
  | constant: S, K, I, B, C, U, add
  | expr expr   left-assoc
  | ( expr )


  expr :=
  | factor factor ...

  expr :=
  | expr factor
  | factor

  factor :=
  | integer
  | constant
  | ( expr )
  

*/
int peek(FILE* in) {
    int c = fgetc(in);
    if (c != EOF)
	ungetc(c, in);
    return c;
}
void eat_whitespace(FILE* in) {
    while (isspace(peek(in)))
	fgetc(in);
}
Word parse_integer(FILE* in) {
    int n = 0;
    while (isdigit(peek(in))) {
	int c = fgetc(in);
	int digit = c - '0';
	n = n*10 + digit;
    }
    return make_int(n);
}
Word parse_symbol(FILE* in) {
    int c = fgetc(in);
    switch (c) {
    case 'S': return S;
    case 'K': return K;
    case 'I': return I;
    case 'B': return B;
    case 'C': return C;
    case 'U': return U;
    case 'P': return P;
    case 'a':
	c = fgetc(in);
	assert(c == 'd');
	c = fgetc(in);
	assert(c == 'd');
	return add;
    default:
	assert(0 && "unrecognized symbol");
	return make_int(666);
    }
}


Word parse_expr(FILE* in);
Word parse_factor(FILE* in) {
    eat_whitespace(in);
    int c = peek(in);
    if (isdigit(c)) {
	return parse_integer(in);
    } else if (isalpha(c)) {
	return parse_symbol(in);
    } else if (c == '(') {
	fgetc(in);
	Word w = parse_expr(in);
	c = peek(in);
	assert(c == ')');
	fgetc(in);
	return w;
    } else {
	assert(0 && "can't parse a factor here");
	return make_int(666);
    }
}
Word parse_expr(FILE* in) {
    Word x = parse_factor(in);
    for (;;) {
	eat_whitespace(in);
	int c = peek(in);
	if (isdigit(c) || isalpha(c) || c == '(') {
	    Word y = parse_factor(in);
	    x = make_app(x, y);
	    continue;
	} else {
	    return x;
	}
    }
}

void print_expr(FILE* out, Word w);
void print_factor(FILE* out, Word w) {
    if (is_word_int(w)) {
	fprintf(out, "%d", as_int(w));
    } else if (is_word_const(w)) {
	fprintf(out, "%s", const_name(w));
    } else if (is_word_app(w)) {
	fprintf(out, "(");
	print_expr(out, w);
    } else {
	assert(0 && "bad word type");
    }
}
void print_expr(FILE* out, Word w) {
    if (is_word_app(w)) {
	Word f = as_app(w)->fun;
	Word a = as_app(w)->arg;
	print_expr(out, f);
	fprintf(out, " ");
	print_factor(out, a);
    } else {
	print_factor(out, w);
    }
}



/******  Machine Model  *****************************************************/

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

    Word w = parse_expr(stdin);
    print_expr(stdout, w);
    printf("\n");
  
    return 0;
}
