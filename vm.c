#include <stdlib.h>
#include <stdint.h>
#include <ctype.h>
#include <assert.h>
#include <stdio.h>
#include <unistd.h>
#include <string.h>


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
const Word constructor = { .pointer = &consts[5] };
const Word caser = { .pointer = &consts[6] };
const Word add = { .pointer = &consts[7] }; // TODO more generic foreign functions?

const char* const_name(Word w) {
    assert(is_word_const(w));
    if (eq(w, S)) return "S";
    if (eq(w, K)) return "K";
    if (eq(w, I)) return "I";
    if (eq(w, B)) return "B";
    if (eq(w, C)) return "C";
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
void fgetword(FILE* in, char* buf, char* end) {
    while ((end - buf) > 1 && isalpha(peek(in)))
	*buf++ = fgetc(in);
    *buf++ = '\0';
    assert(buf <= end);
}
Word parse_symbol(FILE* in) {
    static char buf[1024];
    fgetword(in, buf, array_end(buf));
    
    if (0 == strcmp(buf, "S")) return S;
    if (0 == strcmp(buf, "S")) return S;
    if (0 == strcmp(buf, "K")) return K;
    if (0 == strcmp(buf, "I")) return I;
    if (0 == strcmp(buf, "B")) return B;
    if (0 == strcmp(buf, "C")) return C;
    if (0 == strcmp(buf, "add")) return add;
    
    assert(0 && "unrecognized symbol");
    return make_int(666);
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
	fprintf(out, ")");
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

void dump_stack(FILE* out, int nargs) {
    fprintf(out, "%d", nargs);
    for (Word* p=stack; p<array_end(stack_buf); ++p) {
	fprintf(out, "\t");
	print_factor(out, *p);
    }
    fprintf(out, "\n");
}

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
Word pop_arg() {
    Word w = pop();
    return as_app(w)->arg;
}
void update(Word app, Word f, Word a) {
    as_app(app)->fun = f;
    as_app(app)->arg = a;
}

// Core interpreter loop:
//  - inspects the top element of the stack
//  - if it's an application, pushes into it
//  - if it's a constant with enough args, apply a reduction rule
//  - if it's a curried thing or prim value, pop until nargs==0
// TODO introduce something for erroneous programs (as opposed to VM bugs)
//    - what's the semantics of an error? (probably the Haskell thing)
//    - how to express this to the caller of run?
void r(int nargs) {

    for (;;) {
	//dump_stack(stderr, nargs);
	
	if (is_word_app(stack[0])) {
	    push(as_app(stack[0])->fun);
	    nargs += 1;
	    continue;
	} else if (eq(stack[0], S) && nargs >= 3) {
	    pop();
	    Word f = pop_arg();
	    Word g = pop_arg();
	    Word x = as_app(stack[0])->arg;
	    update(stack[0], make_app(f, x), make_app(g, x));
	    nargs -= 3;
	    continue;
	} else if (eq(stack[0], K) && nargs >= 2) {
	    pop();
	    Word x = pop_arg();
	    Word y = as_app(stack[0])->arg;
	    update(stack[0], I, x);
	    nargs -= 2;
	    continue;
	} else if (eq(stack[0], I) && nargs >= 1) {
	    pop();
	    Word x = pop_arg();
	    push(x);
	    nargs -= 1;
	    continue;
	} else if (eq(stack[0], B) && nargs >= 3) {
	    pop();
	    Word f = pop_arg();
	    Word g = pop_arg();
	    Word x = as_app(stack[0])->arg;
	    update(stack[0], f, make_app(g, x));
	    nargs -= 3;
	    continue;
	} else if (eq(stack[0], C) && nargs >= 3) {
	    pop();
	    Word f = pop_arg();
	    Word x = pop_arg();
	    Word y = as_app(stack[0])->arg;
	    update(stack[0], make_app(f, y), x);
	    nargs -= 3;
	    continue;
	} else if (eq(stack[0], add) && nargs >= 2) {
	    Word x = as_app(stack[1])->arg;
	    Word y = as_app(stack[2])->arg;

	    // eval x, and leave it on the stack to root it.
	    push(x);
	    r(0);

	    // eval y
	    push(y);
	    r(0);
	    
	    y = pop();
	    x = pop();

	    assert(is_word_int(x));
	    assert(is_word_int(y));
	    Word sum = make_int(as_int(x) + as_int(y));

	    // now the stack still has add, (add x), ((add x) y) on it.
	    pop();
	    pop();
	    update(stack[0], I, sum);

	    nargs -= 2;
	    continue;
	} else if (0) {
	    // TODO cases for U and P
	} else if (is_word_const(stack[0])) {
	    // any constant we haven't handled must be partially-applied
	    while (nargs --> 0)
		pop();
	    return;
	} else if (is_word_int(stack[0]) && nargs == 0) {
	    while (nargs --> 0)
		pop();
	    return;
	} else if (is_word_int(stack[0]) && nargs > 0) {
	    assert(0 && "number is not a function");
	}

	assert(0 && "no case in main loop");
	return;
    }
    assert(0 && "fell out of main loop");
    return;
}

// Takes a term graph as input.
// Reduces it in place to a value (or to make_app(I, value)).
// Also, returns the value (without the I wrapper).
Word run(Word w) {
    push(w);
    r(0);
    return pop();
}




int main() {

    Word w = parse_expr(stdin);
    //print_expr(stdout, w);
    //printf("\n");

    w = run(w);
    print_expr(stdout, w);
    printf("\n");
  
    return 0;
}
