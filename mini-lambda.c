#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include <stdio.h>

// (L)anguage

enum Lcon { Var, App, Lam };

struct L {
  enum Lcon tag;
  union {
    char* var;
    struct { struct L* fun; int n_args; struct L* args[]; };
    struct { struct L* bdy; int n_pars; char* pars[]; };
  };
};

static inline struct L* var(char* var) {
  struct L* res = malloc(sizeof(struct L));
  res->tag = Var;
  res->var = var;
  return res;
}

static inline struct L* app(struct L* fun, int n_args, struct L* args[]) {
  struct L* res = malloc(sizeof(struct L) + sizeof(struct L*) * n_args);
  res->tag = App;
  res->fun = fun;
  res->n_args = n_args;
  for (int i = 0; i < n_args; i++) {
    res->args[i] = args[i];
  }
  return res;
}

static inline struct L* app1(struct L* fun, struct L* arg) {
  struct L* res = malloc(sizeof(struct L) + sizeof(struct L*));
  res->tag = App;
  res->fun = fun;
  res->n_args = 1;
  res->args[0] = arg;
  return res;
}

static inline struct L* app2(struct L* fun, struct L* arg1, struct L* arg2) {
  struct L* res = malloc(sizeof(struct L) + sizeof(struct L*) * 2);
  res->tag = App;
  res->fun = fun;
  res->n_args = 2;
  res->args[0] = arg1;
  res->args[1] = arg2;
  return res;
}

static inline struct L* app3(struct L* fun, struct L* arg1, struct L* arg2, struct L* arg3) {
  struct L* res = malloc(sizeof(struct L) + sizeof(struct L*) * 3);
  res->tag = App;
  res->fun = fun;
  res->n_args = 3;
  res->args[0] = arg1;
  res->args[1] = arg2;
  res->args[2] = arg3;
  return res;
}


static inline struct L* lam(int n_pars, char* pars[], struct L* bdy) {
  struct L* res = malloc(sizeof(struct L) + sizeof(char*) * n_pars);
  res->tag = Lam;
  res->bdy = bdy;
  res->n_pars = n_pars;
  for (int i = 0; i < n_pars; i++) {
    res->pars[i] = pars[i];
  }
  return res;
}

static inline struct L* lam1(char* par, struct L* bdy) {
  struct L* res = malloc(sizeof(struct L) + sizeof(char*) * 1);
  res->tag = Lam;
  res->bdy = bdy;
  res->n_pars = 1;
  res->pars[0] = par;
  return res;
}

static inline struct L* lam2(char* par1, char* par2, struct L* bdy) {
  struct L* res = malloc(sizeof(struct L) + sizeof(char*) * 2);
  res->tag = Lam;
  res->bdy = bdy;
  res->n_pars = 2;
  res->pars[0] = par1;
  res->pars[1] = par2;
  return res;
}

static inline struct L* lam3(char* par1, char* par2, char* par3, struct L* bdy) {
  struct L* res = malloc(sizeof(struct L) + sizeof(char*) * 2);
  res->tag = Lam;
  res->bdy = bdy;
  res->n_pars = 3;
  res->pars[0] = par1;
  res->pars[1] = par2;
  res->pars[2] = par3;
  return res;
}

// (E)nvironment

struct E {
  int refcount;
  char* var;
  void* val;
  struct E* rest;
};


static inline void deref_E(struct E* x) {
  x->refcount--;
  if (x->refcount == 0) {
    // free(x);
  }
}

static inline struct E* ref_E(struct E* x) {
  x->refcount++;
  return x;
}

static inline struct E* insert(struct E* env, char* var, void* val) {
  struct E* env2 = malloc(sizeof(struct E));
  env2->refcount = 1;
  env2->var = var;
  env2->val = val;
  env2->rest = env;
  return env2;
}

static inline void* lookup(struct E* env, char* var) {
  while (strcmp(env->var, var) != 0) {
    env = env->rest;
  }
  return env->val;
}

// (V)alues

enum Vcon { Closure, Succ, Num };

struct V {
  int refcount;
  enum Vcon tag;
  union {
    struct {
      struct E* env;
      struct L* bdy;
      char* pars[];
    };
    int num;
  };
};

static inline void deref_V(struct V* x) {
  x->refcount--;
  if (x->refcount == 0) {
    // free(x);
  }
}

static inline struct V* ref_V(struct V* x) {
  x->refcount++;
  return x;
}

// Interpreter

struct V* whnf(struct E* env, struct L* x) {
  for(;;) {
    switch(x->tag) {
      case Var:
        return lookup(env, x->var);
      case App:
        struct V* fun_val = whnf(env, x->fun);
        deref_E(env);
        switch(fun_val->tag){
          case Closure:
            env = fun_val->env;
            for (int i = 0; i < x->n_args; i++) {
              env = insert(env, fun_val->pars[i], whnf(ref_E(env), x->args[i]));
            }
            x = fun_val->bdy;
            deref_V(fun_val);
            break;
          case Succ:
            deref_V(fun_val);
            struct V* n = whnf(ref_E(env), x->args[0]);
            n->num += 1;
            return n;
          default:
            __builtin_unreachable();
        }
        break;
      case Lam:
        struct V* res = malloc(sizeof(struct V) + sizeof(char*) * x->n_pars);
        res->refcount = 1;
        res->env = env;
        res->bdy = x->bdy;
        memcpy(&res->pars, &x->pars, sizeof(char*) * x->n_pars);
        return res;
      default:
        __builtin_unreachable();
    }
  }
}

// TODO Recursive descent parser

// Self application
struct L* w(char* name) {
  return app1(var(name), var(name));
}

struct L* let(char* var, struct L* rhs, struct L* k) {
  return app1(lam1(var, k), rhs);
}

struct L* from_int(int n) {
  struct L* res = lam2("z", "s", var("z"));
  for (; n > 0; n--) {
    res = lam2("z", "s", app1(var("s"),res));
  }
  return res;
}

int main() {

  // add
  // add: n m: n(m, k: add(add, k, n))
  struct L* add =
    lam1("add", lam2("n", "m",
      app2(var("n"),
        var("m"),
        lam1("k",
          app2(w("add"),var("k"),var("n"))
          ))));

  // fib
  // fib: n: n(n, m: m(n, k: add(add, fib(fib, m), fib(fib, k))))
  struct L* fib =
    lam1("fib", lam1("n",
      app2(var("n"),
        var("n"),
        lam1("m",
          app2(var("m"),
            var("n"),
            lam1("k",
              app2(w("add"),
                app1(w("fib"), var("m")),
                app1(w("fib"), var("k"))
                )))))));

  // seven
  // z s: s(z s: s(z s: s(z s: s(z s: s(z s: s(z s: s(z s: z)))))))
  struct L* seven = from_int(7);

  // fib(7)    (= 13)
  struct L* prog =
    let("add", add,
    let("fib", fib,
    app2(app1(w("fib"), seven), var("zero"), var("succ"))
    ));

  struct V* v_zero = malloc(sizeof(struct V));
  v_zero->refcount = 1;
  v_zero->tag = Num;
  v_zero->num = 0;

  struct V* v_succ = malloc(sizeof(struct V));
  v_succ->refcount = 1;
  v_succ->tag = Succ;

  struct E* env = malloc(sizeof(struct E));
  env->refcount = 1;
  env->var = "zero";
  env->val = v_zero;
  env->rest = NULL;

  struct E* env2 = malloc(sizeof(struct E));
  env2->refcount = 1;
  env2->var = "succ";
  env2->val = v_succ;
  env2->rest = env;

  // TODO: Need to do a fold over the integer instead of applying them like they're church numerals
  struct V* res = whnf(env2, app2(from_int(7), var("zero"), var("succ")));
  printf("%d\n", res->num);
}
