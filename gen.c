// Copyright 2012 Rui Ueyama. Released under the MIT license.
// This file has been almost completely rewritten in 2016 by Martijn Heil, to generate Lua code.

#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include "8cc.h"

bool dumpstack = false;
bool dumpsource = true;

static char *REGS[] = {"rdi", "rsi", "rdx", "rcx", "r8", "r9"};
static char *SREGS[] = {"dil", "sil", "dl", "cl", "r8b", "r9b"};
static char *MREGS[] = {"edi", "esi", "edx", "ecx", "r8d", "r9d"};
static int TAB = 8;
static Vector *functions = &EMPTY_VECTOR;
static int stackpos;
static int numgp;
static int numfp;
static FILE *outputfp;
static Map *source_files = &EMPTY_MAP;
static Map *source_lines = &EMPTY_MAP;
static char *last_loc = "";

static void emit_addr(Node *node);
static void emit_expr(Node *node);
static void emit_decl_init(Vector *inits, int off, int totalsize);
static void do_emit_data(Vector *inits, int size, int off, int depth);
static void emit_data(Node *v, int off, int depth);

#define REGAREA_SIZE 176

#define emit(...)        emitf(__LINE__, "\t" __VA_ARGS__)
#define emit_noindent(...)  emitf(__LINE__, __VA_ARGS__)

#ifdef __GNUC__
#define SAVE                                                            \
    int save_hook __attribute__((unused, cleanup(pop_function)));       \
    if (dumpstack)                                                      \
        vec_push(functions, (void *)__func__);

static void pop_function(void *ignore) {
    if (dumpstack)
        vec_pop(functions);
}
#else
#define SAVE
#endif

static char *get_caller_list() {
    Buffer *b = make_buffer();
    for (int i = 0; i < vec_len(functions); i++) {
        if (i > 0)
            buf_printf(b, " -> ");
        buf_printf(b, "%s", vec_get(functions, i));
    }
    buf_write(b, '\0');
    return buf_body(b);
}

void set_output_file(FILE *fp) {
    outputfp = fp;
}

void close_output_file() {
    fclose(outputfp);
}

static void emitf(int line, char *fmt, ...) {
    // Replace "#" with "%%" so that vfprintf prints out "#" as "%".
    char buf[256];
    int i = 0;
    for (char *p = fmt; *p; p++) {
        assert(i < sizeof(buf) - 3);
        if (*p == '#') {
            buf[i++] = '%';
            buf[i++] = '%';
        } else {
            buf[i++] = *p;
        }
    }
    buf[i] = '\0';

    va_list args;
    va_start(args, fmt);
    int col = vfprintf(outputfp, buf, args);
    va_end(args);

    if (dumpstack) {
        for (char *p = fmt; *p; p++)
            if (*p == '\t')
                col += TAB - 1;
        int space = (28 - col) > 0 ? (30 - col) : 2;
        fprintf(outputfp, "%*c %s:%d", space, '#', get_caller_list(), line);
    }
    fprintf(outputfp, "\n");
}

static void emit_nostack(char *fmt, ...) {
    fprintf(outputfp, "\t");
    va_list args;
    va_start(args, fmt);
    vfprintf(outputfp, fmt, args);
    va_end(args);
    fprintf(outputfp, "\n");
}


static char **split(char *buf) {
    char *p = buf;
    int len = 1;
    while (*p) {
        if (p[0] == '\r' && p[1] == '\n') {
            len++;
            p += 2;
            continue;
        }
        if (p[0] == '\r' || p[0] == '\n')
            len++;
        p++;
    }
    p = buf;
    char **r = malloc(sizeof(char *) * len + 1);
    int i = 0;
    while (*p) {
        if (p[0] == '\r' && p[1] == '\n') {
            p[0] = '\0';
            p += 2;
            r[i++] = p;
            continue;
        }
        if (p[0] == '\r' || p[0] == '\n') {
            p[0] = '\0';
            r[i++] = p + 1;
        }
        p++;
    }
    r[i] = NULL;
    return r;
}

static char **read_source_file(char *file) {
    FILE *fp = fopen(file, "r");
    if (!fp)
        return NULL;
    struct stat st;
    fstat(fileno(fp), &st);
    char *buf = malloc(st.st_size + 1);
    if (fread(buf, 1, st.st_size, fp) != st.st_size) {
        fclose(fp);
        return NULL;
    }
    fclose(fp);
    buf[st.st_size] = '\0';
    return split(buf);
}

static void maybe_print_source_line(char *file, int line) {
    if (!dumpsource)
        return;
    char **lines = map_get(source_lines, file);
    if (!lines) {
        lines = read_source_file(file);
        if (!lines)
            return;
        map_put(source_lines, file, lines);
    }
    int len = 0;
    for (char **p = lines; *p; p++)
        len++;
    emit_nostack("# %s", lines[line - 1]);
}

static void maybe_print_source_loc(Node *node) {
    if (!node->sourceLoc)
        return;
    char *file = node->sourceLoc->file;
    long fileno = (long)map_get(source_files, file);
    if (!fileno) {
        fileno = map_len(source_files) + 1;
        map_put(source_files, file, (void *)fileno);
        emit(".file %ld \"%s\"", fileno, quote_cstring(file));
    }
    char *loc = format(".loc %ld %d 0", fileno, node->sourceLoc->line);
    if (strcmp(loc, last_loc)) {
        emit("%s", loc);
        maybe_print_source_line(file, node->sourceLoc->line);
    }
    last_loc = loc;
}








static void emit_decl(Node *node) {
    if(node->declinit != NULL) {
        emit("%s = ", node->declvar->varname);

        for (int i = 0; i < vec_len(node->declinit); i++) {
            emit_expr(vec_get(node->declinit, i));

            if(i < vec_len(node->declinit)-1) emit(",");
        }
    }
}

static bool maybe_emit_builtin(Node *node) {
    return false;
}


static void emit_var(Node *node) {
    emit("%s", node->varname);
}

static void emit_deref(Node *node) {
    emit("__dereference(");
    emit_expr(node->operand);
    emit(")");
}

static void emit_literal(Node *v) {
    switch(v->kind) {
        case KIND_BOOL:     emit("%s", v->ival == 0 ? "false" : "true"); break;
        case KIND_CHAR:     emit("%i", v->ival); break;
        case KIND_SHORT:    emit("%i", v->ival); break;
        case KIND_INT:      emit("%i", v->ival); break;

        case KIND_LONG:     emit("%li", v->ival); break;
        case KIND_LLONG:    emit("%li", v->ival); break;

        case KIND_FLOAT:    emit("%f", v->fval); break;
        case KIND_DOUBLE:   emit("%f", v->fval); break;
        case KIND_LDOUBLE:  emit("%f", v->fval); break;

        case KIND_ARRAY:
            emit("{");
            for(int i = 0; i < (v->ty->size - 1); i++) {
                emit("%i", v->sval[i]);
            }
            emit("}");
        break;

        default:
            error("interal error");
    }
}

static void emit_func_call_args(Vector *args) {
    for (int i = 0; i < vec_len(args); i++) {
        emit_expr(vec_get(args, i));

        // Don't emit a comma after the last argument.
        if(i < vec_len(args)-1) emit(",");
    }
}

static void emit_func_call(Node *v) {
    bool isptr = (node->kind == AST_FUNCPTR_CALL);
    if(isptr) {
        emit_expr(node->fptr);
        emit("("); // TODO arguments
        emit_func_call_args(v->args);
        emit(")");
    } else {
        emit("%s(", node->fname); // TODO arguments
        emit_func_call_args(v->args);
        emit(")");
    }
}


static void emit_return(Node *node) {
    SAVE;
    emit("return");
    if(node->retval != NULL) {
        emit_expr(node->retval);
    }
}



static void emit_expr(Node *node) {
    SAVE;
    maybe_print_source_loc(node);
    switch (node->kind) {
    case AST_LITERAL:       emit_literal(node); return;
    case AST_LVAR:          emit_var(node); return;
    case AST_GVAR:          emit_var(node); return;
    case AST_FUNCDESG:      emit_addr(node); return;
    case AST_FUNCALL:
        if (maybe_emit_builtin(node)) { return; } // TODO
        // fall through

    case AST_FUNCPTR_CALL:  emit_func_call(node); return;
    case AST_DECL:          emit_decl(node); return;
    case AST_CONV:          emit_expr(node); return;
    case AST_ADDR:          emit_addr(node->operand); return;
    case AST_DEREF:         emit_deref(node); return;
    case AST_IF:
    case AST_TERNARY:
        emit_ternary(node);
        return;
    case AST_GOTO:          emit_goto(node); return;
    case AST_LABEL:
        if (node->newlabel)
            emit_label(node->newlabel);
        return;
    case AST_RETURN:  emit_return(node); return;
    case AST_COMPOUND_STMT: emit_compound_stmt(node); return;
    case AST_STRUCT_REF:
        emit_load_struct_ref(node->struc, node->ty, 0);
        return;
    case OP_PRE_INC:        emit_pre_inc_dec(node, "add"); return;
    case OP_PRE_DEC:        emit_pre_inc_dec(node, "sub"); return;
    case OP_POST_INC:       emit_post_inc_dec(node, "add"); return;
    case OP_POST_DEC:       emit_post_inc_dec(node, "sub"); return;
    case '!':               emit_lognot(node); return;
    case '&':               emit_bitand(node); return;
    case '|':               emit_bitor(node); return;
    case '~':               emit_bitnot(node); return;
    case OP_LOGAND:         emit_logand(node); return;
    case OP_LOGOR:          emit_logor(node); return;
    case OP_CAST:           emit_cast(node); return;
    case ',':               emit_comma(node); return;
    case '=':               emit_assign(node); return;
    case OP_LABEL_ADDR:     emit_label_addr(node); return;
    case AST_COMPUTED_GOTO: emit_computed_goto(node); return;
    default:
        emit_binop(node);
    }
}


void emit_toplevel(Node *v) {
    stackpos = 8;
    if (v->kind == AST_FUNC) {
        emit_expr(v->body);
    } else if (v->kind == AST_DECL) {
        emit_global_var(v);
    } else {
        error("internal error");
    }
}
