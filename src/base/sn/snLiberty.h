/**CFile****************************************************************

  FileName    [snLiberty.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Stand-alone Liberty (.lib) syntax parser and Boolean function-expression parser.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snLiberty.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef SN_LIBERTY_H
#define SN_LIBERTY_H

// This header reads a Liberty library into a syntax tree and parses the
// Boolean expressions used by its function, three_state, next_state,
// clocked_on, clear, preset, and enable attributes. It depends only on the C
// standard library, so the same code serves ABC and the external frontend.
//
// The syntax layer is deliberately generic: it records every group,
// simple attribute, and complex attribute as an item with its text spans and
// leaves the interpretation of keys and values to the caller. Rules taken from
// the Liberty Reference Manual (Synopsys, R-2020.09) are cited where the
// code encodes them; where real libraries deviate from the manual (for
// example, C++-style comments), the parser follows the libraries.
//
// Memory is one contiguous copy of the file text plus one item array; spans
// index the text, so parsing a library allocates little beyond its own size.
// Sibling items are parsed iteratively; recursion depth equals group nesting
// depth, which is small in practice.

#include <ctype.h>
#include <math.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "misc/util/abc_namespaces.h"

ABC_NAMESPACE_HEADER_START

#define SN_LIBERTY_INVALID UINT32_MAX

// A half-open byte range [begin, end) in the library text.
typedef struct sn_liberty_span_t
{
    uint32_t begin;
    uint32_t end;
} sn_liberty_span_t;

// The three statement forms of the language (manual, "General Syntax"):
//   group:             key ( head ) { statements }
//   simple attribute:  key : value ;
//   complex attribute: key ( arg, arg, ... ) ;
typedef enum sn_liberty_kind_t
{
    SN_LIBERTY_GROUP = 0,
    SN_LIBERTY_ATTRIBUTE,
    SN_LIBERTY_COMPLEX
} sn_liberty_kind_t;

typedef struct sn_liberty_item_t
{
    uint32_t kind; // sn_liberty_kind_t
    uint32_t line; // 1-based line of the key
    sn_liberty_span_t key;
    // The group head or complex-attribute argument text between the
    // parentheses, or the simple-attribute value after the colon. Quotes and
    // line continuations are kept; the text accessors strip them.
    sn_liberty_span_t value;
    uint32_t child; // first child of a group, else SN_LIBERTY_INVALID
    uint32_t next;  // next sibling, else SN_LIBERTY_INVALID
} sn_liberty_item_t;

#define SN_LIBERTY_SCRATCH_COUNT 4

typedef struct sn_liberty_t
{
    char* path;      // file name used in messages
    char* text;      // library text with comments blanked; NUL-terminated
    size_t size;     // length of text
    sn_liberty_item_t* items;
    uint32_t count;
    uint32_t cap;
    uint32_t root; // synthetic group whose children are the top-level statements
    char* error;   // NULL when parsing succeeded
    bool failed;   // set when a failure could not even allocate its message
    uint32_t line; // parser position, in lines
    uint64_t source_hash; // hash of the text as given, before comments were blanked
    // Rotating NUL-terminated copies handed out by the text accessors, so up
    // to SN_LIBERTY_SCRATCH_COUNT results stay valid at once (enough for one
    // message with several operands).
    char* scratch[SN_LIBERTY_SCRATCH_COUNT];
    size_t scratch_cap[SN_LIBERTY_SCRATCH_COUNT];
    uint32_t scratch_next;
} sn_liberty_t;

// ---------------------------------------------------------------------------
// Errors

// A fast non-cryptographic hash over a byte range, eight bytes at a time; used
// to tie a binary model to the library text it was built from.
static inline uint64_t sn_liberty_hash_bytes(const void* data, size_t size)
{
    const uint8_t* bytes = (const uint8_t*)data;
    uint64_t hash = UINT64_C(0x9E3779B97F4A7C15) ^ (uint64_t)size;
    size_t i = 0;
    for (; i + 8 <= size; i += 8)
    {
        uint64_t word;
        memcpy(&word, bytes + i, 8);
        hash ^= word;
        hash *= UINT64_C(0xff51afd7ed558ccd);
        hash ^= hash >> 32;
    }
    for (; i < size; i++)
    {
        hash ^= bytes[i];
        hash *= UINT64_C(0x100000001b3);
    }
    return hash;
}

static inline void sn_liberty_set_error(sn_liberty_t* lib, uint32_t line, const char* format, ...)
{
    if (lib->error || lib->failed)
        return;
    char message[512];
    va_list args;
    va_start(args, format);
    vsnprintf(message, sizeof(message), format, args);
    va_end(args);
    const char* path = lib->path ? lib->path : "?";
    size_t length = strlen(path) + strlen(message) + 64;
    lib->error = (char*)malloc(length);
    if (lib->error)
        snprintf(lib->error, length, "%s:%u: %s", path, line, message);
    else
        lib->failed = true; // no message, but sn_liberty_ok() still reports the failure
}

// ---------------------------------------------------------------------------
// Construction and destruction

static inline void sn_liberty_destroy(sn_liberty_t* lib)
{
    if (!lib)
        return;
    free(lib->path);
    free(lib->text);
    free(lib->items);
    free(lib->error);
    for (uint32_t i = 0; i < SN_LIBERTY_SCRATCH_COUNT; i++)
        free(lib->scratch[i]);
    free(lib);
}

static inline uint32_t sn_liberty_new_item(sn_liberty_t* lib, sn_liberty_kind_t kind, uint32_t line)
{
    if (lib->count == lib->cap)
    {
        uint32_t cap = lib->cap ? lib->cap * 2 : 1024;
        sn_liberty_item_t* items = (sn_liberty_item_t*)realloc(lib->items, (size_t)cap * sizeof(sn_liberty_item_t));
        if (!items)
        {
            sn_liberty_set_error(lib, line, "out of memory");
            return SN_LIBERTY_INVALID;
        }
        lib->items = items;
        lib->cap = cap;
    }
    sn_liberty_item_t* item = &lib->items[lib->count];
    memset(item, 0, sizeof(*item));
    item->kind = (uint32_t)kind;
    item->line = line;
    item->child = SN_LIBERTY_INVALID;
    item->next = SN_LIBERTY_INVALID;
    return lib->count++;
}

// Blanks comments with spaces, keeping newlines so line numbers survive.
// Block comments follow the manual; line comments ("//") appear in vendor
// libraries and are accepted too. Neither is recognized inside a string.
// Blanks comments with spaces, keeping newlines so line numbers survive.
// Block comments follow the manual; line comments ("//") appear in vendor
// libraries and are accepted too. Neither is recognized inside a string.
// Returns the offset of an unterminated block comment, or size when every
// comment is closed.
static inline size_t sn_liberty_blank_comments(char* text, size_t size)
{
    size_t i = 0;
    while (i + 1 < size)
    {
        if (text[i] == '"')
        {
            for (i++; i < size && text[i] != '"'; i++)
                if (text[i] == '\\' && i + 1 < size)
                    i++;
            i++;
        }
        else if (text[i] == '/' && text[i + 1] == '*')
        {
            size_t begin = i;
            size_t j = i + 2;
            while (j + 1 < size && !(text[j] == '*' && text[j + 1] == '/'))
                j++;
            if (j + 1 >= size)
                return begin;
            for (; i < j + 2; i++)
                if (text[i] != '\n')
                    text[i] = ' ';
        }
        else if (text[i] == '/' && text[i + 1] == '/')
        {
            for (; i < size && text[i] != '\n'; i++)
                text[i] = ' ';
        }
        else
            i++;
    }
    return size;
}

// ---------------------------------------------------------------------------
// Lexical helpers over the text

// A backslash continues the statement on the next line (manual, "General
// Syntax"); it is treated as white space wherever it appears outside a string.
static inline bool sn_liberty_is_space(char c)
{
    return c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == '\\' || c == '\f' || c == '\v';
}

static inline bool sn_liberty_is_delimiter(char c)
{
    return c == 0 || sn_liberty_is_space(c) || c == ':' || c == ';' || c == '(' || c == ')' || c == '{' ||
           c == '}' || c == '"' || c == ',';
}

// Advances over white space, counting lines.
static inline size_t sn_liberty_skip_space(sn_liberty_t* lib, size_t pos, size_t end)
{
    while (pos < end && sn_liberty_is_space(lib->text[pos]))
    {
        if (lib->text[pos] == '\n')
            lib->line++;
        pos++;
    }
    return pos;
}

// Advances past a quoted string starting at pos (which holds the opening
// quote), honoring backslash escapes and counting lines.
static inline size_t sn_liberty_skip_string(sn_liberty_t* lib, size_t pos, size_t end)
{
    for (pos++; pos < end; pos++)
    {
        char c = lib->text[pos];
        if (c == '\\' && pos + 1 < end)
        {
            if (lib->text[pos + 1] == '\n')
                lib->line++;
            pos++;
        }
        else if (c == '\n')
            lib->line++;
        else if (c == '"')
            return pos + 1;
    }
    return pos;
}

// Finds the parenthesis or brace matching the one at pos, ignoring nested
// pairs inside strings. Returns end when unmatched.
static inline size_t sn_liberty_find_match(sn_liberty_t* lib, size_t pos, size_t end)
{
    char open = lib->text[pos];
    char close = open == '(' ? ')' : '}';
    uint32_t depth = 0;
    while (pos < end)
    {
        char c = lib->text[pos];
        if (c == '"')
        {
            pos = sn_liberty_skip_string(lib, pos, end);
            continue;
        }
        if (c == '\n')
            lib->line++;
        else if (c == open)
            depth++;
        else if (c == close && --depth == 0)
            return pos;
        pos++;
    }
    return end;
}

static inline sn_liberty_span_t sn_liberty_trim(const sn_liberty_t* lib, size_t begin, size_t end)
{
    while (begin < end && sn_liberty_is_space(lib->text[begin]))
        begin++;
    while (end > begin && sn_liberty_is_space(lib->text[end - 1]))
        end--;
    sn_liberty_span_t span;
    span.begin = (uint32_t)begin;
    span.end = (uint32_t)end;
    return span;
}

// ---------------------------------------------------------------------------
// Parser

// Parses the statements in [pos, end) as children of parent. Siblings are
// linked in file order; groups recurse into their bodies.
static inline bool sn_liberty_parse_body(sn_liberty_t* lib, uint32_t parent, size_t pos, size_t end)
{
    uint32_t last = SN_LIBERTY_INVALID;
    for (;;)
    {
        pos = sn_liberty_skip_space(lib, pos, end);
        if (pos >= end)
            return true;
        char c = lib->text[pos];
        if (c == ';')
        {
            pos++; // stray statement terminator
            continue;
        }
        uint32_t line = lib->line;
        size_t key_begin = pos;
        if (c == '"')
            pos = sn_liberty_skip_string(lib, pos, end);
        else
            while (pos < end && !sn_liberty_is_delimiter(lib->text[pos]))
                pos++;
        if (pos == key_begin)
        {
            sn_liberty_set_error(lib, line, "unexpected character '%c'", c);
            return false;
        }
        size_t key_end = pos;
        pos = sn_liberty_skip_space(lib, pos, end);
        uint32_t item;
        if (pos < end && lib->text[pos] == ':')
        {
            // Simple attribute: the value runs to the terminating semicolon
            // or, when the semicolon is missing, to the end of the line.
            pos = sn_liberty_skip_space(lib, pos + 1, end);
            size_t value_begin = pos;
            while (pos < end)
            {
                char v = lib->text[pos];
                if (v == '"')
                {
                    pos = sn_liberty_skip_string(lib, pos, end);
                    continue;
                }
                if (v == ';' || v == '\n' || v == '}')
                    break;
                if (v == '\\' && pos + 1 < end && lib->text[pos + 1] == '\n')
                {
                    lib->line++;
                    pos += 2;
                    continue;
                }
                pos++;
            }
            item = sn_liberty_new_item(lib, SN_LIBERTY_ATTRIBUTE, line);
            if (item == SN_LIBERTY_INVALID)
                return false;
            lib->items[item].value = sn_liberty_trim(lib, value_begin, pos);
            if (pos < end && lib->text[pos] == ';')
                pos++;
        }
        else if (pos < end && lib->text[pos] == '(')
        {
            size_t close = sn_liberty_find_match(lib, pos, end);
            if (close >= end)
            {
                sn_liberty_set_error(lib, line, "unmatched '(' in \"%.*s\"", (int)(key_end - key_begin),
                                     lib->text + key_begin);
                return false;
            }
            sn_liberty_span_t head = sn_liberty_trim(lib, pos + 1, close);
            pos = sn_liberty_skip_space(lib, close + 1, end);
            if (pos < end && lib->text[pos] == '{')
            {
                // The match search counts the body's lines; the recursive parse
                // counts them again from the brace, so save and restore.
                uint32_t line_at_brace = lib->line;
                size_t body_close = sn_liberty_find_match(lib, pos, end);
                if (body_close >= end)
                {
                    sn_liberty_set_error(lib, line, "unmatched '{' in group \"%.*s\"", (int)(key_end - key_begin),
                                         lib->text + key_begin);
                    return false;
                }
                item = sn_liberty_new_item(lib, SN_LIBERTY_GROUP, line);
                if (item == SN_LIBERTY_INVALID)
                    return false;
                lib->items[item].value = head;
                uint32_t line_after_body = lib->line;
                lib->line = line_at_brace;
                if (!sn_liberty_parse_body(lib, item, pos + 1, body_close))
                    return false;
                lib->line = line_after_body;
                pos = body_close + 1;
            }
            else
            {
                item = sn_liberty_new_item(lib, SN_LIBERTY_COMPLEX, line);
                if (item == SN_LIBERTY_INVALID)
                    return false;
                lib->items[item].value = head;
                if (pos < end && lib->text[pos] == ';')
                    pos++;
            }
        }
        else
        {
            sn_liberty_set_error(lib, line, "expected ':' or '(' after \"%.*s\"", (int)(key_end - key_begin),
                                 lib->text + key_begin);
            return false;
        }
        lib->items[item].key.begin = (uint32_t)key_begin;
        lib->items[item].key.end = (uint32_t)key_end;
        if (last == SN_LIBERTY_INVALID)
            lib->items[parent].child = item;
        else
            lib->items[last].next = item;
        last = item;
    }
}

// Parses a library held in memory. The text is copied. Returns NULL only
// when the object itself cannot be allocated; every other failure, including
// later allocation failures, is reported through sn_liberty_ok() and ->error.
static inline sn_liberty_t* sn_liberty_parse_text(const char* name, const char* text, size_t size)
{
    sn_liberty_t* lib = (sn_liberty_t*)calloc(1, sizeof(sn_liberty_t));
    if (!lib)
        return NULL;
    lib->path = (char*)malloc(strlen(name) + 1);
    if (lib->path)
        strcpy(lib->path, name);
    lib->text = (char*)malloc(size + 1);
    if (!lib->path || !lib->text)
    {
        sn_liberty_set_error(lib, 0, "out of memory");
        return lib;
    }
    strcpy(lib->path, name);
    memcpy(lib->text, text, size);
    lib->text[size] = 0;
    lib->size = size;
    lib->source_hash = sn_liberty_hash_bytes(text, size);
    if (size > UINT32_MAX - 1)
    {
        sn_liberty_set_error(lib, 0, "file larger than 4 GB");
        return lib;
    }
    size_t open_comment = sn_liberty_blank_comments(lib->text, size);
    if (open_comment < size)
    {
        uint32_t line = 1;
        for (size_t i = 0; i < open_comment; i++)
            line += lib->text[i] == '\n';
        sn_liberty_set_error(lib, line, "unterminated block comment");
        return lib;
    }
    lib->line = 1;
    lib->root = sn_liberty_new_item(lib, SN_LIBERTY_GROUP, 0);
    if (lib->root != SN_LIBERTY_INVALID)
        sn_liberty_parse_body(lib, lib->root, 0, size);
    return lib;
}

static inline sn_liberty_t* sn_liberty_read_file(const char* path)
{
    FILE* in = fopen(path, "rb");
    if (!in)
    {
        sn_liberty_t* lib = sn_liberty_parse_text(path, "", 0);
        if (lib)
        {
            free(lib->error);
            lib->error = NULL;
            sn_liberty_set_error(lib, 0, "cannot open file");
        }
        return lib;
    }
    size_t cap = 1u << 20, size = 0;
    char* text = (char*)malloc(cap);
    while (text)
    {
        size += fread(text + size, 1, cap - size, in);
        if (size < cap)
            break;
        cap *= 2;
        char* grown = (char*)realloc(text, cap);
        if (!grown)
            free(text);
        text = grown;
    }
    bool read_error = ferror(in) != 0;
    fclose(in);
    if (!text)
        return NULL;
    sn_liberty_t* lib = read_error ? sn_liberty_parse_text(path, "", 0) : sn_liberty_parse_text(path, text, size);
    free(text);
    if (lib && read_error)
    {
        free(lib->error);
        lib->error = NULL;
        sn_liberty_set_error(lib, 0, "read error");
    }
    return lib;
}

static inline bool sn_liberty_ok(const sn_liberty_t* lib)
{
    return lib && !lib->error && !lib->failed;
}

// ---------------------------------------------------------------------------
// Navigation

static inline const sn_liberty_item_t* sn_liberty_item(const sn_liberty_t* lib, uint32_t id)
{
    return id < lib->count ? &lib->items[id] : NULL;
}

static inline uint32_t sn_liberty_root(const sn_liberty_t* lib)
{
    return lib->root;
}

static inline uint32_t sn_liberty_first_child(const sn_liberty_t* lib, uint32_t id)
{
    return id < lib->count ? lib->items[id].child : SN_LIBERTY_INVALID;
}

static inline uint32_t sn_liberty_next(const sn_liberty_t* lib, uint32_t id)
{
    return id < lib->count ? lib->items[id].next : SN_LIBERTY_INVALID;
}

static inline sn_liberty_kind_t sn_liberty_kind(const sn_liberty_t* lib, uint32_t id)
{
    return (sn_liberty_kind_t)lib->items[id].kind;
}

static inline uint32_t sn_liberty_line(const sn_liberty_t* lib, uint32_t id)
{
    return lib->items[id].line;
}

static inline bool sn_liberty_span_is(const sn_liberty_t* lib, sn_liberty_span_t span, const char* text)
{
    size_t length = strlen(text);
    return span.end - span.begin == length && memcmp(lib->text + span.begin, text, length) == 0;
}

// True when the item's key equals the given name.
static inline bool sn_liberty_key_is(const sn_liberty_t* lib, uint32_t id, const char* key)
{
    return id < lib->count && sn_liberty_span_is(lib, lib->items[id].key, key);
}

// The first child of parent with the given key after the item `after`
// (SN_LIBERTY_INVALID to start from the first child).
static inline uint32_t sn_liberty_find(const sn_liberty_t* lib, uint32_t parent, const char* key, uint32_t after)
{
    uint32_t id = after == SN_LIBERTY_INVALID ? sn_liberty_first_child(lib, parent) : sn_liberty_next(lib, after);
    for (; id != SN_LIBERTY_INVALID; id = lib->items[id].next)
        if (sn_liberty_span_is(lib, lib->items[id].key, key))
            return id;
    return SN_LIBERTY_INVALID;
}

static inline uint32_t sn_liberty_count(const sn_liberty_t* lib, uint32_t parent, const char* key)
{
    uint32_t count = 0;
    for (uint32_t id = sn_liberty_find(lib, parent, key, SN_LIBERTY_INVALID); id != SN_LIBERTY_INVALID;
         id = sn_liberty_find(lib, parent, key, id))
        count++;
    return count;
}

#define sn_liberty_for_each_child(lib, parent, id) \
    for (uint32_t id = sn_liberty_first_child((lib), (parent)); id != SN_LIBERTY_INVALID; id = sn_liberty_next((lib), id))

#define sn_liberty_for_each_named(lib, parent, key, id)                                               \
    for (uint32_t id = sn_liberty_find((lib), (parent), (key), SN_LIBERTY_INVALID); id != SN_LIBERTY_INVALID; \
         id = sn_liberty_find((lib), (parent), (key), id))

// ---------------------------------------------------------------------------
// Text extraction

// Copies a span into buffer as a NUL-terminated string, removing line
// continuations, outer quotes, and backslash escapes inside quotes. Returns
// the length the full text needs (excluding the NUL), like snprintf.
static inline size_t sn_liberty_span_copy(const sn_liberty_t* lib, sn_liberty_span_t span, char* buffer,
                                          size_t cap)
{
    size_t length = 0;
    bool quoted = false;
    for (uint32_t i = span.begin; i < span.end; i++)
    {
        char c = lib->text[i];
        if (c == '"')
        {
            quoted = !quoted;
            continue;
        }
        if (c == '\\' && i + 1 < span.end)
        {
            char n = lib->text[i + 1];
            if (n == '\n')
            {
                i++;
                continue;
            }
            if (n == '\r' && i + 2 < span.end && lib->text[i + 2] == '\n')
            {
                i += 2;
                continue;
            }
            if (quoted)
            {
                c = n;
                i++;
            }
            else if (n == ' ' || n == '\t')
                continue; // continuation with trailing blanks before the newline
        }
        else if (!quoted && c == '\n')
            c = ' ';
        if (length + 1 < cap)
            buffer[length] = c;
        length++;
    }
    if (cap)
        buffer[length < cap ? length : cap - 1] = 0;
    return length;
}

// Returns the span's text in a rotating internal buffer.
static inline const char* sn_liberty_span_text(sn_liberty_t* lib, sn_liberty_span_t span)
{
    uint32_t slot = lib->scratch_next;
    lib->scratch_next = (slot + 1) % SN_LIBERTY_SCRATCH_COUNT;
    size_t needed = sn_liberty_span_copy(lib, span, lib->scratch[slot], lib->scratch_cap[slot]) + 1;
    if (needed > lib->scratch_cap[slot])
    {
        size_t cap = needed < 64 ? 64 : needed;
        char* grown = (char*)realloc(lib->scratch[slot], cap);
        if (!grown)
        {
            lib->failed = true; // an empty string must not pass for a value
            return "";
        }
        lib->scratch[slot] = grown;
        lib->scratch_cap[slot] = cap;
        sn_liberty_span_copy(lib, span, lib->scratch[slot], cap);
    }
    return lib->scratch[slot];
}

static inline const char* sn_liberty_key(sn_liberty_t* lib, uint32_t id)
{
    return sn_liberty_span_text(lib, lib->items[id].key);
}

// The simple-attribute value, the complex-attribute argument text, or the
// group head, with quotes and continuations removed.
static inline const char* sn_liberty_value(sn_liberty_t* lib, uint32_t id)
{
    return sn_liberty_span_text(lib, lib->items[id].value);
}

// Splits a group head or complex-attribute argument list on commas outside
// quotes and parentheses. Returns the number of arguments.
static inline uint32_t sn_liberty_arg_count(const sn_liberty_t* lib, uint32_t id)
{
    sn_liberty_span_t span = lib->items[id].value;
    if (span.begin == span.end)
        return 0;
    uint32_t count = 1, depth = 0;
    bool quoted = false;
    for (uint32_t i = span.begin; i < span.end; i++)
    {
        char c = lib->text[i];
        if (c == '\\' && quoted)
            i++;
        else if (c == '"')
            quoted = !quoted;
        else if (!quoted && c == '(')
            depth++;
        else if (!quoted && c == ')')
            depth--;
        else if (!quoted && depth == 0 && c == ',')
            count++;
    }
    return count;
}

static inline sn_liberty_span_t sn_liberty_arg_span(const sn_liberty_t* lib, uint32_t id, uint32_t index)
{
    sn_liberty_span_t span = lib->items[id].value;
    uint32_t begin = span.begin, seen = 0, depth = 0;
    bool quoted = false;
    for (uint32_t i = span.begin; i < span.end; i++)
    {
        char c = lib->text[i];
        if (c == '\\' && quoted)
            i++;
        else if (c == '"')
            quoted = !quoted;
        else if (!quoted && c == '(')
            depth++;
        else if (!quoted && c == ')')
            depth--;
        else if (!quoted && depth == 0 && c == ',')
        {
            if (seen == index)
                return sn_liberty_trim(lib, begin, i);
            seen++;
            begin = i + 1;
        }
    }
    if (seen == index)
        return sn_liberty_trim(lib, begin, span.end);
    sn_liberty_span_t empty = {span.end, span.end};
    return empty;
}

// The index-th argument of a complex attribute or group head, unquoted.
static inline const char* sn_liberty_arg(sn_liberty_t* lib, uint32_t id, uint32_t index)
{
    return sn_liberty_span_text(lib, sn_liberty_arg_span(lib, id, index));
}

// The name of a group: its first head argument (cell(NAME), pin(NAME),
// ff(IQ, IQN) gives IQ). Empty for unnamed groups such as timing().
static inline const char* sn_liberty_name(sn_liberty_t* lib, uint32_t id)
{
    return sn_liberty_arg(lib, id, 0);
}

// ---------------------------------------------------------------------------
// Attribute lookups on a group

// The value of the simple attribute `key` in group `id`, or NULL when absent.
static inline const char* sn_liberty_attribute(sn_liberty_t* lib, uint32_t id, const char* key)
{
    uint32_t item = sn_liberty_find(lib, id, key, SN_LIBERTY_INVALID);
    if (item == SN_LIBERTY_INVALID || lib->items[item].kind != SN_LIBERTY_ATTRIBUTE)
        return NULL;
    return sn_liberty_value(lib, item);
}

// Reads a numeric simple attribute. The whole value must be a number (a
// trailing unit or other text is rejected), so callers can tell a malformed
// value from a missing one with sn_liberty_attribute().
static inline bool sn_liberty_attribute_double(sn_liberty_t* lib, uint32_t id, const char* key, double* out)
{
    const char* text = sn_liberty_attribute(lib, id, key);
    if (!text)
        return false;
    char* stop = NULL;
    double value = strtod(text, &stop);
    if (stop == text)
        return false;
    while (*stop && isspace((unsigned char)*stop))
        stop++;
    if (*stop || !(value == value) || value > 1e300 || value < -1e300)
        return false;
    *out = value;
    return true;
}

// Boolean attributes are written true/false; the manual also allows the
// enumerations in quotes, which sn_liberty_value already removed.
static inline bool sn_liberty_attribute_bool(sn_liberty_t* lib, uint32_t id, const char* key, bool* out)
{
    const char* text = sn_liberty_attribute(lib, id, key);
    if (!text)
        return false;
    if (strcmp(text, "true") == 0 || strcmp(text, "TRUE") == 0)
        *out = true;
    else if (strcmp(text, "false") == 0 || strcmp(text, "FALSE") == 0)
        *out = false;
    else
        return false;
    return true;
}

// ---------------------------------------------------------------------------
// Writer, mainly for round-trip tests and debugging

static inline void sn_liberty_write_item(sn_liberty_t* lib, uint32_t id, FILE* out, int indent)
{
    for (; id != SN_LIBERTY_INVALID; id = lib->items[id].next)
    {
        const sn_liberty_item_t* item = &lib->items[id];
        fprintf(out, "%*s%s", indent, "", sn_liberty_key(lib, id));
        if (item->kind == SN_LIBERTY_ATTRIBUTE)
            fprintf(out, " : %.*s ;\n", (int)(item->value.end - item->value.begin), lib->text + item->value.begin);
        else if (item->kind == SN_LIBERTY_COMPLEX)
            fprintf(out, " (%.*s) ;\n", (int)(item->value.end - item->value.begin), lib->text + item->value.begin);
        else
        {
            fprintf(out, " (%.*s) {\n", (int)(item->value.end - item->value.begin), lib->text + item->value.begin);
            sn_liberty_write_item(lib, item->child, out, indent + 2);
            fprintf(out, "%*s}\n", indent, "");
        }
    }
}

static inline void sn_liberty_write(sn_liberty_t* lib, FILE* out)
{
    sn_liberty_write_item(lib, sn_liberty_first_child(lib, lib->root), out, 0);
}

// ---------------------------------------------------------------------------
// Boolean expressions
//
// Grammar from the manual ("function Simple Attribute", Table 9): operands are
// pin names, 0, and 1; operators are ' (postfix NOT), ! (prefix NOT),
// ^ (XOR), * & and juxtaposition (AND), + | (OR), with parentheses.
// Precedence, tightest first: inversion, XOR, AND, OR; equal levels associate
// left to right. Note that XOR binds tighter than AND, unlike C. A pin name
// that begins with a digit is written as an escaped quoted string, \"1A\".

typedef enum sn_liberty_op_t
{
    SN_LIBERTY_CONST0 = 0,
    SN_LIBERTY_CONST1,
    SN_LIBERTY_PIN,
    SN_LIBERTY_NOT,
    SN_LIBERTY_AND,
    SN_LIBERTY_OR,
    SN_LIBERTY_XOR
} sn_liberty_op_t;

typedef struct sn_liberty_node_t
{
    uint32_t op;    // sn_liberty_op_t
    uint32_t left;  // operand, or the name offset for SN_LIBERTY_PIN
    uint32_t right; // second operand of binary operators
} sn_liberty_node_t;

typedef struct sn_liberty_expr_t
{
    sn_liberty_node_t* nodes;
    uint32_t count;
    uint32_t cap;
    uint32_t root;
    char* names; // NUL-separated pin names referenced by nodes
    uint32_t names_size;
    uint32_t names_cap;
    char* error;
    bool out_of_memory; // the failure was an allocation, not the text
} sn_liberty_expr_t;

static inline void sn_liberty_expr_init(sn_liberty_expr_t* expr)
{
    memset(expr, 0, sizeof(*expr));
    expr->root = SN_LIBERTY_INVALID;
}

static inline void sn_liberty_expr_destroy(sn_liberty_expr_t* expr)
{
    free(expr->nodes);
    free(expr->names);
    free(expr->error);
    sn_liberty_expr_init(expr);
}

static inline const char* sn_liberty_expr_pin_name(const sn_liberty_expr_t* expr, uint32_t node)
{
    return expr->nodes[node].op == SN_LIBERTY_PIN ? expr->names + expr->nodes[node].left : NULL;
}

typedef struct sn_liberty_expr_parser_t
{
    sn_liberty_expr_t* expr;
    const char* text;
    size_t pos;
} sn_liberty_expr_parser_t;

static inline void sn_liberty_expr_error(sn_liberty_expr_parser_t* parser, const char* message)
{
    if (parser->expr->error)
        return;
    size_t length = strlen(message) + strlen(parser->text) + 64;
    parser->expr->error = (char*)malloc(length);
    if (!parser->expr->error)
        parser->expr->out_of_memory = true;
    if (parser->expr->error)
        snprintf(parser->expr->error, length, "%s at offset %zu in \"%s\"", message, parser->pos, parser->text);
}

static inline uint32_t sn_liberty_expr_node(sn_liberty_expr_parser_t* parser, sn_liberty_op_t op, uint32_t left,
                                            uint32_t right)
{
    sn_liberty_expr_t* expr = parser->expr;
    if (expr->count == expr->cap)
    {
        uint32_t cap = expr->cap ? expr->cap * 2 : 16;
        sn_liberty_node_t* nodes = (sn_liberty_node_t*)realloc(expr->nodes, (size_t)cap * sizeof(sn_liberty_node_t));
        if (!nodes)
        {
            expr->out_of_memory = true;
            sn_liberty_expr_error(parser, "out of memory");
            return SN_LIBERTY_INVALID;
        }
        expr->nodes = nodes;
        expr->cap = cap;
    }
    sn_liberty_node_t* node = &expr->nodes[expr->count];
    node->op = (uint32_t)op;
    node->left = left;
    node->right = right;
    return expr->count++;
}

static inline uint32_t sn_liberty_expr_pin(sn_liberty_expr_parser_t* parser, const char* name, size_t length)
{
    sn_liberty_expr_t* expr = parser->expr;
    // Reuse an existing name so equal pins share one offset.
    for (uint32_t offset = 0; offset < expr->names_size;)
    {
        size_t existing = strlen(expr->names + offset);
        if (existing == length && memcmp(expr->names + offset, name, length) == 0)
            return sn_liberty_expr_node(parser, SN_LIBERTY_PIN, offset, SN_LIBERTY_INVALID);
        offset += (uint32_t)existing + 1;
    }
    if (expr->names_size + length + 1 > expr->names_cap)
    {
        uint32_t cap = expr->names_cap ? expr->names_cap * 2 : 64;
        while (cap < expr->names_size + length + 1)
            cap *= 2;
        char* names = (char*)realloc(expr->names, cap);
        if (!names)
        {
            expr->out_of_memory = true;
            sn_liberty_expr_error(parser, "out of memory");
            return SN_LIBERTY_INVALID;
        }
        expr->names = names;
        expr->names_cap = cap;
    }
    uint32_t offset = expr->names_size;
    memcpy(expr->names + offset, name, length);
    expr->names[offset + length] = 0;
    expr->names_size += (uint32_t)length + 1;
    return sn_liberty_expr_node(parser, SN_LIBERTY_PIN, offset, SN_LIBERTY_INVALID);
}

static inline void sn_liberty_expr_skip(sn_liberty_expr_parser_t* parser)
{
    while (parser->text[parser->pos] && isspace((unsigned char)parser->text[parser->pos]))
        parser->pos++;
}

static inline bool sn_liberty_expr_is_name_char(char c)
{
    return isalnum((unsigned char)c) || c == '_' || c == '[' || c == ']' || c == '.' || c == '$';
}

// True when the next token can start an operand, which makes juxtaposition an
// implicit AND.
static inline bool sn_liberty_expr_starts_operand(sn_liberty_expr_parser_t* parser)
{
    sn_liberty_expr_skip(parser);
    char c = parser->text[parser->pos];
    return c == '(' || c == '!' || c == '"' || c == '\\' || sn_liberty_expr_is_name_char(c);
}

static inline uint32_t sn_liberty_expr_parse_or(sn_liberty_expr_parser_t* parser);

static inline uint32_t sn_liberty_expr_parse_primary(sn_liberty_expr_parser_t* parser)
{
    sn_liberty_expr_skip(parser);
    const char* text = parser->text;
    char c = text[parser->pos];
    if (c == '(')
    {
        parser->pos++;
        uint32_t inner = sn_liberty_expr_parse_or(parser);
        sn_liberty_expr_skip(parser);
        if (text[parser->pos] != ')')
        {
            sn_liberty_expr_error(parser, "expected ')'");
            return SN_LIBERTY_INVALID;
        }
        parser->pos++;
        return inner;
    }
    if (c == '\\' || c == '"')
    {
        // Escaped quoted name: \"1A\" inside the attribute string, or "1A"
        // once the attribute's own quotes were stripped.
        if (c == '\\')
            parser->pos++;
        if (text[parser->pos] != '"')
        {
            sn_liberty_expr_error(parser, "expected quoted pin name");
            return SN_LIBERTY_INVALID;
        }
        size_t begin = ++parser->pos;
        while (text[parser->pos] && text[parser->pos] != '"' && text[parser->pos] != '\\')
            parser->pos++;
        size_t end = parser->pos;
        if (text[parser->pos] == '\\')
            parser->pos++;
        if (text[parser->pos] != '"')
        {
            sn_liberty_expr_error(parser, "unterminated quoted pin name");
            return SN_LIBERTY_INVALID;
        }
        parser->pos++;
        return sn_liberty_expr_pin(parser, text + begin, end - begin);
    }
    if (sn_liberty_expr_is_name_char(c))
    {
        size_t begin = parser->pos;
        while (sn_liberty_expr_is_name_char(text[parser->pos]))
            parser->pos++;
        size_t length = parser->pos - begin;
        if (length == 1 && (c == '0' || c == '1'))
            return sn_liberty_expr_node(parser, c == '0' ? SN_LIBERTY_CONST0 : SN_LIBERTY_CONST1, SN_LIBERTY_INVALID,
                                        SN_LIBERTY_INVALID);
        return sn_liberty_expr_pin(parser, text + begin, length);
    }
    sn_liberty_expr_error(parser, c ? "unexpected character" : "unexpected end of expression");
    return SN_LIBERTY_INVALID;
}

// inversion: '!' unary | primary { "'" }
static inline uint32_t sn_liberty_expr_parse_unary(sn_liberty_expr_parser_t* parser)
{
    sn_liberty_expr_skip(parser);
    if (parser->text[parser->pos] == '!')
    {
        parser->pos++;
        uint32_t operand = sn_liberty_expr_parse_unary(parser);
        if (operand == SN_LIBERTY_INVALID)
            return operand;
        return sn_liberty_expr_node(parser, SN_LIBERTY_NOT, operand, SN_LIBERTY_INVALID);
    }
    uint32_t node = sn_liberty_expr_parse_primary(parser);
    for (;;)
    {
        if (node == SN_LIBERTY_INVALID)
            return node;
        sn_liberty_expr_skip(parser);
        if (parser->text[parser->pos] != '\'')
            return node;
        parser->pos++;
        node = sn_liberty_expr_node(parser, SN_LIBERTY_NOT, node, SN_LIBERTY_INVALID);
    }
}

// xor: unary { '^' unary }
static inline uint32_t sn_liberty_expr_parse_xor(sn_liberty_expr_parser_t* parser)
{
    uint32_t node = sn_liberty_expr_parse_unary(parser);
    for (;;)
    {
        if (node == SN_LIBERTY_INVALID)
            return node;
        sn_liberty_expr_skip(parser);
        if (parser->text[parser->pos] != '^')
            return node;
        parser->pos++;
        uint32_t right = sn_liberty_expr_parse_unary(parser);
        if (right == SN_LIBERTY_INVALID)
            return right;
        node = sn_liberty_expr_node(parser, SN_LIBERTY_XOR, node, right);
    }
}

// and: xor { ('*' | '&' | juxtaposition) xor }
static inline uint32_t sn_liberty_expr_parse_and(sn_liberty_expr_parser_t* parser)
{
    uint32_t node = sn_liberty_expr_parse_xor(parser);
    for (;;)
    {
        if (node == SN_LIBERTY_INVALID)
            return node;
        sn_liberty_expr_skip(parser);
        char c = parser->text[parser->pos];
        if (c == '*' || c == '&')
            parser->pos++;
        else if (!sn_liberty_expr_starts_operand(parser))
            return node;
        uint32_t right = sn_liberty_expr_parse_xor(parser);
        if (right == SN_LIBERTY_INVALID)
            return right;
        node = sn_liberty_expr_node(parser, SN_LIBERTY_AND, node, right);
    }
}

// or: and { ('+' | '|') and }
static inline uint32_t sn_liberty_expr_parse_or(sn_liberty_expr_parser_t* parser)
{
    uint32_t node = sn_liberty_expr_parse_and(parser);
    for (;;)
    {
        if (node == SN_LIBERTY_INVALID)
            return node;
        sn_liberty_expr_skip(parser);
        char c = parser->text[parser->pos];
        if (c != '+' && c != '|')
            return node;
        parser->pos++;
        uint32_t right = sn_liberty_expr_parse_and(parser);
        if (right == SN_LIBERTY_INVALID)
            return right;
        node = sn_liberty_expr_node(parser, SN_LIBERTY_OR, node, right);
    }
}

// Parses a Boolean expression string (already unquoted, as returned by
// sn_liberty_attribute). On success expr->root is the top node; on failure
// expr->error describes the problem and the expression is left empty.
static inline bool sn_liberty_expr_parse(sn_liberty_expr_t* expr, const char* text)
{
    sn_liberty_expr_destroy(expr);
    sn_liberty_expr_parser_t parser;
    parser.expr = expr;
    parser.text = text;
    parser.pos = 0;
    uint32_t root = sn_liberty_expr_parse_or(&parser);
    if (root != SN_LIBERTY_INVALID)
    {
        sn_liberty_expr_skip(&parser);
        if (text[parser.pos])
        {
            sn_liberty_expr_error(&parser, "unexpected trailing text");
            root = SN_LIBERTY_INVALID;
        }
    }
    if (root == SN_LIBERTY_INVALID)
    {
        char* error = expr->error;
        bool out_of_memory = expr->out_of_memory;
        expr->error = NULL;
        sn_liberty_expr_destroy(expr);
        expr->error = error;
        expr->out_of_memory = out_of_memory;
        return false;
    }
    expr->root = root;
    return true;
}

// Evaluates an expression under an assignment given as parallel name/value
// arrays. Unassigned pins evaluate to false and are reported through
// `unknown` when it is not NULL.
static inline bool sn_liberty_expr_eval(const sn_liberty_expr_t* expr, uint32_t node, const char* const* names,
                                        const bool* values, uint32_t count, bool* unknown)
{
    const sn_liberty_node_t* n = &expr->nodes[node];
    switch ((sn_liberty_op_t)n->op)
    {
        case SN_LIBERTY_CONST0:
            return false;
        case SN_LIBERTY_CONST1:
            return true;
        case SN_LIBERTY_PIN:
            for (uint32_t i = 0; i < count; i++)
                if (strcmp(names[i], expr->names + n->left) == 0)
                    return values[i];
            if (unknown)
                *unknown = true;
            return false;
        case SN_LIBERTY_NOT:
            return !sn_liberty_expr_eval(expr, n->left, names, values, count, unknown);
        case SN_LIBERTY_AND:
        case SN_LIBERTY_OR:
        case SN_LIBERTY_XOR:
        {
            // Both operands are evaluated so every unassigned pin is reported.
            bool left = sn_liberty_expr_eval(expr, n->left, names, values, count, unknown);
            bool right = sn_liberty_expr_eval(expr, n->right, names, values, count, unknown);
            return n->op == SN_LIBERTY_AND ? (left && right) : n->op == SN_LIBERTY_OR ? (left || right) : (left != right);
        }
    }
    return false;
}

// Writes an expression in Liberty syntax with explicit parentheses, using
// the manual's operators: ! for NOT, * for AND, + for OR, ^ for XOR.
static inline void sn_liberty_expr_write(const sn_liberty_expr_t* expr, uint32_t node, FILE* out)
{
    const sn_liberty_node_t* n = &expr->nodes[node];
    switch ((sn_liberty_op_t)n->op)
    {
        case SN_LIBERTY_CONST0:
            fputs("0", out);
            return;
        case SN_LIBERTY_CONST1:
            fputs("1", out);
            return;
        case SN_LIBERTY_PIN:
        {
            // Quote names the parser would not read back as the same pin: a
            // leading digit (including the constants 0 and 1) or a character
            // outside the identifier set. The escaped form is the one the
            // manual uses inside function strings.
            const char* name = expr->names + n->left;
            bool plain = !isdigit((unsigned char)name[0]) && name[0];
            for (const char* c = name; plain && *c; c++)
                plain = sn_liberty_expr_is_name_char(*c);
            if (plain)
                fputs(name, out);
            else
                fprintf(out, "\\\"%s\\\"", name);
            return;
        }
        case SN_LIBERTY_NOT:
            fputs("!", out);
            sn_liberty_expr_write(expr, n->left, out);
            return;
        case SN_LIBERTY_AND:
        case SN_LIBERTY_OR:
        case SN_LIBERTY_XOR:
            fputs("(", out);
            sn_liberty_expr_write(expr, n->left, out);
            fputs(n->op == SN_LIBERTY_AND ? " * " : n->op == SN_LIBERTY_OR ? " + " : " ^ ", out);
            sn_liberty_expr_write(expr, n->right, out);
            fputs(")", out);
            return;
    }
}

// ===========================================================================
// Library model
//
// The model interprets the syntax tree into typed records for what mapping,
// timing, and power evaluation need: cells, pins of every kind, functional
// groups, timing arcs with resolved lookup tables, internal and leakage power,
// and the library-level units, defaults, templates, operating conditions, wire
// loads, and bus types. Every record keeps the id of the syntax item it came
// from, so attributes the model does not interpret remain reachable through
// the syntax API on model->syntax.
//
// Names are offsets into one interned string pool (sn_lib_name); expressions
// are indices into the model's expression array; absent names, expressions,
// and records are SN_LIB_NONE; absent numbers are NAN.

#define SN_LIB_NONE UINT32_MAX

typedef enum sn_lib_direction_t
{
    SN_LIB_DIRECTION_UNKNOWN = 0,
    SN_LIB_INPUT,
    SN_LIB_OUTPUT,
    SN_LIB_INOUT,
    SN_LIB_INTERNAL
} sn_lib_direction_t;

typedef enum sn_lib_pin_kind_t
{
    SN_LIB_PIN_SCALAR = 0, // pin(A)
    SN_LIB_PIN_BUS,        // bus(A) with a bus_type; its bits follow as SN_LIB_PIN_BIT
    SN_LIB_PIN_BUNDLE,     // bundle(Q) with members; its members follow as SN_LIB_PIN_BIT
    SN_LIB_PIN_BIT,        // one bit of a bus or one member of a bundle
    SN_LIB_PIN_PG          // pg_pin(VDD): power or ground
} sn_lib_pin_kind_t;

typedef enum sn_lib_sense_t
{
    SN_LIB_SENSE_UNKNOWN = 0,
    SN_LIB_POSITIVE_UNATE,
    SN_LIB_NEGATIVE_UNATE,
    SN_LIB_NON_UNATE
} sn_lib_sense_t;

// The timing_type values of the manual; SN_LIB_TIMING_OTHER keeps the raw
// name for values outside this list.
typedef enum sn_lib_timing_type_t
{
    SN_LIB_TIMING_COMBINATIONAL = 0,
    SN_LIB_TIMING_COMBINATIONAL_RISE,
    SN_LIB_TIMING_COMBINATIONAL_FALL,
    SN_LIB_TIMING_THREE_STATE_DISABLE,
    SN_LIB_TIMING_THREE_STATE_DISABLE_RISE,
    SN_LIB_TIMING_THREE_STATE_DISABLE_FALL,
    SN_LIB_TIMING_THREE_STATE_ENABLE,
    SN_LIB_TIMING_THREE_STATE_ENABLE_RISE,
    SN_LIB_TIMING_THREE_STATE_ENABLE_FALL,
    SN_LIB_TIMING_RISING_EDGE,
    SN_LIB_TIMING_FALLING_EDGE,
    SN_LIB_TIMING_PRESET,
    SN_LIB_TIMING_CLEAR,
    SN_LIB_TIMING_HOLD_RISING,
    SN_LIB_TIMING_HOLD_FALLING,
    SN_LIB_TIMING_SETUP_RISING,
    SN_LIB_TIMING_SETUP_FALLING,
    SN_LIB_TIMING_RECOVERY_RISING,
    SN_LIB_TIMING_RECOVERY_FALLING,
    SN_LIB_TIMING_REMOVAL_RISING,
    SN_LIB_TIMING_REMOVAL_FALLING,
    SN_LIB_TIMING_SKEW_RISING,
    SN_LIB_TIMING_SKEW_FALLING,
    SN_LIB_TIMING_MINIMUM_PULSE_WIDTH,
    SN_LIB_TIMING_MINIMUM_PERIOD,
    SN_LIB_TIMING_MIN_CLOCK_TREE_PATH,
    SN_LIB_TIMING_MAX_CLOCK_TREE_PATH,
    SN_LIB_TIMING_NON_SEQ_SETUP_RISING,
    SN_LIB_TIMING_NON_SEQ_SETUP_FALLING,
    SN_LIB_TIMING_NON_SEQ_HOLD_RISING,
    SN_LIB_TIMING_NON_SEQ_HOLD_FALLING,
    SN_LIB_TIMING_NOCHANGE_HIGH_HIGH,
    SN_LIB_TIMING_NOCHANGE_HIGH_LOW,
    SN_LIB_TIMING_NOCHANGE_LOW_HIGH,
    SN_LIB_TIMING_NOCHANGE_LOW_LOW,
    SN_LIB_TIMING_OTHER
} sn_lib_timing_type_t;

static const char* const sn_lib_timing_type_names[] = {
    "combinational", "combinational_rise", "combinational_fall", "three_state_disable",
    "three_state_disable_rise", "three_state_disable_fall", "three_state_enable", "three_state_enable_rise",
    "three_state_enable_fall", "rising_edge", "falling_edge", "preset", "clear", "hold_rising", "hold_falling",
    "setup_rising", "setup_falling", "recovery_rising", "recovery_falling", "removal_rising", "removal_falling",
    "skew_rising", "skew_falling", "minimum_pulse_width", "minimum_period", "min_clock_tree_path",
    "max_clock_tree_path", "non_seq_setup_rising", "non_seq_setup_falling", "non_seq_hold_rising",
    "non_seq_hold_falling", "nochange_high_high", "nochange_high_low", "nochange_low_high", "nochange_low_low"};

// clear_preset_var1/2 values (manual, Table 10): the output when clear and
// preset are active together.
typedef enum sn_lib_collision_t
{
    SN_LIB_COLLISION_UNSPECIFIED = 0,
    SN_LIB_COLLISION_LOW,      // L
    SN_LIB_COLLISION_HIGH,     // H
    SN_LIB_COLLISION_HOLD,     // N: no change
    SN_LIB_COLLISION_TOGGLE,   // T
    SN_LIB_COLLISION_UNKNOWN   // X
} sn_lib_collision_t;

// A lookup table template: the variables of each dimension and the default
// index values (lu_table_template, power_lut_template, and the CCS
// templates all share this shape).
typedef struct sn_lib_template_t
{
    uint32_t name;
    uint32_t kind;  // name of the group key, e.g. lu_table_template
    bool invalid;   // an index list failed to parse; tables using it are invalid
    uint32_t dims;
    uint32_t variable[3];     // names such as input_net_transition
    uint32_t index_offset[3]; // into model->doubles
    uint32_t index_count[3];
    uint32_t item;
} sn_lib_template_t;

// A lookup table: values in row-major order over the dimensions, with index
// arrays taken from the table when present and from its template otherwise.
// A "scalar" table has dims == 0 and one value.
typedef struct sn_lib_table_t
{
    uint32_t template_id; // SN_LIB_NONE for scalar or unresolved templates
    bool invalid;         // axes or values failed validation; lookups return NAN
    uint32_t dims;
    uint32_t index_offset[3];
    uint32_t index_count[3];
    uint32_t values_offset;
    uint32_t values_count;
    uint32_t item;
} sn_lib_table_t;

typedef struct sn_lib_timing_t
{
    uint32_t pin; // the pin whose timing group this is
    uint32_t related_pin;
    uint32_t related_bus_pins;
    uint32_t related_output_pin;
    uint32_t timing_type;      // sn_lib_timing_type_t
    uint32_t timing_type_name; // raw name; set for SN_LIB_TIMING_OTHER
    uint32_t sense;            // sn_lib_sense_t
    uint32_t when;             // expression
    uint32_t sdf_cond;         // raw text
    uint32_t cell_rise, cell_fall, rise_transition, fall_transition, rise_constraint, fall_constraint; // tables
    // Generic CMOS delay model values.
    double intrinsic_rise, intrinsic_fall, rise_resistance, fall_resistance;
    uint32_t item;
} sn_lib_timing_t;

typedef struct sn_lib_power_t
{
    uint32_t pin;
    uint32_t related_pin;
    uint32_t related_pg_pin;
    uint32_t when; // expression
    uint32_t rise_power, fall_power, power; // tables
    uint32_t item;
} sn_lib_power_t;

typedef struct sn_lib_leakage_t
{
    uint32_t cell;
    uint32_t when; // expression, SN_LIB_NONE for the unconditional entry
    uint32_t related_pg_pin;
    double value;
    uint32_t item;
} sn_lib_leakage_t;

typedef struct sn_lib_pin_t
{
    uint32_t name;
    uint32_t cell;
    uint32_t kind;      // sn_lib_pin_kind_t
    uint32_t direction; // sn_lib_direction_t
    bool in_test_cell;  // declared inside test_cell rather than the cell proper
    // Set when any attribute of this pin was present but malformed (an
    // unparsable function, an unknown direction, a bad number). The malformed
    // field is left absent rather than inheriting a value; an interface built
    // from an invalid pin must treat the cell as unresolved.
    bool invalid;
    bool clock;
    bool is_pad;
    // Bus and bundle structure.
    uint32_t parent;    // the bus or bundle pin of a SN_LIB_PIN_BIT, else SN_LIB_NONE
    uint32_t bus_type;  // name of the type group of a bus pin
    int32_t bus_from, bus_to; // declared bit range of a bus (bus_from is the MSB when downto)
    uint32_t bit_index; // position of a bit within its bus or bundle
    // Function.
    uint32_t function, three_state, state_function, x_function, power_down_function; // expressions
    uint32_t internal_node; // name
    uint32_t nextstate_type, signal_type, pin_func_type; // names
    // Electrical limits and loads.
    double capacitance, rise_capacitance, fall_capacitance;
    double max_capacitance, min_capacitance, max_transition, min_transition, max_fanout, fanout_load;
    double min_pulse_width_high, min_pulse_width_low, min_period;
    // Power and ground association.
    uint32_t related_power_pin, related_ground_pin;
    uint32_t pg_type, voltage_name; // pg_pin attributes
    // Arcs and power groups, contiguous in the model arrays.
    uint32_t timing_first, timing_count;
    uint32_t power_first, power_count;
    uint32_t item;
} sn_lib_pin_t;

// ff, ff_bank, latch, and latch_bank groups share one record. For latches
// next_state holds data_in and clocked_on holds enable (clocked_on_also
// holds enable_also).
typedef struct sn_lib_state_t
{
    uint32_t cell;
    bool is_latch;
    bool in_test_cell;
    bool invalid;        // a malformed expression or bank width
    uint32_t bits;       // 1, or the bank width
    uint32_t var1, var2; // internal state names, e.g. IQ and IQN
    uint32_t next_state, clocked_on, clocked_on_also, clear, preset, power_down_function; // expressions
    uint32_t collision_var1, collision_var2; // sn_lib_collision_t
    uint32_t item;
} sn_lib_state_t;

typedef struct sn_lib_statetable_t
{
    uint32_t cell;
    uint32_t inputs;  // the input node name list, space separated
    uint32_t outputs; // the internal node name list
    uint32_t table;   // the table text with rows separated by commas
    uint32_t item;
} sn_lib_statetable_t;

typedef struct sn_lib_cell_t
{
    uint32_t name;
    uint32_t footprint;
    double area;
    double cell_leakage_power;
    bool dont_use, dont_touch, is_macro, is_pad;
    // clock_gating_integrated_cell is an enumeration (latch_posedge,
    // latch_negedge_precontrol, ...); the flag records its presence.
    bool clock_gating_integrated;
    uint32_t clock_gating_integrated_cell;
    // Set when the cell or any of its pins or state groups is invalid.
    bool invalid;
    uint32_t pin_first, pin_count;
    uint32_t state_first, state_count;
    uint32_t statetable_first, statetable_count;
    uint32_t leakage_first, leakage_count;
    uint32_t test_cell_item; // SN_LIB_NONE without a test_cell group
    uint32_t item;
} sn_lib_cell_t;

typedef struct sn_lib_type_t
{
    uint32_t name;
    bool invalid; // sizes or range failed validation; buses of this type are not expanded
    uint32_t bit_width;
    int32_t bit_from, bit_to;
    bool downto;
    uint32_t item;
} sn_lib_type_t;

typedef struct sn_lib_operating_conditions_t
{
    uint32_t name;
    double process, temperature, voltage;
    uint32_t tree_type;
    uint32_t item;
} sn_lib_operating_conditions_t;

typedef struct sn_lib_wire_load_t
{
    uint32_t name;
    double resistance, capacitance, area, slope;
    uint32_t fanout_length_offset, fanout_length_count; // (fanout, length) pairs in doubles
    uint32_t item;
} sn_lib_wire_load_t;

typedef struct sn_lib_named_value_t
{
    uint32_t name;
    double value;
} sn_lib_named_value_t;

typedef struct sn_lib_define_t
{
    uint32_t attribute, group, type;
} sn_lib_define_t;

typedef struct sn_lib_t
{
    sn_liberty_t* syntax; // owned; item ids in the records refer to it; NULL after a binary load
    char* path;           // file name used in messages
    uint64_t source_size; // size and hash of the library text the model came from
    uint64_t source_hash;
    char* error;
    bool out_of_memory;       // a record or pool could not grow; the model is incomplete
    uint32_t malformed_count; // attributes present but unusable, each also warned about
    uint32_t invalid_cells;   // cells with any invalid record
    char** warnings;
    uint32_t warnings_count, warnings_cap;

    // Interned names and numeric pool.
    char* names;
    uint32_t names_size, names_cap;
    uint32_t* name_buckets;
    uint32_t name_bucket_count;
    double* doubles;
    uint32_t doubles_count, doubles_cap;
    sn_liberty_expr_t* exprs;
    uint32_t exprs_count, exprs_cap;

    // Library header.
    uint32_t name, technology, delay_model;
    uint32_t bus_naming_style; // the library's format, "%s[%d]" when absent
    uint32_t time_unit, voltage_unit, current_unit, leakage_power_unit, pulling_resistance_unit;
    double capacitive_load_unit;
    uint32_t capacitive_load_unit_name;
    double nom_process, nom_temperature, nom_voltage;
    uint32_t default_operating_conditions;
    sn_lib_named_value_t* defaults; // every numeric default_* attribute
    uint32_t defaults_count, defaults_cap;
    sn_lib_named_value_t* voltage_map;
    uint32_t voltage_map_count, voltage_map_cap;
    sn_lib_define_t* defines;
    uint32_t defines_count, defines_cap;
    sn_lib_template_t* templates;
    uint32_t templates_count, templates_cap;
    sn_lib_operating_conditions_t* conditions;
    uint32_t conditions_count, conditions_cap;
    sn_lib_wire_load_t* wire_loads;
    uint32_t wire_loads_count, wire_loads_cap;
    sn_lib_type_t* types;
    uint32_t types_count, types_cap;

    // Cells and their parts.
    sn_lib_cell_t* cells;
    uint32_t cells_count, cells_cap;
    uint32_t* cell_buckets; // name hash to cell id
    uint32_t cell_bucket_count;
    sn_lib_pin_t* pins;
    uint32_t pins_count, pins_cap;
    sn_lib_state_t* states;
    uint32_t states_count, states_cap;
    sn_lib_statetable_t* statetables;
    uint32_t statetables_count, statetables_cap;
    sn_lib_timing_t* timings;
    uint32_t timings_count, timings_cap;
    sn_lib_power_t* powers;
    uint32_t powers_count, powers_cap;
    sn_lib_leakage_t* leakages;
    uint32_t leakages_count, leakages_cap;
    sn_lib_table_t* tables;
    uint32_t tables_count, tables_cap;
} sn_lib_t;

// ---------------------------------------------------------------------------
// Model storage helpers

static inline void* sn_lib_push_raw(bool* out_of_memory, void** array, uint32_t* count, uint32_t* cap, size_t size)
{
    if (*count == *cap)
    {
        uint32_t new_cap = *cap ? *cap * 2 : 16;
        void* grown = realloc(*array, (size_t)new_cap * size);
        if (!grown)
        {
            *out_of_memory = true;
            return NULL;
        }
        *array = grown;
        *cap = new_cap;
    }
    void* slot = (char*)*array + (size_t)(*count)++ * size;
    memset(slot, 0, size);
    return slot;
}

#define SN_LIB_PUSH(model, field, type)                                                                     \
    ((type*)sn_lib_push_raw(&(model)->out_of_memory, (void**)&(model)->field, &(model)->field##_count, \
                            &(model)->field##_cap, sizeof(type)))

static inline void sn_lib_warn(sn_lib_t* model, uint32_t item, const char* format, ...)
{
    char message[512];
    va_list args;
    va_start(args, format);
    vsnprintf(message, sizeof(message), format, args);
    va_end(args);
    uint32_t line = model->syntax && item != SN_LIB_NONE && item < model->syntax->count
                        ? model->syntax->items[item].line
                        : 0;
    const char* path = model->path ? model->path : "?";
    size_t length = strlen(path) + strlen(message) + 64;
    char* text = (char*)malloc(length);
    if (!text)
    {
        model->out_of_memory = true;
        return;
    }
    snprintf(text, length, "%s:%u: %s", path, line, message);
    char** slot = SN_LIB_PUSH(model, warnings, char*);
    if (slot)
        *slot = text;
    else
        free(text);
}

static inline uint64_t sn_lib_hash_string(const char* text, size_t length)
{
    uint64_t hash = UINT64_C(1469598103934665603);
    for (size_t i = 0; i < length; i++)
        hash = (hash ^ (unsigned char)text[i]) * UINT64_C(1099511628211);
    return hash;
}

static inline const char* sn_lib_name(const sn_lib_t* model, uint32_t name)
{
    return name == SN_LIB_NONE ? "" : model->names + name;
}

// Interns a string and returns its offset; equal strings share one offset.
// Interns a string and returns its offset; equal strings share one offset.
// The pool may move: keep offsets, not pointers, across calls that intern.
static inline uint32_t sn_lib_intern(sn_lib_t* model, const char* text)
{
    if (!text)
        return SN_LIB_NONE;
    size_t length = strlen(text);
    if (!model->name_bucket_count)
    {
        uint32_t count = 1024;
        model->name_buckets = (uint32_t*)malloc(count * sizeof(uint32_t));
        if (!model->name_buckets)
        {
            model->out_of_memory = true;
            return SN_LIB_NONE;
        }
        memset(model->name_buckets, 0xff, count * sizeof(uint32_t));
        model->name_bucket_count = count;
    }
    uint64_t hash = sn_lib_hash_string(text, length);
    uint32_t bucket = (uint32_t)(hash & (model->name_bucket_count - 1));
    for (uint32_t probe = 0; probe < model->name_bucket_count; probe++)
    {
        uint32_t slot = (bucket + probe) & (model->name_bucket_count - 1);
        uint32_t offset = model->name_buckets[slot];
        if (offset == SN_LIB_NONE)
        {
            if (model->names_size + length + 1 > model->names_cap)
            {
                uint32_t cap = model->names_cap ? model->names_cap * 2 : 4096;
                while (cap < model->names_size + length + 1)
                    cap *= 2;
                char* names = (char*)realloc(model->names, cap);
                if (!names)
                {
                    model->out_of_memory = true;
                    return SN_LIB_NONE;
                }
                model->names = names;
                model->names_cap = cap;
            }
            offset = model->names_size;
            memcpy(model->names + offset, text, length + 1);
            model->names_size += (uint32_t)length + 1;
            model->name_buckets[slot] = offset;
            // Grow the table at 50% load by rehashing the pool; when the new
            // table cannot be allocated the old one keeps working, only slower.
            uint32_t used = 0;
            for (uint32_t i = 0; i < model->name_bucket_count; i++)
                used += model->name_buckets[i] != SN_LIB_NONE;
            if (used * 2 > model->name_bucket_count)
            {
                uint32_t count = model->name_bucket_count * 2;
                uint32_t* buckets = (uint32_t*)malloc(count * sizeof(uint32_t));
                if (buckets)
                {
                    memset(buckets, 0xff, count * sizeof(uint32_t));
                    for (uint32_t o = 0; o < model->names_size;)
                    {
                        size_t l = strlen(model->names + o);
                        uint32_t b = (uint32_t)(sn_lib_hash_string(model->names + o, l) & (count - 1));
                        while (buckets[b] != SN_LIB_NONE)
                            b = (b + 1) & (count - 1);
                        buckets[b] = o;
                        o += (uint32_t)l + 1;
                    }
                    free(model->name_buckets);
                    model->name_buckets = buckets;
                    model->name_bucket_count = count;
                }
            }
            return offset;
        }
        if (strcmp(model->names + offset, text) == 0)
            return offset;
    }
    model->out_of_memory = true; // a full table cannot happen below 50% load
    return SN_LIB_NONE;
}

static inline uint32_t sn_lib_push_double(sn_lib_t* model, double value)
{
    double* slot = SN_LIB_PUSH(model, doubles, double);
    if (!slot)
        return SN_LIB_NONE;
    *slot = value;
    return model->doubles_count - 1;
}

// Parses a comma or space separated list of numbers into the double pool.
static inline bool sn_lib_parse_numbers(sn_lib_t* model, const char* text, uint32_t* offset, uint32_t* count)
{
    *offset = model->doubles_count;
    *count = 0;
    const char* pos = text;
    for (;;)
    {
        while (*pos && (isspace((unsigned char)*pos) || *pos == ',' || *pos == '"' || *pos == '\\'))
            pos++;
        if (!*pos)
            return true;
        char* stop = NULL;
        double value = strtod(pos, &stop);
        if (stop == pos || !(value == value) || value > 1e300 || value < -1e300)
            return false;
        if (sn_lib_push_double(model, value) == SN_LIB_NONE)
            return false;
        (*count)++;
        pos = stop;
    }
}

static inline uint32_t sn_lib_parse_expression(sn_lib_t* model, uint32_t item, const char* text)
{
    if (!text)
        return SN_LIB_NONE;
    sn_liberty_expr_t* expr = SN_LIB_PUSH(model, exprs, sn_liberty_expr_t);
    if (!expr)
        return SN_LIB_NONE;
    sn_liberty_expr_init(expr);
    if (!sn_liberty_expr_parse(expr, text))
    {
        if (expr->out_of_memory)
            model->out_of_memory = true;
        else
        {
            sn_lib_warn(model, item, "cannot parse expression: %s", expr->error);
            model->malformed_count++;
        }
        sn_liberty_expr_destroy(expr);
        model->exprs_count--;
        return SN_LIB_NONE;
    }
    return model->exprs_count - 1;
}

static inline const sn_liberty_expr_t* sn_lib_expr(const sn_lib_t* model, uint32_t id)
{
    return id == SN_LIB_NONE ? NULL : &model->exprs[id];
}

// ---------------------------------------------------------------------------
// Attribute readers on syntax groups

static inline uint32_t sn_lib_read_name(sn_lib_t* model, uint32_t group, const char* key)
{
    return sn_lib_intern(model, sn_liberty_attribute(model->syntax, group, key));
}

// Reads a numeric attribute: NAN when absent, and NAN plus a warning and a
// malformed count when present but not a number.
static inline double sn_lib_read_double(sn_lib_t* model, uint32_t group, const char* key)
{
    double value;
    if (sn_liberty_attribute_double(model->syntax, group, key, &value))
        return value;
    const char* text = sn_liberty_attribute(model->syntax, group, key);
    if (text)
    {
        sn_lib_warn(model, group, "%s has a non-numeric value \"%s\"", key, text);
        model->malformed_count++;
    }
    return NAN;
}

static inline bool sn_lib_read_bool(sn_lib_t* model, uint32_t group, const char* key, bool fallback)
{
    bool value;
    if (sn_liberty_attribute_bool(model->syntax, group, key, &value))
        return value;
    const char* text = sn_liberty_attribute(model->syntax, group, key);
    if (text)
    {
        sn_lib_warn(model, group, "%s has a non-Boolean value \"%s\"", key, text);
        model->malformed_count++;
    }
    return fallback;
}

static inline uint32_t sn_lib_read_expr(sn_lib_t* model, uint32_t group, const char* key)
{
    uint32_t item = sn_liberty_find(model->syntax, group, key, SN_LIBERTY_INVALID);
    if (item == SN_LIBERTY_INVALID)
        return SN_LIB_NONE;
    return sn_lib_parse_expression(model, item, sn_liberty_value(model->syntax, item));
}

// Parses an integer in [minimum, maximum] from the whole of text.
static inline bool sn_lib_parse_int(const char* text, long minimum, long maximum, long* out)
{
    if (!text || !*text)
        return false;
    char* stop = NULL;
    long value = strtol(text, &stop, 10);
    while (*stop && isspace((unsigned char)*stop))
        stop++;
    if (stop == text || *stop || value < minimum || value > maximum)
        return false;
    *out = value;
    return true;
}

// Reads an integer attribute: false when absent; false plus a warning and a
// malformed count when present but outside [minimum, maximum] or not integral.
static inline bool sn_lib_read_int(sn_lib_t* model, uint32_t group, const char* key, long minimum, long maximum,
                                   long* out)
{
    const char* text = sn_liberty_attribute(model->syntax, group, key);
    if (!text)
        return false;
    if (sn_lib_parse_int(text, minimum, maximum, out))
        return true;
    sn_lib_warn(model, group, "%s must be an integer in [%ld, %ld], not \"%s\"", key, minimum, maximum, text);
    model->malformed_count++;
    return false;
}

static inline sn_lib_direction_t sn_lib_read_direction(sn_lib_t* model, uint32_t group)
{
    const char* text = sn_liberty_attribute(model->syntax, group, "direction");
    if (!text)
        return SN_LIB_DIRECTION_UNKNOWN;
    if (strcmp(text, "input") == 0)
        return SN_LIB_INPUT;
    if (strcmp(text, "output") == 0)
        return SN_LIB_OUTPUT;
    if (strcmp(text, "inout") == 0)
        return SN_LIB_INOUT;
    if (strcmp(text, "internal") == 0)
        return SN_LIB_INTERNAL;
    sn_lib_warn(model, group, "unknown pin direction \"%s\"", text);
    model->malformed_count++;
    return SN_LIB_DIRECTION_UNKNOWN;
}

static inline sn_lib_collision_t sn_lib_read_collision(sn_lib_t* model, uint32_t group, const char* key)
{
    const char* text = sn_liberty_attribute(model->syntax, group, key);
    if (!text)
        return SN_LIB_COLLISION_UNSPECIFIED;
    switch (text[0])
    {
        case 'L': return SN_LIB_COLLISION_LOW;
        case 'H': return SN_LIB_COLLISION_HIGH;
        case 'N': return SN_LIB_COLLISION_HOLD;
        case 'T': return SN_LIB_COLLISION_TOGGLE;
        case 'X': return SN_LIB_COLLISION_UNKNOWN;
        default: break;
    }
    sn_lib_warn(model, group, "unknown %s value \"%s\"", key, text);
    model->malformed_count++;
    return SN_LIB_COLLISION_UNSPECIFIED;
}

// ---------------------------------------------------------------------------
// Templates and tables

static inline uint32_t sn_lib_find_template(const sn_lib_t* model, const char* name)
{
    for (uint32_t i = 0; i < model->templates_count; i++)
        if (strcmp(sn_lib_name(model, model->templates[i].name), name) == 0)
            return i;
    return SN_LIB_NONE;
}

// Reads index_1..index_3 complex attributes of a template or table group.
// Reads index_1..index_3 complex attributes of a template or table group.
// Returns the number of leading axes present; a list that fails to parse is
// reported through *bad.
static inline uint32_t sn_lib_read_indices(sn_lib_t* model, uint32_t group, uint32_t* offsets, uint32_t* counts,
                                           bool* bad)
{
    uint32_t dims = 0;
    static const char* const keys[3] = {"index_1", "index_2", "index_3"};
    for (uint32_t d = 0; d < 3; d++)
    {
        offsets[d] = SN_LIB_NONE;
        counts[d] = 0;
        uint32_t item = sn_liberty_find(model->syntax, group, keys[d], SN_LIBERTY_INVALID);
        if (item == SN_LIBERTY_INVALID)
            continue;
        if (!sn_lib_parse_numbers(model, sn_liberty_value(model->syntax, item), &offsets[d], &counts[d]))
        {
            sn_lib_warn(model, item, "cannot parse %s", keys[d]);
            offsets[d] = SN_LIB_NONE;
            counts[d] = 0;
            *bad = true;
        }
        else
            dims = d + 1;
    }
    return dims;
}

static inline void sn_lib_read_template(sn_lib_t* model, uint32_t group)
{
    sn_lib_template_t* t = SN_LIB_PUSH(model, templates, sn_lib_template_t);
    if (!t)
        return;
    t->name = sn_lib_intern(model, sn_liberty_name(model->syntax, group));
    t->kind = sn_lib_intern(model, sn_liberty_key(model->syntax, group));
    t->item = group;
    t->variable[0] = sn_lib_read_name(model, group, "variable_1");
    t->variable[1] = sn_lib_read_name(model, group, "variable_2");
    t->variable[2] = sn_lib_read_name(model, group, "variable_3");
    bool bad = false;
    t->dims = sn_lib_read_indices(model, group, t->index_offset, t->index_count, &bad);
    for (uint32_t d = 0; d < 3; d++)
        if (t->variable[d] != SN_LIB_NONE && d + 1 > t->dims)
            t->dims = d + 1; // a template may declare variables and leave the indices to each table
    if (bad)
    {
        t->invalid = true;
        model->malformed_count++;
    }
}

// Reads a table group such as cell_rise(template) { index_1(...); values(...); }.
static inline uint32_t sn_lib_read_table(sn_lib_t* model, uint32_t group)
{
    if (group == SN_LIBERTY_INVALID)
        return SN_LIB_NONE;
    sn_lib_table_t* table = SN_LIB_PUSH(model, tables, sn_lib_table_t);
    if (!table)
        return SN_LIB_NONE;
    uint32_t id = model->tables_count - 1;
    table->item = group;
    table->template_id = SN_LIB_NONE;
    const char* template_name = sn_liberty_name(model->syntax, group);
    bool scalar = strcmp(template_name, "scalar") == 0;
    if (!scalar && template_name[0])
    {
        table->template_id = sn_lib_find_template(model, template_name);
        if (table->template_id == SN_LIB_NONE)
            sn_lib_warn(model, group, "unknown table template \"%s\"", template_name);
    }
    bool bad = false;
    uint32_t dims = sn_lib_read_indices(model, group, table->index_offset, table->index_count, &bad);
    uint32_t required = dims;
    if (table->template_id != SN_LIB_NONE)
    {
        const sn_lib_template_t* t = &model->templates[table->template_id];
        if (t->invalid)
            bad = true;
        required = t->dims;
        for (uint32_t d = 0; d < 3; d++)
            if (table->index_offset[d] == SN_LIB_NONE && t->index_offset[d] != SN_LIB_NONE)
            {
                table->index_offset[d] = t->index_offset[d];
                table->index_count[d] = t->index_count[d];
                if (d + 1 > dims)
                    dims = d + 1;
            }
    }
    // The template's dimensionality is binding: a two-variable template needs
    // two axes from the template or the table, else the table is unusable.
    if (!scalar && required > dims)
    {
        sn_lib_warn(model, group, "table has %u of the %u axes its template declares", dims, required);
        bad = true;
    }
    table->dims = scalar ? 0 : dims;
    uint32_t values = sn_liberty_find(model->syntax, group, "values", SN_LIBERTY_INVALID);
    if (values == SN_LIBERTY_INVALID)
    {
        sn_lib_warn(model, group, "table without values");
        bad = true;
    }
    else if (!sn_lib_parse_numbers(model, sn_liberty_value(model->syntax, values), &table->values_offset,
                                   &table->values_count))
    {
        sn_lib_warn(model, values, "cannot parse table values");
        table->values_count = 0;
        bad = true;
    }
    if (bad)
        table->invalid = true;
    // Validate the axes and the value count before anything interpolates.
    uint32_t expected = 1;
    for (uint32_t d = 0; d < table->dims; d++)
    {
        if (table->index_offset[d] == SN_LIB_NONE || table->index_count[d] == 0)
        {
            sn_lib_warn(model, group, "table is missing index_%u", d + 1);
            table->invalid = true;
            continue;
        }
        const double* axis = model->doubles + table->index_offset[d];
        for (uint32_t i = 1; i < table->index_count[d]; i++)
            if (!(axis[i] > axis[i - 1]))
            {
                sn_lib_warn(model, group, "index_%u is not strictly increasing", d + 1);
                table->invalid = true;
                break;
            }
        expected *= table->index_count[d];
    }
    if (!table->values_count)
        table->invalid = true;
    else if (table->values_count != expected)
    {
        sn_lib_warn(model, group, "table has %u values for %u index points", table->values_count, expected);
        table->invalid = true;
    }
    if (table->invalid)
        model->malformed_count++;
    return id;
}

static inline uint32_t sn_lib_read_table_named(sn_lib_t* model, uint32_t group, const char* key)
{
    return sn_lib_read_table(model, sn_liberty_find(model->syntax, group, key, SN_LIBERTY_INVALID));
}

static inline double sn_lib_table_value(const sn_lib_t* model, uint32_t table_id, uint32_t i, uint32_t j,
                                        uint32_t k)
{
    const sn_lib_table_t* table = &model->tables[table_id];
    if (table->invalid)
        return NAN;
    uint32_t index = i;
    if (table->dims > 1)
        index = index * table->index_count[1] + j;
    if (table->dims > 2)
        index = index * table->index_count[2] + k;
    return index < table->values_count ? model->doubles[table->values_offset + index] : NAN;
}

// Locates x on an axis: the lower index and the interpolation weight, with
// linear extrapolation outside the axis range.
static inline void sn_lib_axis_locate(const double* axis, uint32_t count, double x, uint32_t* lower, double* weight)
{
    if (count < 2)
    {
        *lower = 0;
        *weight = 0.0;
        return;
    }
    uint32_t i = 0;
    while (i + 2 < count && x > axis[i + 1])
        i++;
    *lower = i;
    double span = axis[i + 1] - axis[i];
    *weight = span != 0.0 ? (x - axis[i]) / span : 0.0;
}

// Evaluates a table at (x, y) with linear interpolation along each axis;
// unused axes are ignored (a 1-D table takes x, a scalar table neither).
// Evaluates a table of up to three dimensions at (x, y, z) with linear
// interpolation along each axis and linear extrapolation outside the axis
// ranges; unused coordinates are ignored (a 1-D table takes x, a scalar
// table none). Invalid tables give NAN.
static inline double sn_lib_table_lookup3(const sn_lib_t* model, uint32_t table_id, double x, double y, double z)
{
    if (table_id == SN_LIB_NONE)
        return NAN;
    const sn_lib_table_t* table = &model->tables[table_id];
    if (table->invalid)
        return NAN;
    if (table->dims == 0 || table->values_count == 1)
        return model->doubles[table->values_offset];
    const double coordinate[3] = {x, y, z};
    uint32_t lower[3] = {0, 0, 0}, upper[3] = {0, 0, 0};
    double weight[3] = {0.0, 0.0, 0.0};
    for (uint32_t d = 0; d < table->dims; d++)
    {
        sn_lib_axis_locate(model->doubles + table->index_offset[d], table->index_count[d], coordinate[d], &lower[d],
                           &weight[d]);
        upper[d] = table->index_count[d] > 1 ? lower[d] + 1 : lower[d];
    }
    // Multilinear interpolation over the 2^dims corners.
    double result = 0.0;
    for (uint32_t corner = 0; corner < (1u << table->dims); corner++)
    {
        double factor = 1.0;
        uint32_t index[3] = {0, 0, 0};
        for (uint32_t d = 0; d < table->dims; d++)
        {
            bool high = (corner >> d) & 1u;
            factor *= high ? weight[d] : 1.0 - weight[d];
            index[d] = high ? upper[d] : lower[d];
        }
        if (factor != 0.0)
            result += factor * sn_lib_table_value(model, table_id, index[0], index[1], index[2]);
    }
    return result;
}

// Two-coordinate lookup for the common delay and power tables. A table with
// three dimensions needs sn_lib_table_lookup3 and gives NAN here.
static inline double sn_lib_table_lookup(const sn_lib_t* model, uint32_t table_id, double x, double y)
{
    if (table_id != SN_LIB_NONE && model->tables[table_id].dims > 2)
        return NAN;
    return sn_lib_table_lookup3(model, table_id, x, y, 0.0);
}

// ---------------------------------------------------------------------------
// Timing, power, and leakage groups

static inline void sn_lib_read_timing(sn_lib_t* model, uint32_t pin_id, uint32_t group)
{
    sn_lib_timing_t* arc = SN_LIB_PUSH(model, timings, sn_lib_timing_t);
    if (!arc)
        return;
    sn_liberty_t* syntax = model->syntax;
    arc->pin = pin_id;
    arc->item = group;
    arc->related_pin = sn_lib_read_name(model, group, "related_pin");
    arc->related_bus_pins = sn_lib_read_name(model, group, "related_bus_pins");
    arc->related_output_pin = sn_lib_read_name(model, group, "related_output_pin");
    arc->sdf_cond = sn_lib_read_name(model, group, "sdf_cond");
    arc->when = sn_lib_read_expr(model, group, "when");
    const char* type = sn_liberty_attribute(syntax, group, "timing_type");
    arc->timing_type = SN_LIB_TIMING_COMBINATIONAL;
    arc->timing_type_name = SN_LIB_NONE;
    if (type)
    {
        arc->timing_type = SN_LIB_TIMING_OTHER;
        // Libraries write the pulse-width check as min_pulse_width as often as
        // the manual's minimum_pulse_width.
        if (strcmp(type, "min_pulse_width") == 0)
            type = "minimum_pulse_width";
        for (uint32_t i = 0; i < sizeof(sn_lib_timing_type_names) / sizeof(sn_lib_timing_type_names[0]); i++)
            if (strcmp(type, sn_lib_timing_type_names[i]) == 0)
            {
                arc->timing_type = i;
                break;
            }
        if (arc->timing_type == SN_LIB_TIMING_OTHER)
            arc->timing_type_name = sn_lib_intern(model, type);
    }
    const char* sense = sn_liberty_attribute(syntax, group, "timing_sense");
    arc->sense = SN_LIB_SENSE_UNKNOWN;
    if (sense)
    {
        if (strcmp(sense, "positive_unate") == 0)
            arc->sense = SN_LIB_POSITIVE_UNATE;
        else if (strcmp(sense, "negative_unate") == 0)
            arc->sense = SN_LIB_NEGATIVE_UNATE;
        else if (strcmp(sense, "non_unate") == 0)
            arc->sense = SN_LIB_NON_UNATE;
        else
            sn_lib_warn(model, group, "unknown timing_sense \"%s\"", sense);
    }
    arc->intrinsic_rise = sn_lib_read_double(model, group, "intrinsic_rise");
    arc->intrinsic_fall = sn_lib_read_double(model, group, "intrinsic_fall");
    arc->rise_resistance = sn_lib_read_double(model, group, "rise_resistance");
    arc->fall_resistance = sn_lib_read_double(model, group, "fall_resistance");
    // Tables are read after the scalar fields; reading may push more arcs'
    // worth of storage, so re-fetch the record pointer through its index.
    uint32_t id = model->timings_count - 1;
    uint32_t cell_rise = sn_lib_read_table_named(model, group, "cell_rise");
    uint32_t cell_fall = sn_lib_read_table_named(model, group, "cell_fall");
    uint32_t rise_transition = sn_lib_read_table_named(model, group, "rise_transition");
    uint32_t fall_transition = sn_lib_read_table_named(model, group, "fall_transition");
    uint32_t rise_constraint = sn_lib_read_table_named(model, group, "rise_constraint");
    uint32_t fall_constraint = sn_lib_read_table_named(model, group, "fall_constraint");
    arc = &model->timings[id];
    arc->cell_rise = cell_rise;
    arc->cell_fall = cell_fall;
    arc->rise_transition = rise_transition;
    arc->fall_transition = fall_transition;
    arc->rise_constraint = rise_constraint;
    arc->fall_constraint = fall_constraint;
}

static inline void sn_lib_read_power(sn_lib_t* model, uint32_t pin_id, uint32_t group)
{
    sn_lib_power_t* power = SN_LIB_PUSH(model, powers, sn_lib_power_t);
    if (!power)
        return;
    uint32_t id = model->powers_count - 1;
    power->pin = pin_id;
    power->item = group;
    power->related_pin = sn_lib_read_name(model, group, "related_pin");
    power->related_pg_pin = sn_lib_read_name(model, group, "related_pg_pin");
    power->when = sn_lib_read_expr(model, group, "when");
    uint32_t rise = sn_lib_read_table_named(model, group, "rise_power");
    uint32_t fall = sn_lib_read_table_named(model, group, "fall_power");
    uint32_t both = sn_lib_read_table_named(model, group, "power");
    power = &model->powers[id];
    power->rise_power = rise;
    power->fall_power = fall;
    power->power = both;
}

// ---------------------------------------------------------------------------
// Pins

static inline void sn_lib_pin_init(sn_lib_pin_t* pin, uint32_t cell)
{
    pin->cell = cell;
    pin->parent = SN_LIB_NONE;
    pin->bus_type = SN_LIB_NONE;
    pin->function = pin->three_state = pin->state_function = pin->x_function = pin->power_down_function =
        SN_LIB_NONE;
    pin->internal_node = pin->nextstate_type = pin->signal_type = pin->pin_func_type = SN_LIB_NONE;
    pin->related_power_pin = pin->related_ground_pin = pin->pg_type = pin->voltage_name = SN_LIB_NONE;
    pin->capacitance = pin->rise_capacitance = pin->fall_capacitance = NAN;
    pin->max_capacitance = pin->min_capacitance = pin->max_transition = pin->min_transition = NAN;
    pin->max_fanout = pin->fanout_load = NAN;
    pin->min_pulse_width_high = pin->min_pulse_width_low = pin->min_period = NAN;
    pin->timing_first = pin->power_first = 0;
    pin->timing_count = pin->power_count = 0;
    pin->item = SN_LIB_NONE;
}

// Reads the attributes of a pin, bus, or bundle group into an existing pin
// record; then its timing and internal_power groups.
static inline void sn_lib_read_pin_attributes(sn_lib_t* model, uint32_t pin_id, uint32_t group)
{
    sn_lib_pin_t* pin = &model->pins[pin_id];
    pin->item = group;
    uint32_t malformed_before = model->malformed_count;
    if (sn_liberty_attribute(model->syntax, group, "direction"))
        pin->direction = sn_lib_read_direction(model, group); // unknown text leaves UNKNOWN, not the parent's
    // A Boolean that is present replaces the inherited one; malformed text
    // gives false (and marks the pin invalid below).
    if (sn_liberty_attribute(model->syntax, group, "clock"))
        pin->clock = sn_lib_read_bool(model, group, "clock", false);
    if (sn_liberty_attribute(model->syntax, group, "is_pad"))
        pin->is_pad = sn_lib_read_bool(model, group, "is_pad", false);
    // An expression attribute that is present replaces the inherited one even
    // when it fails to parse: the field becomes absent and the pin invalid.
#define SN_LIB_READ_EXPR_FIELD(field)                                                             \
    do                                                                                            \
    {                                                                                             \
        bool present = sn_liberty_find(model->syntax, group, #field, SN_LIBERTY_INVALID) != SN_LIBERTY_INVALID; \
        uint32_t e = sn_lib_read_expr(model, group, #field);                                       \
        pin = &model->pins[pin_id];                                                               \
        if (present)                                                                              \
            pin->field = e;                                                                       \
    } while (0)
    SN_LIB_READ_EXPR_FIELD(function);
    SN_LIB_READ_EXPR_FIELD(three_state);
    SN_LIB_READ_EXPR_FIELD(state_function);
    SN_LIB_READ_EXPR_FIELD(x_function);
    SN_LIB_READ_EXPR_FIELD(power_down_function);
#undef SN_LIB_READ_EXPR_FIELD
#define SN_LIB_READ_NAME_FIELD(field) \
    do { uint32_t n = sn_lib_read_name(model, group, #field); if (n != SN_LIB_NONE) pin->field = n; } while (0)
    SN_LIB_READ_NAME_FIELD(internal_node);
    SN_LIB_READ_NAME_FIELD(nextstate_type);
    SN_LIB_READ_NAME_FIELD(signal_type);
    SN_LIB_READ_NAME_FIELD(pin_func_type);
    SN_LIB_READ_NAME_FIELD(related_power_pin);
    SN_LIB_READ_NAME_FIELD(related_ground_pin);
    SN_LIB_READ_NAME_FIELD(pg_type);
    SN_LIB_READ_NAME_FIELD(voltage_name);
#undef SN_LIB_READ_NAME_FIELD
#define SN_LIB_READ_DOUBLE_FIELD(field)                                                  \
    do                                                                                   \
    {                                                                                    \
        if (sn_liberty_attribute(model->syntax, group, #field))                          \
            pin->field = sn_lib_read_double(model, group, #field); /* NAN when malformed */ \
    } while (0)
    SN_LIB_READ_DOUBLE_FIELD(capacitance);
    SN_LIB_READ_DOUBLE_FIELD(rise_capacitance);
    SN_LIB_READ_DOUBLE_FIELD(fall_capacitance);
    SN_LIB_READ_DOUBLE_FIELD(max_capacitance);
    SN_LIB_READ_DOUBLE_FIELD(min_capacitance);
    SN_LIB_READ_DOUBLE_FIELD(max_transition);
    SN_LIB_READ_DOUBLE_FIELD(min_transition);
    SN_LIB_READ_DOUBLE_FIELD(max_fanout);
    SN_LIB_READ_DOUBLE_FIELD(fanout_load);
    SN_LIB_READ_DOUBLE_FIELD(min_pulse_width_high);
    SN_LIB_READ_DOUBLE_FIELD(min_pulse_width_low);
    SN_LIB_READ_DOUBLE_FIELD(min_period);
#undef SN_LIB_READ_DOUBLE_FIELD
    // Arcs and power groups of this group, appended contiguously.
    uint32_t timing_first = model->timings_count;
    sn_liberty_for_each_named(model->syntax, group, "timing", arc)
        sn_lib_read_timing(model, pin_id, arc);
    uint32_t power_first = model->powers_count;
    sn_liberty_for_each_named(model->syntax, group, "internal_power", power)
        sn_lib_read_power(model, pin_id, power);
    pin = &model->pins[pin_id];
    if (model->timings_count > timing_first)
    {
        pin->timing_first = timing_first;
        pin->timing_count = model->timings_count - timing_first;
    }
    if (model->powers_count > power_first)
    {
        pin->power_first = power_first;
        pin->power_count = model->powers_count - power_first;
    }
    if (model->malformed_count != malformed_before)
        pin->invalid = true;
}

// Formats a bus bit name from the library's bus_naming_style, which uses %s
// for the bus name and %d for the bit index in either order. Returns a
// malloc'd string, or NULL when the style has other conversions or lacks one
// of them; an allocation failure returns NULL and sets *out_of_memory.
static inline char* sn_lib_format_bit_name(const char* style, const char* bus, int32_t index, bool* out_of_memory)
{
    size_t length = 0;
    for (int pass = 0; pass < 2; pass++)
    {
        char* out = NULL;
        if (pass)
        {
            out = (char*)malloc(length + 1);
            if (!out)
            {
                *out_of_memory = true;
                return NULL;
            }
        }
        size_t at = 0;
        bool saw_name = false, saw_index = false;
        for (const char* c = style; *c; c++)
        {
            char piece[32];
            const char* text = piece;
            if (*c == '%' && c[1] == 's')
            {
                text = bus;
                saw_name = true;
                c++;
            }
            else if (*c == '%' && c[1] == 'd')
            {
                snprintf(piece, sizeof(piece), "%d", index);
                saw_index = true;
                c++;
            }
            else if (*c == '%')
            {
                free(out);
                return NULL;
            }
            else
            {
                piece[0] = *c;
                piece[1] = 0;
            }
            size_t n = strlen(text);
            if (out)
                memcpy(out + at, text, n);
            at += n;
        }
        if (!saw_name || !saw_index)
        {
            free(out);
            return NULL;
        }
        if (out)
        {
            out[at] = 0;
            return out;
        }
        length = at;
    }
    return NULL;
}

// Interprets a nested pin group name inside a bus: "A[3]" or "A[3:1]" over
// the bus's declared indices. Returns false when the name is not of that form.
// Interprets a nested pin group name inside a bus: "A[3]" or "A[3:1]" over
// the bus's declared indices. Returns 0 when the name is not of that form,
// 1 when it is, and 2 when it is but an index is not a bounded integer.
static inline int sn_lib_parse_bit_range(const char* text, const char* bus, int32_t* high, int32_t* low)
{
    size_t n = strlen(bus);
    if (strncmp(text, bus, n) != 0 || text[n] != '[')
        return 0;
    const char* pos = text + n + 1;
    const long limit = 1L << 20;
    char* stop = NULL;
    long first = strtol(pos, &stop, 10);
    if (stop == pos)
        return 0;
    long second = first;
    if (*stop == ':')
    {
        pos = stop + 1;
        second = strtol(pos, &stop, 10);
        if (stop == pos)
            return 0;
    }
    if (*stop != ']' || stop[1])
        return 0;
    if (first < -limit || first > limit || second < -limit || second > limit)
        return 2;
    *high = (int32_t)(first > second ? first : second);
    *low = (int32_t)(first > second ? second : first);
    return 1;
}

// strdup is POSIX, not C99, so the header carries its own copy.
static inline char* sn_lib_copy_string(const char* text)
{
    size_t length = strlen(text) + 1;
    char* copy = (char*)malloc(length);
    if (copy)
        memcpy(copy, text, length);
    return copy;
}

static inline uint32_t sn_lib_find_type(const sn_lib_t* model, uint32_t name)
{
    for (uint32_t i = 0; i < model->types_count; i++)
        if (model->types[i].name == name)
            return i;
    return SN_LIB_NONE;
}

static inline uint32_t sn_lib_add_pin(sn_lib_t* model, uint32_t cell, uint32_t name, sn_lib_pin_kind_t kind,
                                      bool in_test_cell)
{
    sn_lib_pin_t* pin = SN_LIB_PUSH(model, pins, sn_lib_pin_t);
    if (!pin)
        return SN_LIB_NONE;
    sn_lib_pin_init(pin, cell);
    pin->name = name;
    pin->kind = (uint32_t)kind;
    pin->in_test_cell = in_test_cell;
    return model->pins_count - 1;
}

// Reads pin, bus, bundle, and pg_pin groups of a cell or test_cell body.
static inline void sn_lib_read_pins(sn_lib_t* model, uint32_t cell, uint32_t body, bool in_test_cell)
{
    sn_liberty_t* syntax = model->syntax;
    sn_liberty_for_each_child(syntax, body, group)
    {
        if (sn_liberty_kind(syntax, group) != SN_LIBERTY_GROUP)
            continue;
        bool is_pin = sn_liberty_key_is(syntax, group, "pin");
        bool is_bus = sn_liberty_key_is(syntax, group, "bus");
        bool is_bundle = sn_liberty_key_is(syntax, group, "bundle");
        bool is_pg = sn_liberty_key_is(syntax, group, "pg_pin");
        if (!is_pin && !is_bus && !is_bundle && !is_pg)
            continue;
        uint32_t arg_count = sn_liberty_arg_count(syntax, group);
        // pin(A, B) declares several pins with the same attributes.
        for (uint32_t a = 0; a < (arg_count ? arg_count : 1); a++)
        {
            uint32_t name = sn_lib_intern(model, sn_liberty_arg(syntax, group, a));
            sn_lib_pin_kind_t kind = is_bus ? SN_LIB_PIN_BUS : is_bundle ? SN_LIB_PIN_BUNDLE
                                    : is_pg ? SN_LIB_PIN_PG : SN_LIB_PIN_SCALAR;
            uint32_t pin_id = sn_lib_add_pin(model, cell, name, kind, in_test_cell);
            if (pin_id == SN_LIB_NONE)
                return;
            sn_lib_read_pin_attributes(model, pin_id, group);
            if (!is_bus && !is_bundle)
                continue;

            // Expand the bits, inheriting the parent's attributes and arcs.
            // Interning moves the name pool, so the style and bus name are
            // copied out of it for the duration of the expansion.
            uint32_t bit_names_first = model->pins_count;
            char* style = sn_lib_copy_string(sn_lib_name(model, model->bus_naming_style));
            char* bus_name = sn_lib_copy_string(sn_lib_name(model, name));
            if (!style || !bus_name)
            {
                free(style);
                free(bus_name);
                model->out_of_memory = true;
                return;
            }
            if (is_bus)
            {
                uint32_t type_name = sn_lib_read_name(model, group, "bus_type");
                uint32_t type_id = sn_lib_find_type(model, type_name);
                model->pins[pin_id].bus_type = type_name;
                if (type_id == SN_LIB_NONE || model->types[type_id].invalid)
                {
                    sn_lib_warn(model, group, "bus \"%s\" has %s bus_type \"%s\"; its bits are not expanded",
                                bus_name, type_id == SN_LIB_NONE ? "unknown" : "an invalid",
                                sn_lib_name(model, type_name));
                    model->malformed_count++;
                    model->pins[pin_id].invalid = true;
                    free(style);
                    free(bus_name);
                    continue;
                }
                const sn_lib_type_t* type = &model->types[type_id];
                model->pins[pin_id].bus_from = type->bit_from;
                model->pins[pin_id].bus_to = type->bit_to;
                bool style_ok = true;
                for (uint32_t b = 0; b < type->bit_width; b++)
                {
                    int32_t index = type->downto ? type->bit_from - (int32_t)b : type->bit_from + (int32_t)b;
                    char* bit_name = style_ok ? sn_lib_format_bit_name(style, bus_name, index, &model->out_of_memory)
                                              : NULL;
                    if (!bit_name && style_ok && b == 0 && !model->out_of_memory)
                    {
                        sn_lib_warn(model, group, "bus_naming_style \"%s\" is not supported; using %%s[%%d]", style);
                        style_ok = false;
                    }
                    if (!bit_name && !model->out_of_memory)
                        bit_name = sn_lib_format_bit_name("%s[%d]", bus_name, index, &model->out_of_memory);
                    uint32_t bit_id = bit_name ? sn_lib_add_pin(model, cell, sn_lib_intern(model, bit_name),
                                                                SN_LIB_PIN_BIT, in_test_cell)
                                               : SN_LIB_NONE;
                    free(bit_name);
                    if (bit_id == SN_LIB_NONE)
                    {
                        model->out_of_memory = true;
                        free(style);
                        free(bus_name);
                        return;
                    }
                    sn_lib_pin_t copy = model->pins[pin_id];
                    copy.name = model->pins[bit_id].name;
                    copy.kind = SN_LIB_PIN_BIT;
                    copy.parent = pin_id;
                    copy.bit_index = b;
                    model->pins[bit_id] = copy;
                }
            }
            else
            {
                uint32_t members = sn_liberty_find(syntax, group, "members", SN_LIBERTY_INVALID);
                uint32_t member_count = members == SN_LIBERTY_INVALID ? 0 : sn_liberty_arg_count(syntax, members);
                if (!member_count)
                {
                    sn_lib_warn(model, group, "bundle \"%s\" has no members", bus_name);
                    model->malformed_count++;
                    model->pins[pin_id].invalid = true;
                }
                for (uint32_t m = 0; m < member_count; m++)
                {
                    uint32_t member_name = sn_lib_intern(model, sn_liberty_arg(syntax, members, m));
                    uint32_t bit_id = sn_lib_add_pin(model, cell, member_name, SN_LIB_PIN_BIT, in_test_cell);
                    if (bit_id == SN_LIB_NONE)
                    {
                        free(style);
                        free(bus_name);
                        return;
                    }
                    sn_lib_pin_t copy = model->pins[pin_id];
                    copy.name = member_name;
                    copy.kind = SN_LIB_PIN_BIT;
                    copy.parent = pin_id;
                    copy.bit_index = m;
                    model->pins[bit_id] = copy;
                }
            }
            // Nested pin groups override the attributes of individual bits,
            // named either as members ("A[2]" in the naming style) or, for
            // buses, as declared-index ranges ("A[3:1]").
            sn_liberty_for_each_named(syntax, group, "pin", bit_group)
            {
                uint32_t bit_args = sn_liberty_arg_count(syntax, bit_group);
                for (uint32_t a2 = 0; a2 < (bit_args ? bit_args : 1); a2++)
                {
                    const char* bit_text = sn_liberty_arg(syntax, bit_group, a2);
                    uint32_t bit_name = sn_lib_intern(model, bit_text);
                    uint32_t matched = 0;
                    int32_t high = 0, low = 0;
                    int range = is_bus ? sn_lib_parse_bit_range(bit_text, bus_name, &high, &low) : 0;
                    if (range == 2)
                    {
                        sn_lib_warn(model, bit_group, "pin \"%s\": index outside the representable range", bit_text);
                        model->malformed_count++;
                        model->pins[pin_id].invalid = true;
                        continue;
                    }
                    for (uint32_t p = bit_names_first; p < model->pins_count; p++)
                    {
                        if (model->pins[p].parent != pin_id)
                            continue;
                        bool hit = model->pins[p].name == bit_name;
                        if (!hit && range == 1)
                        {
                            const sn_lib_pin_t* bus_pin = &model->pins[pin_id];
                            int32_t index = bus_pin->bus_from > bus_pin->bus_to
                                                ? bus_pin->bus_from - (int32_t)model->pins[p].bit_index
                                                : bus_pin->bus_from + (int32_t)model->pins[p].bit_index;
                            hit = index >= low && index <= high;
                        }
                        if (!hit)
                            continue;
                        sn_lib_read_pin_attributes(model, p, bit_group);
                        matched++;
                    }
                    if (!matched)
                    {
                        sn_lib_warn(model, bit_group, "pin \"%s\" is not a bit of \"%s\"", bit_text, bus_name);
                        model->malformed_count++;
                        model->pins[pin_id].invalid = true;
                    }
                }
            }
            free(style);
            free(bus_name);
        }
    }
}

// ---------------------------------------------------------------------------
// Sequential groups

static inline void sn_lib_read_state(sn_lib_t* model, uint32_t cell, uint32_t group, bool is_latch, bool is_bank,
                                     bool in_test_cell)
{
    sn_lib_state_t* state = SN_LIB_PUSH(model, states, sn_lib_state_t);
    if (!state)
        return;
    uint32_t id = model->states_count - 1;
    sn_liberty_t* syntax = model->syntax;
    state->cell = cell;
    state->is_latch = is_latch;
    state->in_test_cell = in_test_cell;
    state->item = group;
    state->var1 = sn_lib_intern(model, sn_liberty_arg(syntax, group, 0));
    state->var2 = sn_liberty_arg_count(syntax, group) > 1 ? sn_lib_intern(model, sn_liberty_arg(syntax, group, 1))
                                                          : SN_LIB_NONE;
    state->bits = 1;
    uint32_t malformed_before = model->malformed_count;
    if (is_bank)
    {
        const char* bits = sn_liberty_arg_count(syntax, group) > 2 ? sn_liberty_arg(syntax, group, 2) : "";
        long width = 0;
        if (sn_lib_parse_int(bits, 1, 65536, &width))
            state->bits = (uint32_t)width;
        else
        {
            sn_lib_warn(model, group, "bank width must be an integer in [1, 65536], not \"%s\"", bits);
            model->malformed_count++;
            state->bits = 0;
        }
    }
    uint32_t next_state = sn_lib_read_expr(model, group, is_latch ? "data_in" : "next_state");
    uint32_t clocked_on = sn_lib_read_expr(model, group, is_latch ? "enable" : "clocked_on");
    uint32_t clocked_on_also = sn_lib_read_expr(model, group, is_latch ? "enable_also" : "clocked_on_also");
    uint32_t clear = sn_lib_read_expr(model, group, "clear");
    uint32_t preset = sn_lib_read_expr(model, group, "preset");
    uint32_t power_down = sn_lib_read_expr(model, group, "power_down_function");
    state = &model->states[id];
    state->next_state = next_state;
    state->clocked_on = clocked_on;
    state->clocked_on_also = clocked_on_also;
    state->clear = clear;
    state->preset = preset;
    state->power_down_function = power_down;
    state->collision_var1 = sn_lib_read_collision(model, group, "clear_preset_var1");
    state->collision_var2 = sn_lib_read_collision(model, group, "clear_preset_var2");
    if (!is_latch && clocked_on == SN_LIB_NONE)
    {
        sn_lib_warn(model, group, "ff group without clocked_on");
        model->malformed_count++;
    }
    state = &model->states[id];
    state->invalid = model->malformed_count != malformed_before;
}

static inline void sn_lib_read_statetable(sn_lib_t* model, uint32_t cell, uint32_t group)
{
    sn_lib_statetable_t* table = SN_LIB_PUSH(model, statetables, sn_lib_statetable_t);
    if (!table)
        return;
    sn_liberty_t* syntax = model->syntax;
    table->cell = cell;
    table->item = group;
    table->inputs = sn_lib_intern(model, sn_liberty_arg(syntax, group, 0));
    table->outputs = sn_liberty_arg_count(syntax, group) > 1 ? sn_lib_intern(model, sn_liberty_arg(syntax, group, 1))
                                                             : SN_LIB_NONE;
    table->table = sn_lib_read_name(model, group, "table");
    if (table->table == SN_LIB_NONE)
        sn_lib_warn(model, group, "statetable without a table");
}

static inline void sn_lib_read_sequential(sn_lib_t* model, uint32_t cell, uint32_t body, bool in_test_cell)
{
    sn_liberty_t* syntax = model->syntax;
    sn_liberty_for_each_child(syntax, body, group)
    {
        if (sn_liberty_kind(syntax, group) != SN_LIBERTY_GROUP)
            continue;
        if (sn_liberty_key_is(syntax, group, "ff"))
            sn_lib_read_state(model, cell, group, false, false, in_test_cell);
        else if (sn_liberty_key_is(syntax, group, "ff_bank"))
            sn_lib_read_state(model, cell, group, false, true, in_test_cell);
        else if (sn_liberty_key_is(syntax, group, "latch"))
            sn_lib_read_state(model, cell, group, true, false, in_test_cell);
        else if (sn_liberty_key_is(syntax, group, "latch_bank"))
            sn_lib_read_state(model, cell, group, true, true, in_test_cell);
        else if (sn_liberty_key_is(syntax, group, "statetable") && !in_test_cell)
            sn_lib_read_statetable(model, cell, group);
    }
}

// ---------------------------------------------------------------------------
// Cells

static inline void sn_lib_read_cell(sn_lib_t* model, uint32_t group)
{
    sn_lib_cell_t* cell = SN_LIB_PUSH(model, cells, sn_lib_cell_t);
    if (!cell)
        return;
    uint32_t id = model->cells_count - 1;
    sn_liberty_t* syntax = model->syntax;
    cell->name = sn_lib_intern(model, sn_liberty_name(syntax, group));
    cell->item = group;
    cell->test_cell_item = SN_LIB_NONE;
    uint32_t malformed_before = model->malformed_count;
    cell->footprint = sn_lib_read_name(model, group, "cell_footprint");
    cell->area = sn_lib_read_double(model, group, "area");
    cell->cell_leakage_power = sn_lib_read_double(model, group, "cell_leakage_power");
    cell->dont_use = sn_lib_read_bool(model, group, "dont_use", false);
    cell->dont_touch = sn_lib_read_bool(model, group, "dont_touch", false);
    cell->is_macro = sn_lib_read_bool(model, group, "is_macro_cell", false);
    cell->is_pad = sn_lib_read_bool(model, group, "pad_cell", false);
    cell->clock_gating_integrated_cell = sn_lib_read_name(model, group, "clock_gating_integrated_cell");
    cell->clock_gating_integrated = cell->clock_gating_integrated_cell != SN_LIB_NONE;
    uint32_t test_cell = sn_liberty_find(syntax, group, "test_cell", SN_LIBERTY_INVALID);

    uint32_t pin_first = model->pins_count;
    sn_lib_read_pins(model, id, group, false);
    if (test_cell != SN_LIBERTY_INVALID)
        sn_lib_read_pins(model, id, test_cell, true);
    uint32_t state_first = model->states_count;
    uint32_t statetable_first = model->statetables_count;
    sn_lib_read_sequential(model, id, group, false);
    if (test_cell != SN_LIBERTY_INVALID)
        sn_lib_read_sequential(model, id, test_cell, true);
    uint32_t leakage_first = model->leakages_count;
    sn_liberty_for_each_named(syntax, group, "leakage_power", leak)
    {
        sn_lib_leakage_t* entry = SN_LIB_PUSH(model, leakages, sn_lib_leakage_t);
        if (!entry)
            break;
        uint32_t leak_id = model->leakages_count - 1;
        entry->cell = id;
        entry->item = leak;
        entry->related_pg_pin = sn_lib_read_name(model, leak, "related_pg_pin");
        entry->value = sn_lib_read_double(model, leak, "value");
        uint32_t when = sn_lib_read_expr(model, leak, "when");
        model->leakages[leak_id].when = when;
    }
    cell = &model->cells[id];
    cell->test_cell_item = test_cell == SN_LIBERTY_INVALID ? SN_LIB_NONE : test_cell;
    cell->pin_first = pin_first;
    cell->pin_count = model->pins_count - pin_first;
    cell->state_first = state_first;
    cell->state_count = model->states_count - state_first;
    cell->statetable_first = statetable_first;
    cell->statetable_count = model->statetables_count - statetable_first;
    cell->leakage_first = leakage_first;
    cell->leakage_count = model->leakages_count - leakage_first;
    cell->invalid = model->malformed_count != malformed_before;
    if (cell->invalid)
        model->invalid_cells++;
}

// ---------------------------------------------------------------------------
// Library-level groups

// Reads a bus type. Sizes must be integral and bounded, and the declared
// range must agree with the width and direction; otherwise the type is
// marked invalid and buses using it are not expanded.
static inline void sn_lib_read_type(sn_lib_t* model, uint32_t group)
{
    sn_lib_type_t* type = SN_LIB_PUSH(model, types, sn_lib_type_t);
    if (!type)
        return;
    type->name = sn_lib_intern(model, sn_liberty_name(model->syntax, group));
    type->item = group;
    const long limit = 1L << 20;
    long width = 0, from = 0, to = 0;
    bool has_width = sn_lib_read_int(model, group, "bit_width", 1, 65536, &width);
    bool has_from = sn_lib_read_int(model, group, "bit_from", -limit, limit, &from);
    bool has_to = sn_lib_read_int(model, group, "bit_to", -limit, limit, &to);
    bool bad = (!has_width && sn_liberty_attribute(model->syntax, group, "bit_width")) ||
               (!has_from && sn_liberty_attribute(model->syntax, group, "bit_from")) ||
               (!has_to && sn_liberty_attribute(model->syntax, group, "bit_to"));
    bool has_downto = sn_liberty_attribute(model->syntax, group, "downto") != NULL;
    uint32_t malformed_before = model->malformed_count;
    type->downto = sn_lib_read_bool(model, group, "downto", has_from && has_to && from > to);
    bad = bad || model->malformed_count != malformed_before;
    if (!bad && has_from != has_to)
    {
        sn_lib_warn(model, group, "type \"%s\" declares only one of bit_from and bit_to", sn_lib_name(model, type->name));
        bad = true;
    }
    if (!bad && !has_width && !has_from)
    {
        sn_lib_warn(model, group, "type \"%s\" has no bit_width or bit range", sn_lib_name(model, type->name));
        bad = true;
    }
    if (!bad && has_from)
    {
        long span = (from > to ? from - to : to - from) + 1;
        if (has_width && span != width)
        {
            sn_lib_warn(model, group, "type \"%s\": bit_width %ld disagrees with bit_from/bit_to",
                        sn_lib_name(model, type->name), width);
            bad = true;
        }
        else if (has_downto && from != to && type->downto != (from > to))
        {
            sn_lib_warn(model, group, "type \"%s\": downto disagrees with bit_from/bit_to",
                        sn_lib_name(model, type->name));
            bad = true;
        }
        else if (span > 65536)
        {
            sn_lib_warn(model, group, "type \"%s\": range wider than 65536 bits", sn_lib_name(model, type->name));
            bad = true;
        }
        else
        {
            type->bit_from = (int32_t)from;
            type->bit_to = (int32_t)to;
            type->bit_width = (uint32_t)span;
        }
    }
    else if (!bad)
    {
        // Only the width is known: number the bits from zero upward.
        type->bit_width = (uint32_t)width;
        type->bit_from = type->downto ? (int32_t)type->bit_width - 1 : 0;
        type->bit_to = type->downto ? 0 : (int32_t)type->bit_width - 1;
    }
    if (bad)
    {
        type->invalid = true;
        type->bit_width = 0;
        model->malformed_count = malformed_before + 1;
    }
}

static inline void sn_lib_read_library_header(sn_lib_t* model, uint32_t library)
{
    sn_liberty_t* syntax = model->syntax;
    model->name = sn_lib_intern(model, sn_liberty_name(syntax, library));
    uint32_t technology = sn_liberty_find(syntax, library, "technology", SN_LIBERTY_INVALID);
    model->technology = technology == SN_LIBERTY_INVALID ? SN_LIB_NONE
                                                          : sn_lib_intern(model, sn_liberty_arg(syntax, technology, 0));
    model->delay_model = sn_lib_read_name(model, library, "delay_model");
    model->bus_naming_style = sn_lib_read_name(model, library, "bus_naming_style");
    if (model->bus_naming_style == SN_LIB_NONE)
        model->bus_naming_style = sn_lib_intern(model, "%s[%d]");
    model->time_unit = sn_lib_read_name(model, library, "time_unit");
    model->voltage_unit = sn_lib_read_name(model, library, "voltage_unit");
    model->current_unit = sn_lib_read_name(model, library, "current_unit");
    model->leakage_power_unit = sn_lib_read_name(model, library, "leakage_power_unit");
    model->pulling_resistance_unit = sn_lib_read_name(model, library, "pulling_resistance_unit");
    model->capacitive_load_unit = NAN;
    model->capacitive_load_unit_name = SN_LIB_NONE;
    uint32_t load = sn_liberty_find(syntax, library, "capacitive_load_unit", SN_LIBERTY_INVALID);
    if (load != SN_LIBERTY_INVALID && sn_liberty_arg_count(syntax, load) >= 2)
    {
        model->capacitive_load_unit = strtod(sn_liberty_arg(syntax, load, 0), NULL);
        model->capacitive_load_unit_name = sn_lib_intern(model, sn_liberty_arg(syntax, load, 1));
    }
    model->nom_process = sn_lib_read_double(model, library, "nom_process");
    model->nom_temperature = sn_lib_read_double(model, library, "nom_temperature");
    model->nom_voltage = sn_lib_read_double(model, library, "nom_voltage");
    model->default_operating_conditions = sn_lib_read_name(model, library, "default_operating_conditions");

    sn_liberty_for_each_child(syntax, library, item)
    {
        sn_liberty_kind_t kind = sn_liberty_kind(syntax, item);
        if (kind == SN_LIBERTY_ATTRIBUTE && strncmp(syntax->text + syntax->items[item].key.begin, "default_", 8) == 0)
        {
            const char* text = sn_liberty_value(syntax, item);
            char* stop = NULL;
            double value = strtod(text, &stop);
            if (stop != text)
            {
                sn_lib_named_value_t* entry = SN_LIB_PUSH(model, defaults, sn_lib_named_value_t);
                if (entry)
                {
                    entry->name = sn_lib_intern(model, sn_liberty_key(syntax, item));
                    entry->value = value;
                }
            }
        }
        else if (kind == SN_LIBERTY_COMPLEX && sn_liberty_key_is(syntax, item, "voltage_map"))
        {
            sn_lib_named_value_t* entry = SN_LIB_PUSH(model, voltage_map, sn_lib_named_value_t);
            if (entry)
            {
                entry->name = sn_lib_intern(model, sn_liberty_arg(syntax, item, 0));
                entry->value = strtod(sn_liberty_arg(syntax, item, 1), NULL);
            }
        }
        else if (kind == SN_LIBERTY_COMPLEX && sn_liberty_key_is(syntax, item, "define"))
        {
            sn_lib_define_t* entry = SN_LIB_PUSH(model, defines, sn_lib_define_t);
            if (entry)
            {
                entry->attribute = sn_lib_intern(model, sn_liberty_arg(syntax, item, 0));
                entry->group = sn_lib_intern(model, sn_liberty_arg(syntax, item, 1));
                entry->type = sn_lib_intern(model, sn_liberty_arg(syntax, item, 2));
            }
        }
        else if (kind == SN_LIBERTY_GROUP)
        {
            const char* key = sn_liberty_key(syntax, item);
            size_t length = strlen(key);
            if (length > 9 && strcmp(key + length - 9, "_template") == 0)
                sn_lib_read_template(model, item);
            else if (strcmp(key, "type") == 0)
                sn_lib_read_type(model, item);
            else if (strcmp(key, "operating_conditions") == 0)
            {
                sn_lib_operating_conditions_t* c = SN_LIB_PUSH(model, conditions, sn_lib_operating_conditions_t);
                if (c)
                {
                    c->name = sn_lib_intern(model, sn_liberty_name(syntax, item));
                    c->item = item;
                    c->process = sn_lib_read_double(model, item, "process");
                    c->temperature = sn_lib_read_double(model, item, "temperature");
                    c->voltage = sn_lib_read_double(model, item, "voltage");
                    c->tree_type = sn_lib_read_name(model, item, "tree_type");
                }
            }
            else if (strcmp(key, "wire_load") == 0)
            {
                sn_lib_wire_load_t* w = SN_LIB_PUSH(model, wire_loads, sn_lib_wire_load_t);
                if (w)
                {
                    uint32_t wid = model->wire_loads_count - 1;
                    w->name = sn_lib_intern(model, sn_liberty_name(syntax, item));
                    w->item = item;
                    w->resistance = sn_lib_read_double(model, item, "resistance");
                    w->capacitance = sn_lib_read_double(model, item, "capacitance");
                    w->area = sn_lib_read_double(model, item, "area");
                    w->slope = sn_lib_read_double(model, item, "slope");
                    uint32_t first = model->doubles_count;
                    sn_liberty_for_each_named(syntax, item, "fanout_length", pair)
                    {
                        sn_lib_push_double(model, strtod(sn_liberty_arg(syntax, pair, 0), NULL));
                        sn_lib_push_double(model, strtod(sn_liberty_arg(syntax, pair, 1), NULL));
                    }
                    w = &model->wire_loads[wid];
                    w->fanout_length_offset = first;
                    w->fanout_length_count = (model->doubles_count - first) / 2;
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Model construction, lookup, and destruction

static inline void sn_lib_destroy(sn_lib_t* model)
{
    if (!model)
        return;
    sn_liberty_destroy(model->syntax);
    free(model->path);
    free(model->error);
    for (uint32_t i = 0; i < model->warnings_count; i++)
        free(model->warnings[i]);
    free(model->warnings);
    free(model->names);
    free(model->name_buckets);
    free(model->doubles);
    if (model->exprs)
        for (uint32_t i = 0; i < model->exprs_count; i++)
            sn_liberty_expr_destroy(&model->exprs[i]);
    free(model->exprs);
    free(model->defaults);
    free(model->voltage_map);
    free(model->defines);
    free(model->templates);
    free(model->conditions);
    free(model->wire_loads);
    free(model->types);
    free(model->cells);
    free(model->cell_buckets);
    free(model->pins);
    free(model->states);
    free(model->statetables);
    free(model->timings);
    free(model->powers);
    free(model->leakages);
    free(model->tables);
    free(model);
}

static inline void sn_lib_index_cells(sn_lib_t* model)
{
    uint32_t count = 64;
    while (count < model->cells_count * 2)
        count *= 2;
    model->cell_buckets = (uint32_t*)malloc(count * sizeof(uint32_t));
    if (!model->cell_buckets)
    {
        model->out_of_memory = true;
        return;
    }
    memset(model->cell_buckets, 0xff, count * sizeof(uint32_t));
    model->cell_bucket_count = count;
    for (uint32_t i = 0; i < model->cells_count; i++)
    {
        const char* name = sn_lib_name(model, model->cells[i].name);
        uint32_t b = (uint32_t)(sn_lib_hash_string(name, strlen(name)) & (count - 1));
        while (model->cell_buckets[b] != SN_LIB_NONE)
        {
            if (strcmp(sn_lib_name(model, model->cells[model->cell_buckets[b]].name), name) == 0)
                sn_lib_warn(model, model->cells[i].item, "duplicate cell \"%s\"", name);
            b = (b + 1) & (count - 1);
        }
        model->cell_buckets[b] = i;
    }
}

static inline bool sn_lib_ok(const sn_lib_t* model)
{
    return model && !model->error && !model->out_of_memory;
}

// Builds the model from a parsed library, taking ownership of the syntax tree
// (also on failure). Returns NULL when given NULL or when the model itself
// cannot be allocated; otherwise check sn_lib_ok(): ->error names a fatal
// problem, ->out_of_memory an incomplete model, and ->warnings the rest.
static inline sn_lib_t* sn_lib_from_liberty(sn_liberty_t* syntax)
{
    if (!syntax)
        return NULL;
    sn_lib_t* model = (sn_lib_t*)calloc(1, sizeof(sn_lib_t));
    if (!model)
    {
        sn_liberty_destroy(syntax);
        return NULL;
    }
    model->syntax = syntax;
    model->path = sn_lib_copy_string(syntax->path ? syntax->path : "?");
    if (!model->path)
        model->out_of_memory = true; // messages would otherwise silently lose their file name
    model->source_size = syntax->size;
    model->source_hash = syntax->source_hash;
    model->name = model->technology = model->delay_model = SN_LIB_NONE;
    model->time_unit = model->voltage_unit = model->current_unit = SN_LIB_NONE;
    model->leakage_power_unit = model->pulling_resistance_unit = SN_LIB_NONE;
    model->default_operating_conditions = SN_LIB_NONE;
    model->nom_process = model->nom_temperature = model->nom_voltage = NAN;
    if (!sn_liberty_ok(syntax))
    {
        const char* message = syntax->error ? syntax->error : "out of memory while parsing";
        model->error = (char*)malloc(strlen(message) + 1);
        if (model->error)
            strcpy(model->error, message);
        else
            model->out_of_memory = true;
        return model;
    }
    uint32_t library = sn_liberty_find(syntax, sn_liberty_root(syntax), "library", SN_LIBERTY_INVALID);
    if (library == SN_LIBERTY_INVALID)
    {
        const char* message = "no library group found";
        const char* path = syntax->path ? syntax->path : "?";
        model->error = (char*)malloc(strlen(path) + strlen(message) + 8);
        if (model->error)
            sprintf(model->error, "%s: %s", path, message);
        else
            model->out_of_memory = true; // the failure must not read as success
        return model;
    }
    if (sn_liberty_find(syntax, sn_liberty_root(syntax), "library", library) != SN_LIBERTY_INVALID)
        sn_lib_warn(model, library, "file holds several library groups; only the first is modeled");
    sn_lib_read_library_header(model, library);
    sn_liberty_for_each_named(syntax, library, "cell", cell)
        sn_lib_read_cell(model, cell);
    sn_lib_index_cells(model);
    // The syntax accessors report their own allocation failures lazily.
    if (!sn_liberty_ok(syntax))
        model->out_of_memory = true;
    return model;
}

static inline sn_lib_t* sn_lib_load(const char* path)
{
    sn_liberty_t* syntax = sn_liberty_read_file(path);
    if (!syntax)
        return NULL;
    return sn_lib_from_liberty(syntax);
}

static inline uint32_t sn_lib_find_cell(const sn_lib_t* model, const char* name)
{
    if (!model->cell_bucket_count)
        return SN_LIB_NONE;
    uint32_t b = (uint32_t)(sn_lib_hash_string(name, strlen(name)) & (model->cell_bucket_count - 1));
    for (uint32_t probe = 0; probe < model->cell_bucket_count; probe++)
    {
        uint32_t id = model->cell_buckets[(b + probe) & (model->cell_bucket_count - 1)];
        if (id == SN_LIB_NONE)
            return SN_LIB_NONE;
        if (strcmp(sn_lib_name(model, model->cells[id].name), name) == 0)
            return id;
    }
    return SN_LIB_NONE;
}

// Finds a pin of a cell by name, including bus bits (A[3]) and bundle members.
static inline uint32_t sn_lib_find_pin(const sn_lib_t* model, uint32_t cell, const char* name)
{
    const sn_lib_cell_t* c = &model->cells[cell];
    for (uint32_t p = c->pin_first; p < c->pin_first + c->pin_count; p++)
        if (!model->pins[p].in_test_cell && strcmp(sn_lib_name(model, model->pins[p].name), name) == 0)
            return p;
    return SN_LIB_NONE;
}

static inline const char* sn_lib_timing_type_name(const sn_lib_t* model, const sn_lib_timing_t* arc)
{
    if (arc->timing_type == SN_LIB_TIMING_OTHER)
        return sn_lib_name(model, arc->timing_type_name);
    return sn_lib_timing_type_names[arc->timing_type];
}

// The number of cells that are usable for mapping: not dont_use, with at
// least one output whose function is known or that is sequential.
static inline bool sn_lib_cell_is_sequential(const sn_lib_t* model, uint32_t cell)
{
    const sn_lib_cell_t* c = &model->cells[cell];
    for (uint32_t s = c->state_first; s < c->state_first + c->state_count; s++)
        if (!model->states[s].in_test_cell)
            return true;
    return c->statetable_count != 0;
}


// ===========================================================================
// Binary model files
//
// A parsed model can be written to a compact binary file and read back many
// times without re-parsing the library text. The file holds the model only:
// the string pool, the number pool, every record array, the expressions, the
// warnings, and the identity (size and hash) of the text the model came from.
// It does not hold the syntax tree, so a model loaded from a binary file has
// syntax == NULL and every item id equal to SN_LIB_NONE; attributes the model
// does not interpret are unavailable from it.
//
// A functional-only file drops timing arcs, power groups, leakage entries,
// lookup tables, templates, and the numbers they reference, keeping the
// interfaces, functions, sequential groups, and area; it is a small fraction
// of the full file and is what an interface or function consumer needs.
//
// Integers are little-endian; doubles are their IEEE bit patterns. Every
// array is a count followed by its records, written field by field, so the
// layout does not depend on struct padding. The file ends with a hash of its
// payload, checked before decoding, and the reader validates every cross
// reference before returning a model that sn_lib_ok() accepts.

#define SN_LIB_BINARY_MAGIC "SNLIBBIN"
#define SN_LIB_BINARY_VERSION 1u
#define SN_LIB_BINARY_FUNCTIONAL_ONLY 1u

typedef struct sn_lib_binary_options_t
{
    bool functional_only;
} sn_lib_binary_options_t;

// One codec serves both directions so the field order cannot diverge.
typedef struct sn_lib_codec_t
{
    bool writing;
    bool failed;
    uint8_t* buffer; // write mode: the encoded payload, hashed and written at the end
    size_t buffer_size, buffer_cap;
    const uint8_t* data; // read mode: the file contents
    size_t size;
    size_t pos;
    bool out_of_memory;
} sn_lib_codec_t;

static inline void sn_lib_codec_bytes(sn_lib_codec_t* codec, void* bytes, size_t count)
{
    if (codec->failed)
        return;
    if (codec->writing)
    {
        if (count > codec->buffer_cap - codec->buffer_size)
        {
            size_t cap = codec->buffer_cap ? codec->buffer_cap : 1u << 16;
            while (cap - codec->buffer_size < count)
                cap *= 2;
            uint8_t* grown = (uint8_t*)realloc(codec->buffer, cap);
            if (!grown)
            {
                codec->out_of_memory = true;
                codec->failed = true;
                return;
            }
            codec->buffer = grown;
            codec->buffer_cap = cap;
        }
        memcpy(codec->buffer + codec->buffer_size, bytes, count);
        codec->buffer_size += count;
        return;
    }
    if (count > codec->size - codec->pos)
    {
        codec->failed = true;
        memset(bytes, 0, count);
        return;
    }
    memcpy(bytes, codec->data + codec->pos, count);
    codec->pos += count;
}

static inline void sn_lib_codec_u64(sn_lib_codec_t* codec, uint64_t* value)
{
    uint8_t bytes[8];
    if (codec->writing)
        for (int i = 0; i < 8; i++)
            bytes[i] = (uint8_t)(*value >> (8 * i));
    sn_lib_codec_bytes(codec, bytes, 8);
    if (!codec->writing)
    {
        *value = 0;
        for (int i = 0; i < 8; i++)
            *value |= (uint64_t)bytes[i] << (8 * i);
    }
}

static inline void sn_lib_codec_u32(sn_lib_codec_t* codec, uint32_t* value)
{
    uint8_t bytes[4];
    if (codec->writing)
        for (int i = 0; i < 4; i++)
            bytes[i] = (uint8_t)(*value >> (8 * i));
    sn_lib_codec_bytes(codec, bytes, 4);
    if (!codec->writing)
    {
        *value = 0;
        for (int i = 0; i < 4; i++)
            *value |= (uint32_t)bytes[i] << (8 * i);
    }
}

static inline void sn_lib_codec_i32(sn_lib_codec_t* codec, int32_t* value)
{
    uint32_t bits = (uint32_t)*value;
    sn_lib_codec_u32(codec, &bits);
    *value = (int32_t)bits;
}

static inline void sn_lib_codec_bool(sn_lib_codec_t* codec, bool* value)
{
    uint8_t byte = *value ? 1 : 0;
    sn_lib_codec_bytes(codec, &byte, 1);
    if (byte > 1)
        codec->failed = true;
    *value = byte != 0;
}

static inline void sn_lib_codec_f64(sn_lib_codec_t* codec, double* value)
{
    uint64_t bits;
    memcpy(&bits, value, 8);
    sn_lib_codec_u64(codec, &bits);
    memcpy(value, &bits, 8);
}

static inline void sn_lib_codec_u32_array(sn_lib_codec_t* codec, uint32_t* values, uint32_t count)
{
    for (uint32_t i = 0; i < count && !codec->failed; i++)
        sn_lib_codec_u32(codec, &values[i]);
}

// A counted array of fixed-size records. When reading, the array is
// allocated with exactly the count read; a count that cannot fit in the
// remaining bytes is rejected before allocating.
static inline bool sn_lib_codec_array(sn_lib_codec_t* codec, void** array, uint32_t* count, uint32_t* cap,
                                      size_t element_size, size_t minimum_encoded_size)
{
    sn_lib_codec_u32(codec, count);
    if (codec->failed)
        return false;
    if (codec->writing)
        return true;
    if ((uint64_t)*count * minimum_encoded_size > codec->size - codec->pos)
    {
        codec->failed = true;
        return false;
    }
    *array = NULL;
    *cap = 0;
    if (*count)
    {
        *array = calloc(*count, element_size);
        if (!*array)
        {
            *count = 0; // destroy must not walk an array that was never allocated
            codec->out_of_memory = true;
            codec->failed = true;
            return false;
        }
        *cap = *count;
    }
    return true;
}

// A NUL-terminated string: length and bytes. When reading, a fresh copy.
static inline void sn_lib_codec_string(sn_lib_codec_t* codec, char** text)
{
    uint32_t length = codec->writing && *text ? (uint32_t)strlen(*text) : 0;
    sn_lib_codec_u32(codec, &length);
    if (codec->failed)
        return;
    if (codec->writing)
    {
        if (length)
            sn_lib_codec_bytes(codec, *text, length);
        return;
    }
    if (length > codec->size - codec->pos)
    {
        codec->failed = true;
        return;
    }
    *text = (char*)malloc((size_t)length + 1);
    if (!*text)
    {
        codec->out_of_memory = true;
        codec->failed = true;
        return;
    }
    sn_lib_codec_bytes(codec, *text, length);
    (*text)[length] = 0;
}

// Item ids are meaningless without the syntax tree and are never stored.
static inline void sn_lib_codec_item(sn_lib_codec_t* codec, uint32_t* item)
{
    if (!codec->writing)
        *item = SN_LIB_NONE;
}

static inline void sn_lib_codec_template(sn_lib_codec_t* codec, sn_lib_template_t* t)
{
    sn_lib_codec_u32(codec, &t->name);
    sn_lib_codec_u32(codec, &t->kind);
    sn_lib_codec_bool(codec, &t->invalid);
    sn_lib_codec_u32(codec, &t->dims);
    sn_lib_codec_u32_array(codec, t->variable, 3);
    sn_lib_codec_u32_array(codec, t->index_offset, 3);
    sn_lib_codec_u32_array(codec, t->index_count, 3);
    sn_lib_codec_item(codec, &t->item);
}

static inline void sn_lib_codec_table(sn_lib_codec_t* codec, sn_lib_table_t* t)
{
    sn_lib_codec_u32(codec, &t->template_id);
    sn_lib_codec_bool(codec, &t->invalid);
    sn_lib_codec_u32(codec, &t->dims);
    sn_lib_codec_u32_array(codec, t->index_offset, 3);
    sn_lib_codec_u32_array(codec, t->index_count, 3);
    sn_lib_codec_u32(codec, &t->values_offset);
    sn_lib_codec_u32(codec, &t->values_count);
    sn_lib_codec_item(codec, &t->item);
}

static inline void sn_lib_codec_timing(sn_lib_codec_t* codec, sn_lib_timing_t* arc)
{
    sn_lib_codec_u32(codec, &arc->pin);
    sn_lib_codec_u32(codec, &arc->related_pin);
    sn_lib_codec_u32(codec, &arc->related_bus_pins);
    sn_lib_codec_u32(codec, &arc->related_output_pin);
    sn_lib_codec_u32(codec, &arc->timing_type);
    sn_lib_codec_u32(codec, &arc->timing_type_name);
    sn_lib_codec_u32(codec, &arc->sense);
    sn_lib_codec_u32(codec, &arc->when);
    sn_lib_codec_u32(codec, &arc->sdf_cond);
    sn_lib_codec_u32(codec, &arc->cell_rise);
    sn_lib_codec_u32(codec, &arc->cell_fall);
    sn_lib_codec_u32(codec, &arc->rise_transition);
    sn_lib_codec_u32(codec, &arc->fall_transition);
    sn_lib_codec_u32(codec, &arc->rise_constraint);
    sn_lib_codec_u32(codec, &arc->fall_constraint);
    sn_lib_codec_f64(codec, &arc->intrinsic_rise);
    sn_lib_codec_f64(codec, &arc->intrinsic_fall);
    sn_lib_codec_f64(codec, &arc->rise_resistance);
    sn_lib_codec_f64(codec, &arc->fall_resistance);
    sn_lib_codec_item(codec, &arc->item);
}

static inline void sn_lib_codec_power(sn_lib_codec_t* codec, sn_lib_power_t* power)
{
    sn_lib_codec_u32(codec, &power->pin);
    sn_lib_codec_u32(codec, &power->related_pin);
    sn_lib_codec_u32(codec, &power->related_pg_pin);
    sn_lib_codec_u32(codec, &power->when);
    sn_lib_codec_u32(codec, &power->rise_power);
    sn_lib_codec_u32(codec, &power->fall_power);
    sn_lib_codec_u32(codec, &power->power);
    sn_lib_codec_item(codec, &power->item);
}

static inline void sn_lib_codec_leakage(sn_lib_codec_t* codec, sn_lib_leakage_t* leak)
{
    sn_lib_codec_u32(codec, &leak->cell);
    sn_lib_codec_u32(codec, &leak->when);
    sn_lib_codec_u32(codec, &leak->related_pg_pin);
    sn_lib_codec_f64(codec, &leak->value);
    sn_lib_codec_item(codec, &leak->item);
}

static inline void sn_lib_codec_pin(sn_lib_codec_t* codec, sn_lib_pin_t* pin)
{
    sn_lib_codec_u32(codec, &pin->name);
    sn_lib_codec_u32(codec, &pin->cell);
    sn_lib_codec_u32(codec, &pin->kind);
    sn_lib_codec_u32(codec, &pin->direction);
    sn_lib_codec_bool(codec, &pin->in_test_cell);
    sn_lib_codec_bool(codec, &pin->invalid);
    sn_lib_codec_bool(codec, &pin->clock);
    sn_lib_codec_bool(codec, &pin->is_pad);
    sn_lib_codec_u32(codec, &pin->parent);
    sn_lib_codec_u32(codec, &pin->bus_type);
    sn_lib_codec_i32(codec, &pin->bus_from);
    sn_lib_codec_i32(codec, &pin->bus_to);
    sn_lib_codec_u32(codec, &pin->bit_index);
    sn_lib_codec_u32(codec, &pin->function);
    sn_lib_codec_u32(codec, &pin->three_state);
    sn_lib_codec_u32(codec, &pin->state_function);
    sn_lib_codec_u32(codec, &pin->x_function);
    sn_lib_codec_u32(codec, &pin->power_down_function);
    sn_lib_codec_u32(codec, &pin->internal_node);
    sn_lib_codec_u32(codec, &pin->nextstate_type);
    sn_lib_codec_u32(codec, &pin->signal_type);
    sn_lib_codec_u32(codec, &pin->pin_func_type);
    sn_lib_codec_f64(codec, &pin->capacitance);
    sn_lib_codec_f64(codec, &pin->rise_capacitance);
    sn_lib_codec_f64(codec, &pin->fall_capacitance);
    sn_lib_codec_f64(codec, &pin->max_capacitance);
    sn_lib_codec_f64(codec, &pin->min_capacitance);
    sn_lib_codec_f64(codec, &pin->max_transition);
    sn_lib_codec_f64(codec, &pin->min_transition);
    sn_lib_codec_f64(codec, &pin->max_fanout);
    sn_lib_codec_f64(codec, &pin->fanout_load);
    sn_lib_codec_f64(codec, &pin->min_pulse_width_high);
    sn_lib_codec_f64(codec, &pin->min_pulse_width_low);
    sn_lib_codec_f64(codec, &pin->min_period);
    sn_lib_codec_u32(codec, &pin->related_power_pin);
    sn_lib_codec_u32(codec, &pin->related_ground_pin);
    sn_lib_codec_u32(codec, &pin->pg_type);
    sn_lib_codec_u32(codec, &pin->voltage_name);
    sn_lib_codec_u32(codec, &pin->timing_first);
    sn_lib_codec_u32(codec, &pin->timing_count);
    sn_lib_codec_u32(codec, &pin->power_first);
    sn_lib_codec_u32(codec, &pin->power_count);
    sn_lib_codec_item(codec, &pin->item);
}

static inline void sn_lib_codec_state(sn_lib_codec_t* codec, sn_lib_state_t* state)
{
    sn_lib_codec_u32(codec, &state->cell);
    sn_lib_codec_bool(codec, &state->is_latch);
    sn_lib_codec_bool(codec, &state->in_test_cell);
    sn_lib_codec_bool(codec, &state->invalid);
    sn_lib_codec_u32(codec, &state->bits);
    sn_lib_codec_u32(codec, &state->var1);
    sn_lib_codec_u32(codec, &state->var2);
    sn_lib_codec_u32(codec, &state->next_state);
    sn_lib_codec_u32(codec, &state->clocked_on);
    sn_lib_codec_u32(codec, &state->clocked_on_also);
    sn_lib_codec_u32(codec, &state->clear);
    sn_lib_codec_u32(codec, &state->preset);
    sn_lib_codec_u32(codec, &state->power_down_function);
    sn_lib_codec_u32(codec, &state->collision_var1);
    sn_lib_codec_u32(codec, &state->collision_var2);
    sn_lib_codec_item(codec, &state->item);
}

static inline void sn_lib_codec_statetable(sn_lib_codec_t* codec, sn_lib_statetable_t* table)
{
    sn_lib_codec_u32(codec, &table->cell);
    sn_lib_codec_u32(codec, &table->inputs);
    sn_lib_codec_u32(codec, &table->outputs);
    sn_lib_codec_u32(codec, &table->table);
    sn_lib_codec_item(codec, &table->item);
}

static inline void sn_lib_codec_cell(sn_lib_codec_t* codec, sn_lib_cell_t* cell)
{
    sn_lib_codec_u32(codec, &cell->name);
    sn_lib_codec_u32(codec, &cell->footprint);
    sn_lib_codec_f64(codec, &cell->area);
    sn_lib_codec_f64(codec, &cell->cell_leakage_power);
    sn_lib_codec_bool(codec, &cell->dont_use);
    sn_lib_codec_bool(codec, &cell->dont_touch);
    sn_lib_codec_bool(codec, &cell->is_macro);
    sn_lib_codec_bool(codec, &cell->is_pad);
    sn_lib_codec_bool(codec, &cell->clock_gating_integrated);
    sn_lib_codec_u32(codec, &cell->clock_gating_integrated_cell);
    sn_lib_codec_bool(codec, &cell->invalid);
    sn_lib_codec_u32(codec, &cell->pin_first);
    sn_lib_codec_u32(codec, &cell->pin_count);
    sn_lib_codec_u32(codec, &cell->state_first);
    sn_lib_codec_u32(codec, &cell->state_count);
    sn_lib_codec_u32(codec, &cell->statetable_first);
    sn_lib_codec_u32(codec, &cell->statetable_count);
    sn_lib_codec_u32(codec, &cell->leakage_first);
    sn_lib_codec_u32(codec, &cell->leakage_count);
    sn_lib_codec_item(codec, &cell->test_cell_item);
    sn_lib_codec_item(codec, &cell->item);
}

static inline void sn_lib_codec_type(sn_lib_codec_t* codec, sn_lib_type_t* type)
{
    sn_lib_codec_u32(codec, &type->name);
    sn_lib_codec_bool(codec, &type->invalid);
    sn_lib_codec_u32(codec, &type->bit_width);
    sn_lib_codec_i32(codec, &type->bit_from);
    sn_lib_codec_i32(codec, &type->bit_to);
    sn_lib_codec_bool(codec, &type->downto);
    sn_lib_codec_item(codec, &type->item);
}

static inline void sn_lib_codec_conditions(sn_lib_codec_t* codec, sn_lib_operating_conditions_t* c)
{
    sn_lib_codec_u32(codec, &c->name);
    sn_lib_codec_f64(codec, &c->process);
    sn_lib_codec_f64(codec, &c->temperature);
    sn_lib_codec_f64(codec, &c->voltage);
    sn_lib_codec_u32(codec, &c->tree_type);
    sn_lib_codec_item(codec, &c->item);
}

static inline void sn_lib_codec_wire_load(sn_lib_codec_t* codec, sn_lib_wire_load_t* w)
{
    sn_lib_codec_u32(codec, &w->name);
    sn_lib_codec_f64(codec, &w->resistance);
    sn_lib_codec_f64(codec, &w->capacitance);
    sn_lib_codec_f64(codec, &w->area);
    sn_lib_codec_f64(codec, &w->slope);
    sn_lib_codec_u32(codec, &w->fanout_length_offset);
    sn_lib_codec_u32(codec, &w->fanout_length_count);
    sn_lib_codec_item(codec, &w->item);
}

static inline void sn_lib_codec_named_value(sn_lib_codec_t* codec, sn_lib_named_value_t* v)
{
    sn_lib_codec_u32(codec, &v->name);
    sn_lib_codec_f64(codec, &v->value);
}

static inline void sn_lib_codec_define(sn_lib_codec_t* codec, sn_lib_define_t* d)
{
    sn_lib_codec_u32(codec, &d->attribute);
    sn_lib_codec_u32(codec, &d->group);
    sn_lib_codec_u32(codec, &d->type);
}

// An expression: node count, root, name-pool size, nodes, then the names.
static inline void sn_lib_codec_expr(sn_lib_codec_t* codec, sn_liberty_expr_t* expr)
{
    sn_lib_codec_u32(codec, &expr->count);
    sn_lib_codec_u32(codec, &expr->root);
    sn_lib_codec_u32(codec, &expr->names_size);
    if (codec->failed)
        return;
    if (!codec->writing)
    {
        if ((uint64_t)expr->count * 12 + expr->names_size > codec->size - codec->pos)
        {
            codec->failed = true;
            return;
        }
        expr->cap = expr->count;
        expr->names_cap = expr->names_size;
        expr->nodes = expr->count ? (sn_liberty_node_t*)calloc(expr->count, sizeof(*expr->nodes)) : NULL;
        expr->names = expr->names_size ? (char*)malloc(expr->names_size) : NULL;
        if ((expr->count && !expr->nodes) || (expr->names_size && !expr->names))
        {
            codec->out_of_memory = true;
            codec->failed = true;
            return;
        }
    }
    for (uint32_t i = 0; i < expr->count && !codec->failed; i++)
    {
        sn_lib_codec_u32(codec, &expr->nodes[i].op);
        sn_lib_codec_u32(codec, &expr->nodes[i].left);
        sn_lib_codec_u32(codec, &expr->nodes[i].right);
    }
    if (expr->names_size)
        sn_lib_codec_bytes(codec, expr->names, expr->names_size);
}

#define SN_LIB_CODEC_ARRAY(codec, model, field, type, minimum, function)                                   \
    do                                                                                                    \
    {                                                                                                     \
        if (sn_lib_codec_array((codec), (void**)&(model)->field, &(model)->field##_count,                \
                               &(model)->field##_cap, sizeof(type), (minimum)))                           \
            for (uint32_t i = 0; i < (model)->field##_count && !(codec)->failed; i++)                     \
                function((codec), &(model)->field[i]);                                                    \
    } while (0)

// Runs the codec over a model in either direction. In write mode with
// functional_only, the timing, power, leakage, table, and template arrays are
// written empty, pins and cells lose their references to them, and the
// number pool keeps only the wire-load spans.
static inline void sn_lib_codec_model(sn_lib_codec_t* codec, sn_lib_t* model, bool functional_only)
{
    uint32_t flags = functional_only ? SN_LIB_BINARY_FUNCTIONAL_ONLY : 0;
    sn_lib_codec_u32(codec, &flags);
    functional_only = (flags & SN_LIB_BINARY_FUNCTIONAL_ONLY) != 0;
    sn_lib_codec_u64(codec, &model->source_size);
    sn_lib_codec_u64(codec, &model->source_hash);
    if (!codec->writing)
    {
        free(model->path);
        model->path = NULL;
    }
    sn_lib_codec_string(codec, &model->path);

    // String pool.
    sn_lib_codec_u32(codec, &model->names_size);
    if (codec->failed)
        return;
    if (!codec->writing)
    {
        if (model->names_size > codec->size - codec->pos)
        {
            codec->failed = true;
            return;
        }
        model->names_cap = model->names_size;
        model->names = model->names_size ? (char*)malloc(model->names_size) : NULL;
        if (model->names_size && !model->names)
        {
            codec->out_of_memory = true;
            codec->failed = true;
            return;
        }
    }
    if (model->names_size)
        sn_lib_codec_bytes(codec, model->names, model->names_size);

    // Number pool. A functional-only writer emits only the wire-load spans and
    // remaps their offsets while writing the wire-load records below.
    uint32_t doubles_count = model->doubles_count;
    if (codec->writing && functional_only)
    {
        doubles_count = 0;
        for (uint32_t i = 0; i < model->wire_loads_count; i++)
            doubles_count += 2 * model->wire_loads[i].fanout_length_count;
    }
    sn_lib_codec_u32(codec, &doubles_count);
    if (codec->failed)
        return;
    if (!codec->writing)
    {
        if ((uint64_t)doubles_count * 8 > codec->size - codec->pos)
        {
            codec->failed = true;
            return;
        }
        model->doubles_count = model->doubles_cap = doubles_count;
        model->doubles = doubles_count ? (double*)malloc((size_t)doubles_count * sizeof(double)) : NULL;
        if (doubles_count && !model->doubles)
        {
            codec->out_of_memory = true;
            codec->failed = true;
            return;
        }
        for (uint32_t i = 0; i < doubles_count && !codec->failed; i++)
            sn_lib_codec_f64(codec, &model->doubles[i]);
    }
    else if (functional_only)
    {
        for (uint32_t i = 0; i < model->wire_loads_count && !codec->failed; i++)
            for (uint32_t k = 0; k < 2 * model->wire_loads[i].fanout_length_count && !codec->failed; k++)
                sn_lib_codec_f64(codec, &model->doubles[model->wire_loads[i].fanout_length_offset + k]);
    }
    else
        for (uint32_t i = 0; i < doubles_count && !codec->failed; i++)
            sn_lib_codec_f64(codec, &model->doubles[i]);

    // Library header.
    sn_lib_codec_u32(codec, &model->name);
    sn_lib_codec_u32(codec, &model->technology);
    sn_lib_codec_u32(codec, &model->delay_model);
    sn_lib_codec_u32(codec, &model->bus_naming_style);
    sn_lib_codec_u32(codec, &model->time_unit);
    sn_lib_codec_u32(codec, &model->voltage_unit);
    sn_lib_codec_u32(codec, &model->current_unit);
    sn_lib_codec_u32(codec, &model->leakage_power_unit);
    sn_lib_codec_u32(codec, &model->pulling_resistance_unit);
    sn_lib_codec_f64(codec, &model->capacitive_load_unit);
    sn_lib_codec_u32(codec, &model->capacitive_load_unit_name);
    sn_lib_codec_f64(codec, &model->nom_process);
    sn_lib_codec_f64(codec, &model->nom_temperature);
    sn_lib_codec_f64(codec, &model->nom_voltage);
    sn_lib_codec_u32(codec, &model->default_operating_conditions);
    sn_lib_codec_u32(codec, &model->malformed_count);
    sn_lib_codec_u32(codec, &model->invalid_cells);

    SN_LIB_CODEC_ARRAY(codec, model, defaults, sn_lib_named_value_t, 12, sn_lib_codec_named_value);
    SN_LIB_CODEC_ARRAY(codec, model, voltage_map, sn_lib_named_value_t, 12, sn_lib_codec_named_value);
    SN_LIB_CODEC_ARRAY(codec, model, defines, sn_lib_define_t, 12, sn_lib_codec_define);
    SN_LIB_CODEC_ARRAY(codec, model, conditions, sn_lib_operating_conditions_t, 32, sn_lib_codec_conditions);
    SN_LIB_CODEC_ARRAY(codec, model, types, sn_lib_type_t, 18, sn_lib_codec_type);

    // Wire loads: in a functional-only write the offsets are renumbered to the
    // compacted number pool.
    if (codec->writing && functional_only)
    {
        uint32_t count = model->wire_loads_count, next = 0;
        sn_lib_codec_u32(codec, &count);
        for (uint32_t i = 0; i < count && !codec->failed; i++)
        {
            sn_lib_wire_load_t copy = model->wire_loads[i];
            copy.fanout_length_offset = next;
            next += 2 * copy.fanout_length_count;
            sn_lib_codec_wire_load(codec, &copy);
        }
    }
    else
        SN_LIB_CODEC_ARRAY(codec, model, wire_loads, sn_lib_wire_load_t, 44, sn_lib_codec_wire_load);

    // Timing and power data, absent from functional-only files.
    if (codec->writing && functional_only)
    {
        uint32_t zero = 0;
        for (int i = 0; i < 5; i++)
            sn_lib_codec_u32(codec, &zero);
    }
    else
    {
        SN_LIB_CODEC_ARRAY(codec, model, templates, sn_lib_template_t, 48, sn_lib_codec_template);
        SN_LIB_CODEC_ARRAY(codec, model, tables, sn_lib_table_t, 41, sn_lib_codec_table);
        SN_LIB_CODEC_ARRAY(codec, model, timings, sn_lib_timing_t, 92, sn_lib_codec_timing);
        SN_LIB_CODEC_ARRAY(codec, model, powers, sn_lib_power_t, 28, sn_lib_codec_power);
        SN_LIB_CODEC_ARRAY(codec, model, leakages, sn_lib_leakage_t, 20, sn_lib_codec_leakage);
    }

    // Cells, pins, and sequential groups.
    if (codec->writing && functional_only)
    {
        uint32_t count = model->cells_count;
        sn_lib_codec_u32(codec, &count);
        for (uint32_t i = 0; i < count && !codec->failed; i++)
        {
            sn_lib_cell_t copy = model->cells[i];
            copy.leakage_first = copy.leakage_count = 0;
            sn_lib_codec_cell(codec, &copy);
        }
        count = model->pins_count;
        sn_lib_codec_u32(codec, &count);
        for (uint32_t i = 0; i < count && !codec->failed; i++)
        {
            sn_lib_pin_t copy = model->pins[i];
            copy.timing_first = copy.timing_count = copy.power_first = copy.power_count = 0;
            sn_lib_codec_pin(codec, &copy);
        }
    }
    else
    {
        SN_LIB_CODEC_ARRAY(codec, model, cells, sn_lib_cell_t, 62, sn_lib_codec_cell);
        SN_LIB_CODEC_ARRAY(codec, model, pins, sn_lib_pin_t, 192, sn_lib_codec_pin);
    }
    SN_LIB_CODEC_ARRAY(codec, model, states, sn_lib_state_t, 55, sn_lib_codec_state);
    SN_LIB_CODEC_ARRAY(codec, model, statetables, sn_lib_statetable_t, 16, sn_lib_codec_statetable);
    SN_LIB_CODEC_ARRAY(codec, model, exprs, sn_liberty_expr_t, 12, sn_lib_codec_expr);

    // Warnings.
    uint32_t warnings_count = model->warnings_count;
    sn_lib_codec_u32(codec, &warnings_count);
    if (codec->failed)
        return;
    if (!codec->writing)
    {
        if ((uint64_t)warnings_count * 4 > codec->size - codec->pos)
        {
            codec->failed = true;
            return;
        }
        model->warnings = warnings_count ? (char**)calloc(warnings_count, sizeof(char*)) : NULL;
        if (warnings_count && !model->warnings)
        {
            codec->out_of_memory = true;
            codec->failed = true;
            return;
        }
        model->warnings_cap = warnings_count;
        model->warnings_count = 0;
        for (uint32_t i = 0; i < warnings_count && !codec->failed; i++)
        {
            sn_lib_codec_string(codec, &model->warnings[i]);
            if (!codec->failed)
                model->warnings_count++;
        }
    }
    else
        for (uint32_t i = 0; i < warnings_count && !codec->failed; i++)
            sn_lib_codec_string(codec, &model->warnings[i]);
}

#define SN_LIB_BINARY_HEADER_SIZE 12 // magic and version, excluded from the payload hash
#define SN_LIB_BINARY_TRAILER_SIZE 8  // the payload hash

// Encodes the model into a malloc'd byte buffer (the exact file contents).
// Returns false on an allocation failure. The payload is encoded first so
// its hash can be appended.
static inline bool sn_lib_encode_binary(const sn_lib_t* model, const sn_lib_binary_options_t* options,
                                        uint8_t** bytes, size_t* size)
{
    *bytes = NULL;
    *size = 0;
    if (!model)
        return false;
    sn_lib_codec_t codec;
    memset(&codec, 0, sizeof(codec));
    codec.writing = true;
    char magic[8];
    memcpy(magic, SN_LIB_BINARY_MAGIC, 8);
    sn_lib_codec_bytes(&codec, magic, 8);
    uint32_t version = SN_LIB_BINARY_VERSION;
    sn_lib_codec_u32(&codec, &version);
    // The codec never modifies the model in write mode.
    sn_lib_codec_model(&codec, (sn_lib_t*)model, options && options->functional_only);
    if (!codec.failed)
    {
        uint64_t hash = sn_liberty_hash_bytes(codec.buffer + SN_LIB_BINARY_HEADER_SIZE,
                                              codec.buffer_size - SN_LIB_BINARY_HEADER_SIZE);
        sn_lib_codec_u64(&codec, &hash);
    }
    if (codec.failed)
    {
        free(codec.buffer);
        return false;
    }
    *bytes = codec.buffer;
    *size = codec.buffer_size;
    return true;
}

// Writes the model. Returns false on an allocation or I/O error; the caller
// owns the file.
static inline bool sn_lib_write_binary(const sn_lib_t* model, FILE* out, const sn_lib_binary_options_t* options)
{
    uint8_t* bytes = NULL;
    size_t size = 0;
    if (!out || !sn_lib_encode_binary(model, options, &bytes, &size))
        return false;
    bool ok = fwrite(bytes, 1, size, out) == size && fflush(out) == 0;
    free(bytes);
    return ok;
}

static inline bool sn_lib_write_binary_file(const sn_lib_t* model, const char* path,
                                            const sn_lib_binary_options_t* options)
{
    FILE* out = fopen(path, "wb");
    if (!out)
        return false;
    bool ok = sn_lib_write_binary(model, out, options);
    if (fclose(out) != 0)
        ok = false;
    if (!ok)
        remove(path);
    return ok;
}

// Validates every cross reference of a freshly read model.
static inline bool sn_lib_binary_name_ok(const sn_lib_t* model, uint32_t name)
{
    return name == SN_LIB_NONE || (name < model->names_size && (name == 0 || model->names[name - 1] == 0));
}

static inline bool sn_lib_binary_span_ok(uint32_t offset, uint32_t count, uint32_t limit)
{
    return count == 0 ? offset <= limit || offset == SN_LIB_NONE : offset < limit && count <= limit - offset;
}

static inline bool sn_lib_binary_expr_ok(const sn_lib_t* model, uint32_t expr)
{
    return expr == SN_LIB_NONE || expr < model->exprs_count;
}

static inline bool sn_lib_binary_table_ok(const sn_lib_t* model, uint32_t table)
{
    return table == SN_LIB_NONE || table < model->tables_count;
}

static inline bool sn_lib_binary_validate(const sn_lib_t* model)
{
    // The string pool must be a sequence of NUL-terminated strings.
    if (model->names_size && model->names[model->names_size - 1] != 0)
        return false;
    uint32_t header_names[] = {model->name, model->technology, model->delay_model, model->bus_naming_style,
                               model->time_unit, model->voltage_unit, model->current_unit,
                               model->leakage_power_unit, model->pulling_resistance_unit,
                               model->capacitive_load_unit_name, model->default_operating_conditions};
    for (size_t i = 0; i < sizeof(header_names) / sizeof(header_names[0]); i++)
        if (!sn_lib_binary_name_ok(model, header_names[i]))
            return false;
    for (uint32_t i = 0; i < model->exprs_count; i++)
    {
        const sn_liberty_expr_t* expr = &model->exprs[i];
        if (expr->root >= expr->count || (expr->names_size && expr->names[expr->names_size - 1] != 0))
            return false;
        for (uint32_t n = 0; n < expr->count; n++)
        {
            const sn_liberty_node_t* node = &expr->nodes[n];
            if (node->op > SN_LIBERTY_XOR)
                return false;
            if (node->op == SN_LIBERTY_PIN && node->left >= expr->names_size)
                return false;
            if (node->op == SN_LIBERTY_NOT && node->left >= n)
                return false;
            if (node->op >= SN_LIBERTY_AND && (node->left >= n || node->right >= n))
                return false;
        }
    }
    for (uint32_t i = 0; i < model->defaults_count; i++)
        if (!sn_lib_binary_name_ok(model, model->defaults[i].name))
            return false;
    for (uint32_t i = 0; i < model->voltage_map_count; i++)
        if (!sn_lib_binary_name_ok(model, model->voltage_map[i].name))
            return false;
    for (uint32_t i = 0; i < model->defines_count; i++)
        if (!sn_lib_binary_name_ok(model, model->defines[i].attribute) ||
            !sn_lib_binary_name_ok(model, model->defines[i].group) ||
            !sn_lib_binary_name_ok(model, model->defines[i].type))
            return false;
    for (uint32_t i = 0; i < model->conditions_count; i++)
        if (!sn_lib_binary_name_ok(model, model->conditions[i].name) ||
            !sn_lib_binary_name_ok(model, model->conditions[i].tree_type))
            return false;
    for (uint32_t i = 0; i < model->types_count; i++)
        if (!sn_lib_binary_name_ok(model, model->types[i].name))
            return false;
    for (uint32_t i = 0; i < model->wire_loads_count; i++)
    {
        const sn_lib_wire_load_t* w = &model->wire_loads[i];
        if (!sn_lib_binary_name_ok(model, w->name) || w->fanout_length_count > UINT32_MAX / 2 ||
            !sn_lib_binary_span_ok(w->fanout_length_offset, 2 * w->fanout_length_count, model->doubles_count))
            return false;
    }
    for (uint32_t i = 0; i < model->templates_count; i++)
    {
        const sn_lib_template_t* t = &model->templates[i];
        if (!sn_lib_binary_name_ok(model, t->name) || !sn_lib_binary_name_ok(model, t->kind) || t->dims > 3)
            return false;
        for (uint32_t d = 0; d < 3; d++)
            if (!sn_lib_binary_name_ok(model, t->variable[d]) ||
                !sn_lib_binary_span_ok(t->index_offset[d], t->index_count[d], model->doubles_count))
                return false;
    }
    for (uint32_t i = 0; i < model->tables_count; i++)
    {
        const sn_lib_table_t* t = &model->tables[i];
        if ((t->template_id != SN_LIB_NONE && t->template_id >= model->templates_count) || t->dims > 3 ||
            !sn_lib_binary_span_ok(t->values_offset, t->values_count, model->doubles_count))
            return false;
        for (uint32_t d = 0; d < 3; d++)
            if (!sn_lib_binary_span_ok(t->index_offset[d], t->index_count[d], model->doubles_count))
                return false;
    }
    for (uint32_t i = 0; i < model->timings_count; i++)
    {
        const sn_lib_timing_t* arc = &model->timings[i];
        uint32_t tables[] = {arc->cell_rise, arc->cell_fall, arc->rise_transition,
                             arc->fall_transition, arc->rise_constraint, arc->fall_constraint};
        if (arc->pin >= model->pins_count || arc->timing_type > SN_LIB_TIMING_OTHER ||
            arc->sense > SN_LIB_NON_UNATE || !sn_lib_binary_expr_ok(model, arc->when) ||
            !sn_lib_binary_name_ok(model, arc->related_pin) ||
            !sn_lib_binary_name_ok(model, arc->related_bus_pins) ||
            !sn_lib_binary_name_ok(model, arc->related_output_pin) ||
            !sn_lib_binary_name_ok(model, arc->timing_type_name) || !sn_lib_binary_name_ok(model, arc->sdf_cond))
            return false;
        for (size_t k = 0; k < 6; k++)
            if (!sn_lib_binary_table_ok(model, tables[k]))
                return false;
    }
    for (uint32_t i = 0; i < model->powers_count; i++)
    {
        const sn_lib_power_t* power = &model->powers[i];
        if (power->pin >= model->pins_count || !sn_lib_binary_expr_ok(model, power->when) ||
            !sn_lib_binary_name_ok(model, power->related_pin) ||
            !sn_lib_binary_name_ok(model, power->related_pg_pin) || !sn_lib_binary_table_ok(model, power->rise_power) ||
            !sn_lib_binary_table_ok(model, power->fall_power) || !sn_lib_binary_table_ok(model, power->power))
            return false;
    }
    for (uint32_t i = 0; i < model->leakages_count; i++)
        if (model->leakages[i].cell >= model->cells_count || !sn_lib_binary_expr_ok(model, model->leakages[i].when) ||
            !sn_lib_binary_name_ok(model, model->leakages[i].related_pg_pin))
            return false;
    for (uint32_t i = 0; i < model->cells_count; i++)
    {
        const sn_lib_cell_t* cell = &model->cells[i];
        if (!sn_lib_binary_name_ok(model, cell->name) || !sn_lib_binary_name_ok(model, cell->footprint) ||
            !sn_lib_binary_name_ok(model, cell->clock_gating_integrated_cell) ||
            !sn_lib_binary_span_ok(cell->pin_first, cell->pin_count, model->pins_count) ||
            !sn_lib_binary_span_ok(cell->state_first, cell->state_count, model->states_count) ||
            !sn_lib_binary_span_ok(cell->statetable_first, cell->statetable_count, model->statetables_count) ||
            !sn_lib_binary_span_ok(cell->leakage_first, cell->leakage_count, model->leakages_count))
            return false;
    }
    for (uint32_t i = 0; i < model->pins_count; i++)
    {
        const sn_lib_pin_t* pin = &model->pins[i];
        uint32_t names[] = {pin->name, pin->bus_type, pin->internal_node, pin->nextstate_type, pin->signal_type,
                            pin->pin_func_type, pin->related_power_pin, pin->related_ground_pin, pin->pg_type,
                            pin->voltage_name};
        uint32_t exprs[] = {pin->function, pin->three_state, pin->state_function, pin->x_function,
                            pin->power_down_function};
        if (pin->cell >= model->cells_count || pin->kind > SN_LIB_PIN_PG || pin->direction > SN_LIB_INTERNAL ||
            (pin->parent != SN_LIB_NONE && pin->parent >= model->pins_count) ||
            !sn_lib_binary_span_ok(pin->timing_first, pin->timing_count, model->timings_count) ||
            !sn_lib_binary_span_ok(pin->power_first, pin->power_count, model->powers_count))
            return false;
        for (size_t k = 0; k < sizeof(names) / sizeof(names[0]); k++)
            if (!sn_lib_binary_name_ok(model, names[k]))
                return false;
        for (size_t k = 0; k < sizeof(exprs) / sizeof(exprs[0]); k++)
            if (!sn_lib_binary_expr_ok(model, exprs[k]))
                return false;
    }
    for (uint32_t i = 0; i < model->states_count; i++)
    {
        const sn_lib_state_t* state = &model->states[i];
        uint32_t exprs[] = {state->next_state, state->clocked_on, state->clocked_on_also, state->clear,
                            state->preset, state->power_down_function};
        if (state->cell >= model->cells_count || !sn_lib_binary_name_ok(model, state->var1) ||
            !sn_lib_binary_name_ok(model, state->var2) || state->collision_var1 > SN_LIB_COLLISION_UNKNOWN ||
            state->collision_var2 > SN_LIB_COLLISION_UNKNOWN)
            return false;
        for (size_t k = 0; k < sizeof(exprs) / sizeof(exprs[0]); k++)
            if (!sn_lib_binary_expr_ok(model, exprs[k]))
                return false;
    }
    for (uint32_t i = 0; i < model->statetables_count; i++)
        if (model->statetables[i].cell >= model->cells_count ||
            !sn_lib_binary_name_ok(model, model->statetables[i].inputs) ||
            !sn_lib_binary_name_ok(model, model->statetables[i].outputs) ||
            !sn_lib_binary_name_ok(model, model->statetables[i].table))
            return false;
    return true;
}

// Decodes a model from the bytes of a binary file; `name` is used in
// messages and may be NULL. Returns NULL only when the model object itself
// cannot be allocated; otherwise check sn_lib_ok() and ->error.
static inline sn_lib_t* sn_lib_decode_binary(const uint8_t* data, size_t size, const char* name)
{
    sn_lib_t* model = (sn_lib_t*)calloc(1, sizeof(sn_lib_t));
    if (!model)
        return NULL;
    if (name)
        model->path = sn_lib_copy_string(name);
    model->nom_process = model->nom_temperature = model->nom_voltage = NAN;
    model->capacitive_load_unit = NAN;
    const char* problem = NULL;
    if (!data)
        problem = "no data";
    else if (size < SN_LIB_BINARY_HEADER_SIZE + SN_LIB_BINARY_TRAILER_SIZE ||
             memcmp(data, SN_LIB_BINARY_MAGIC, 8) != 0)
        problem = "not an SN library binary";
    if (!problem)
    {
        // The trailer hash covers everything between the header and itself.
        size_t payload = size - SN_LIB_BINARY_HEADER_SIZE - SN_LIB_BINARY_TRAILER_SIZE;
        uint64_t stored = 0;
        for (int i = 0; i < 8; i++)
            stored |= (uint64_t)data[size - SN_LIB_BINARY_TRAILER_SIZE + i] << (8 * i);
        if (stored != sn_liberty_hash_bytes(data + SN_LIB_BINARY_HEADER_SIZE, payload))
            problem = "SN library binary is corrupted (payload hash mismatch)";
    }
    if (!problem)
    {
        sn_lib_codec_t codec;
        memset(&codec, 0, sizeof(codec));
        codec.data = data;
        codec.size = size - SN_LIB_BINARY_TRAILER_SIZE;
        codec.pos = 8;
        uint32_t version = 0;
        sn_lib_codec_u32(&codec, &version);
        if (version != SN_LIB_BINARY_VERSION)
            problem = "unsupported SN library binary version";
        else
        {
            sn_lib_codec_model(&codec, model, false);
            if (codec.out_of_memory)
                model->out_of_memory = true;
            else if (codec.failed || codec.pos != codec.size)
                problem = "malformed or truncated SN library binary";
            else if (!sn_lib_binary_validate(model))
                problem = "SN library binary fails validation";
        }
    }
    if (problem)
    {
        const char* path = model->path ? model->path : "?";
        if (name && (!model->path || strcmp(model->path, name) != 0))
        {
            // Prefer the caller's name over one decoded from a damaged file.
            free(model->path);
            model->path = sn_lib_copy_string(name);
            path = model->path ? model->path : name;
        }
        model->error = (char*)malloc(strlen(path) + strlen(problem) + 8);
        if (model->error)
            sprintf(model->error, "%s: %s", path, problem);
        else
            model->out_of_memory = true;
        return model;
    }
    if (!model->out_of_memory)
        sn_lib_index_cells(model);
    return model;
}

// Reads a model from an open binary file. Returns NULL only when the model
// object itself cannot be allocated; otherwise check sn_lib_ok() and ->error.
static inline sn_lib_t* sn_lib_read_binary_named(FILE* in, const char* name)
{
    if (!in)
    {
        sn_lib_t* model = sn_lib_decode_binary(NULL, 0, name);
        if (model)
        {
            free(model->error);
            model->error = NULL;
            const char* path = name ? name : "?";
            model->error = (char*)malloc(strlen(path) + 32);
            if (model->error)
                sprintf(model->error, "%s: cannot open file", path);
            else
                model->out_of_memory = true;
        }
        return model;
    }
    size_t cap = 1u << 20, size = 0;
    uint8_t* data = (uint8_t*)malloc(cap);
    while (data)
    {
        size += fread(data + size, 1, cap - size, in);
        if (size < cap)
            break;
        cap *= 2;
        uint8_t* grown = (uint8_t*)realloc(data, cap);
        if (!grown)
            free(data);
        data = grown;
    }
    sn_lib_t* model;
    if (!data)
    {
        model = (sn_lib_t*)calloc(1, sizeof(sn_lib_t));
        if (model)
        {
            model->out_of_memory = true;
            if (name)
                model->path = sn_lib_copy_string(name);
        }
        return model;
    }
    if (ferror(in))
    {
        model = sn_lib_decode_binary(NULL, 0, name);
        if (model && model->error)
        {
            free(model->error);
            model->error = NULL;
            const char* path = name ? name : "?";
            model->error = (char*)malloc(strlen(path) + 32);
            if (model->error)
                sprintf(model->error, "%s: read error", path);
            else
                model->out_of_memory = true;
        }
    }
    else
        model = sn_lib_decode_binary(data, size, name);
    free(data);
    return model;
}

static inline sn_lib_t* sn_lib_read_binary(FILE* in)
{
    return sn_lib_read_binary_named(in, NULL);
}


static inline sn_lib_t* sn_lib_load_binary(const char* path)
{
    FILE* in = fopen(path, "rb");
    sn_lib_t* model = sn_lib_read_binary_named(in, path);
    if (in)
        fclose(in);
    return model;
}

// True when the file starts with the binary magic.
static inline bool sn_lib_is_binary_file(const char* path)
{
    FILE* in = fopen(path, "rb");
    if (!in)
        return false;
    char magic[8];
    bool binary = fread(magic, 1, 8, in) == 8 && memcmp(magic, SN_LIB_BINARY_MAGIC, 8) == 0;
    fclose(in);
    return binary;
}

// Loads a library from either representation, chosen by the file's magic.
static inline sn_lib_t* sn_lib_load_any(const char* path)
{
    return sn_lib_is_binary_file(path) ? sn_lib_load_binary(path) : sn_lib_load(path);
}

// Reads just the identity of a binary file: the size and hash of the library
// text it was built from and whether it is functional-only.
static inline bool sn_lib_binary_identity(FILE* in, uint64_t* source_size, uint64_t* source_hash,
                                          bool* functional_only)
{
    uint8_t header[8 + 4 + 4 + 8 + 8];
    if (!in || fread(header, 1, sizeof(header), in) != sizeof(header) ||
        memcmp(header, SN_LIB_BINARY_MAGIC, 8) != 0)
        return false;
    sn_lib_codec_t codec;
    memset(&codec, 0, sizeof(codec));
    codec.data = header + 8;
    codec.size = sizeof(header) - 8;
    uint32_t version = 0, flags = 0;
    sn_lib_codec_u32(&codec, &version);
    sn_lib_codec_u32(&codec, &flags);
    sn_lib_codec_u64(&codec, source_size);
    sn_lib_codec_u64(&codec, source_hash);
    *functional_only = (flags & SN_LIB_BINARY_FUNCTIONAL_ONLY) != 0;
    return !codec.failed && version == SN_LIB_BINARY_VERSION;
}

// Size and hash of a library text file, for comparison with a binary's
// identity. Reads the bytes without parsing them; the parser hashes the same
// bytes, so the two agree.
static inline bool sn_lib_source_identity(const char* path, uint64_t* source_size, uint64_t* source_hash)
{
    FILE* in = fopen(path, "rb");
    if (!in)
        return false;
    size_t cap = 1u << 20, size = 0;
    uint8_t* data = (uint8_t*)malloc(cap);
    while (data)
    {
        size += fread(data + size, 1, cap - size, in);
        if (size < cap)
            break;
        cap *= 2;
        uint8_t* grown = (uint8_t*)realloc(data, cap);
        if (!grown)
            free(data);
        data = grown;
    }
    bool ok = data && !ferror(in);
    fclose(in);
    if (ok)
    {
        *source_size = size;
        *source_hash = sn_liberty_hash_bytes(data, size);
    }
    free(data);
    return ok;
}

ABC_NAMESPACE_HEADER_END

#endif
