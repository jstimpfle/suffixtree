/* Suffix tree construction with Ukkonen's algorithm.
 *
 * Base implementation, uses 26 pointers per node (only lowercase letters
 * allowed), therefore very inflexible and inefficient.
 *
 * Not heavily tested, probably still contains bugs.
 *
 * Written by Jens Stimpfle in 2014.
 * No license. Do what you want with it.
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NUM_SYMBOLS 26
#define FIRST_SYMBOL 'a'

/* We don't have nodes. Our edges all have an implicit "node at the end",
 * represented by the members "link" and "childs" */

struct edge {
        const char *label;
        int len;
        struct edge *link;
        struct edge *childs[NUM_SYMBOLS];
};

struct state {
        struct edge *edge;
        struct edge *parent;
        int offset;
        const char *suffix;
        const char *tail;
};


static struct state st;
static struct edge rootedge;
static struct edge *edges;
static size_t edges_size;
static size_t edges_capacity;
static char *string;
static char *string_end;
static size_t string_capacity;


/*********************
 * MEMORY MANAGEMENT *
 *********************/

static void *need_alloced(void *ptr)
{
        if (ptr == NULL) {
                fprintf(stderr, "OOM!\n");
                exit(1);
        }
        return ptr;
}

static void *xmalloc(size_t s)
{
        return need_alloced(malloc(s));
}

static void *xrealloc(void *ptr, size_t s)
{
        return need_alloced(realloc(ptr, s));
}

static struct edge *allocate_edge(void)
{
        assert(edges_size < edges_capacity);
        struct edge *edge = &edges[edges_size++];
        memset(edge, 0, sizeof *edge);
        return edge;
}


/**********************
 * PRINTING FUNCTIONS *
 **********************/

static void print_edge(struct edge *edge)
{
        /*printf("\"");
         */
        fwrite(edge->label, edge->len, 1, stdout);
        /*printf("\"");
         */
}

static void print_edge_nl(struct edge *edge)
{
        print_edge(edge);
        printf("\n");
}

static void print_edge_full(struct edge *edge)
{
        printf("%s", edge->label);
}

static void print_tree_sub(struct edge *edge, int indent)
{
        int i;

        for (i = 0; i < indent; i++)
                printf(" ");
        print_edge_nl(edge);

        for (i = 0; i < NUM_SYMBOLS; i++) {
                if (edge->childs[i] != NULL) {
                        print_tree_sub(edge->childs[i], indent + edge->len);
                }
        }
}

static void print_tree(void)
{
        int i;
        for (i = 0; i < NUM_SYMBOLS; i++)
                if (rootedge.childs[i])
                        print_tree_sub(rootedge.childs[i], 0);
}

static void print_all_suffixes_sub(struct edge *edge, char *buf, int offset)
{
        memcpy(&buf[offset], edge->label, edge->len);

        int i, havechilds = 0;
        for (i = 0; i < NUM_SYMBOLS; i++) {
                if (edge->childs[i] != NULL) {
                        havechilds = 1;
                        print_all_suffixes_sub(edge->childs[i],
                                               buf, offset + edge->len);
                }
        }
        if (!havechilds) {
                fwrite(buf, offset + edge->len, 1, stdout);
                printf("\n");
        }
}

static void print_all_suffixes(void)
{
        char *buf = xmalloc(string_end - string);
        print_all_suffixes_sub(&rootedge, buf, 0);
        free(buf);
}


/*********************
 * TREE CONSTRUCTION *
 *********************/

static void go_to_node(struct edge *edge)
{
        st.edge = edge;
        st.offset = edge->len;
        st.parent = NULL;
}

static int get_symbol(char c)
{
        int sym = (int)c - FIRST_SYMBOL;
        assert(0 <= sym && sym < NUM_SYMBOLS);
        return sym;
}

/* Advance the current position in the tree if there's a continuation beginning
 * with the given character.
 * Returns wether a step was taken.
 */
static int charstep(char c)
{
        if (st.offset >= st.edge->len) {
                int sym = get_symbol(c);
                if (st.edge->childs[sym] == NULL)
                        return 0;
                st.parent = st.edge;
                st.edge = st.edge->childs[sym];
                st.offset = 0;
                assert(st.edge->label[st.offset] == c);
        }
        if (st.edge->label[st.offset] != c)
                return 0;
        else {
                st.offset++;
                return 1;
        }
}

static const char *consume_string(const char *s)
{
        while (s < string_end && charstep(*s))
                s++;
        return s;
}

static void consume_whole_string(const char *s, const char *end)
{
        while (s < end && charstep(*s))
                s++;
        assert(s == end);
}

static void insert_tail(void)
{
        int sym;
        struct edge *child;
        child = allocate_edge();
        child->label = st.tail;
        child->len = string_end - st.tail;
        sym = get_symbol(st.tail[0]);
        assert(st.offset == st.edge->len);
        assert(st.edge->childs[sym] == NULL);
        st.edge->childs[sym] = child;
}

static void split_if_not_at_node(void)
{
        assert(0 <= st.offset && st.offset <= st.edge->len);

        int sym;
        struct edge *tophalf, *bottomhalf;

        if (st.offset >= st.edge->len)
                return;

        tophalf = allocate_edge();
        bottomhalf = st.edge;
        st.edge = tophalf;

        tophalf->label = bottomhalf->label;
        tophalf->len = st.offset;
        bottomhalf->label += st.offset;
        bottomhalf->len   -= st.offset;

        sym = get_symbol(bottomhalf->label[0]);
        tophalf->childs[sym] = bottomhalf;

        /* fix parent pointer */
        sym = get_symbol(tophalf->label[0]);
        assert(st.parent != NULL);
        assert(st.parent->childs[sym] == bottomhalf);
        st.parent->childs[sym] = tophalf;
}


/* Repositions tree pointer and fixes suffix links.
 *
 * Finally, if there's a tail left, insert the tail and returns 1. Otherwise,
 * returns 0.
 *
 * This function is hard to understand. See
 * https://www.cs.duke.edu/courses/fall12/compsci260/resources/suffix.trees.in.detail.pdf
 */
static int state_transition(void)
{
        if (st.tail < st.suffix)
                st.tail = st.suffix;
        if (st.tail == string_end)
                return 0;
        if (st.edge == &rootedge) {
                assert(st.tail == st.suffix);
        } else if (st.edge->link == NULL && st.parent == &rootedge) {
                struct edge *last = st.edge;
                go_to_node(&rootedge);
                consume_whole_string(last->label + 1, last->label + last->len);
                split_if_not_at_node();
                last->link = st.edge;
        } else if (st.edge->link == NULL && st.parent != &rootedge) {
                struct edge *last = st.edge;
                go_to_node(st.parent->link);
                consume_whole_string(last->label, last->label + last->len);
                split_if_not_at_node();
                last->link = st.edge;
        } else if (st.edge->link != NULL) {
                go_to_node(st.edge->link);
        } else {
                assert(0);
        }

        st.tail = consume_string(st.tail);
        split_if_not_at_node();

        if (st.tail == string_end)
                return 0;

        insert_tail();
        st.suffix++;
        return 1;
}

static void state_init(void)
{
        st.suffix = st.tail = string;
}

static void construct_suffixtree(void)
{
        ssize_t nread = getline(&string, &string_capacity, stdin);

        if (nread == -1) {
                perror("getline()");
                exit(1);
        }

        string_end = string + nread;
        while (string_end > string
               && (string_end[-1] == '\r' || string_end[-1] == '\n'))
                string_end--;

        edges_capacity = 2 * (string_end - string);
        edges = xrealloc(edges, edges_capacity * sizeof *edges);
        edges_size = 0;

        rootedge.link = NULL;
        rootedge.label = "(root)";
        rootedge.len = 0;  /* ! */
        memset(rootedge.childs, 0, sizeof rootedge.childs);

        go_to_node(&rootedge);

        state_init();

        while (state_transition()) {
                /*print_tree();
                 */
        }
}

int main(void)
{
        construct_suffixtree();

        /*print_tree();
         */
        /*print_all_suffixes();
         */

        return 0;
}
