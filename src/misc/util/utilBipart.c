/**CFile****************************************************************

  FileName    [utilBipart.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Handling counter-examples.]

  Synopsis    [Handling counter-examples.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: utilBipart.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <assert.h>
#include <time.h>

#include "misc/util/abc_global.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define List_ForEachSet(pList, pSet, s) for ((s) = 0, (pSet) = (pList) + 1; (s) < (pList)[0]; ++(s), (pSet) += (pSet)[0] + 1)
#define Set_ForEachNode(pSet, node, n) for ((n) = 1; (n) <= (pSet)[0] && (((node) = (pSet)[n]), 1); ++(n))

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

typedef struct {
  int *data;
  int size;
  int cap;
} IntVector;

typedef struct {
  int node_count;
  int edge_count;
  int *offset;
  int *neighbors;
  int *orig_ids;
} Graph;

typedef struct {
  int sizeA;
  int sizeB;
  int *nodesA;
  int *nodesB;
  uint64_t hashA;
  uint64_t hashB;
} ComponentRecord;

typedef struct {
  ComponentRecord *data;
  int size;
  int cap;
} ComponentList;

typedef struct {
  int u;
  int v;
  int assigned;
} EdgeInfo;

typedef struct {
  uint64_t key;
  int index;
} EdgeMapEntry;

typedef struct {
  IntVector nodesA;
  IntVector nodesB;
  IntVector edges;
  int edge_count;
} WorkComponent;

typedef struct {
  Graph graph;
  EdgeInfo *edges;
  EdgeMapEntry *edge_map;
  int edge_count;
  WorkComponent *components;
  int component_count;
} SolverContext;

static void validate_edge_ownership(const SolverContext *ctx) {
  int *owner;
  int i;
  if (ctx->edge_count == 0) {
    return;
  }
  owner = (int *)malloc(ctx->edge_count * sizeof(int));
  assert(owner);
  for (i = 0; i < ctx->edge_count; ++i) {
    owner[i] = -1;
  }
  for (i = 0; i < ctx->component_count; ++i) {
    const WorkComponent *comp = &ctx->components[i];
    int j;
    for (j = 0; j < comp->edges.size; ++j) {
      int idx = comp->edges.data[j];
      assert(idx >= 0 && idx < ctx->edge_count);
      assert(owner[idx] == -1);
      owner[idx] = i;
      assert(ctx->edges[idx].assigned == i);
    }
    for (j = 1; j < comp->nodesA.size; ++j) {
      assert(comp->nodesA.data[j - 1] < comp->nodesA.data[j]);
    }
    for (j = 1; j < comp->nodesB.size; ++j) {
      assert(comp->nodesB.data[j - 1] < comp->nodesB.data[j]);
    }
  }
  for (i = 0; i < ctx->edge_count; ++i) {
    int assigned = ctx->edges[i].assigned;
    if (assigned >= 0) {
      assert(owner[i] == assigned);
    } else {
      assert(owner[i] == -1);
    }
  }
  free(owner);
}

static void vec_init(IntVector *v) {
  v->data = NULL;
  v->size = 0;
  v->cap = 0;
}

static void vec_reserve(IntVector *v, int need) {
  if (need > v->cap) {
    int cap = v->cap ? v->cap : 8;
    while (cap < need) {
      cap *= 2;
    }
    v->data = (int *)realloc(v->data, cap * sizeof(int));
    assert(v->data);
    v->cap = cap;
  }
}

static void vec_push(IntVector *v, int value) {
  vec_reserve(v, v->size + 1);
  v->data[v->size++] = value;
}

static void vec_clear(IntVector *v) {
  v->size = 0;
}

static void vec_free(IntVector *v) {
  free(v->data);
  v->data = NULL;
  v->size = 0;
  v->cap = 0;
}

static void component_list_init(ComponentList *list) {
  list->data = NULL;
  list->size = 0;
  list->cap = 0;
}

static void component_list_push(ComponentList *list, ComponentRecord rec) {
  if (list->size == list->cap) {
    int cap = list->cap ? list->cap * 2 : 4;
    list->data = (ComponentRecord *)realloc(list->data, cap * sizeof(ComponentRecord));
    assert(list->data);
    list->cap = cap;
  }
  list->data[list->size++] = rec;
}

static void component_list_free(ComponentList *list) {
  int i;
  for (i = 0; i < list->size; ++i) {
    free(list->data[i].nodesA);
    free(list->data[i].nodesB);
  }
  free(list->data);
  list->data = NULL;
  list->size = 0;
  list->cap = 0;
}

static int cmp_int(const void *a, const void *b) {
  const int lhs = *(const int *)a;
  const int rhs = *(const int *)b;
  return (lhs > rhs) - (lhs < rhs);
}

static int compare_sets(const int *a, int sizeA, const int *b, int sizeB) {
  int i;
  if (sizeA < sizeB) {
    return -1;
  }
  if (sizeA > sizeB) {
    return 1;
  }
  for (i = 0; i < sizeA; ++i) {
    if (a[i] < b[i]) {
      return -1;
    }
    if (a[i] > b[i]) {
      return 1;
    }
  }
  return 0;
}

static int threshold_value(int percent, int count) {
  return (percent * count + 99) / 100;
}

static uint64_t hash_ids(const int *ids, int count) {
  uint64_t h = 1469598103934665603ULL;
  uint64_t prime = 1099511628211ULL;
  int i;
  for (i = 0; i < count; ++i) {
    h ^= (uint64_t)(uint32_t)ids[i] + 0x9e3779b97f4a7c15ULL;
    h *= prime;
  }
  return h;
}

static int binary_search_id(const int *ids, int count, int value) {
  int lo = 0;
  int hi = count - 1;
  while (lo <= hi) {
    int mid = lo + (hi - lo) / 2;
    if (ids[mid] == value) {
      return mid;
    }
    if (ids[mid] < value) {
      lo = mid + 1;
    } else {
      hi = mid - 1;
    }
  }
  return -1;
}

static void graph_free(Graph *g) {
  free(g->offset);
  free(g->neighbors);
  free(g->orig_ids);
  g->offset = NULL;
  g->neighbors = NULL;
  g->orig_ids = NULL;
  g->node_count = 0;
  g->edge_count = 0;
}

static void graph_build(Graph *g, int *pairs, int pair_count) {
  int *ids;
  int id_count = 0;
  int unique_ids = 0;
  int i;
  int edge_capacity;
  int *edges_u;
  int *edges_v;
  int mapped_edges = 0;
  int *degree;
  int *offset;
  int *neighbors;
  int total_adj;
  int *cursor;
  int *new_offsets;
  int write_pos;

  g->node_count = 0;
  g->edge_count = 0;
  g->offset = NULL;
  g->neighbors = NULL;
  g->orig_ids = NULL;

  if (pair_count == 0) {
    g->offset = (int *)calloc(1, sizeof(int));
    assert(g->offset);
    return;
  }

  assert((pair_count & 1) == 0);
  edge_capacity = pair_count / 2;

  ids = (int *)malloc(pair_count * sizeof(int));
  assert(ids);
  edges_u = (int *)malloc(edge_capacity * sizeof(int));
  edges_v = (int *)malloc(edge_capacity * sizeof(int));
  assert(edges_u && edges_v);

  for (i = 0; i < pair_count; i += 2) {
    ids[id_count++] = pairs[i];
    ids[id_count++] = pairs[i + 1];
  }

  qsort(ids, id_count, sizeof(int), cmp_int);
  for (i = 0; i < id_count; ++i) {
    if (i == 0 || ids[i] != ids[i - 1]) {
      ids[unique_ids++] = ids[i];
    }
  }

  g->node_count = unique_ids;
  g->orig_ids = (int *)malloc(unique_ids * sizeof(int));
  assert(g->orig_ids);
  for (i = 0; i < unique_ids; ++i) {
    g->orig_ids[i] = ids[i];
  }

  for (i = 0; i < pair_count; i += 2) {
    int a = pairs[i];
    int b = pairs[i + 1];
    int u = binary_search_id(g->orig_ids, unique_ids, a);
    int v = binary_search_id(g->orig_ids, unique_ids, b);
    if (u == v) {
      continue;
    }
    edges_u[mapped_edges] = u;
    edges_v[mapped_edges] = v;
    mapped_edges++;
  }

  degree = (int *)calloc(unique_ids, sizeof(int));
  assert(degree);
  for (i = 0; i < mapped_edges; ++i) {
    int u = edges_u[i];
    int v = edges_v[i];
    degree[u]++;
    degree[v]++;
  }

  offset = (int *)malloc((unique_ids + 1) * sizeof(int));
  assert(offset);
  offset[0] = 0;
  for (i = 0; i < unique_ids; ++i) {
    offset[i + 1] = offset[i] + degree[i];
  }
  total_adj = offset[unique_ids];
  neighbors = (int *)malloc(total_adj * sizeof(int));
  assert(neighbors);

  cursor = (int *)malloc(unique_ids * sizeof(int));
  assert(cursor);
  memcpy(cursor, offset, unique_ids * sizeof(int));
  for (i = 0; i < mapped_edges; ++i) {
    int u = edges_u[i];
    int v = edges_v[i];
    neighbors[cursor[u]++] = v;
    neighbors[cursor[v]++] = u;
  }
  free(cursor);
  free(edges_u);
  free(edges_v);
  free(degree);

  new_offsets = (int *)malloc((unique_ids + 1) * sizeof(int));
  assert(new_offsets);
  new_offsets[0] = 0;
  write_pos = 0;
  for (i = 0; i < unique_ids; ++i) {
    int start = offset[i];
    int end = offset[i + 1];
    int len = end - start;
    int j;
    if (len > 1) {
      qsort(neighbors + start, len, sizeof(int), cmp_int);
    }
    {
      int last = -1;
      for (j = start; j < end; ++j) {
        int v = neighbors[j];
        if (v == i) {
          continue;
        }
        if (last != -1 && v == last) {
          continue;
        }
        neighbors[write_pos++] = v;
        last = v;
      }
    }
    new_offsets[i + 1] = write_pos;
  }

  free(offset);
  free(ids);

  g->offset = new_offsets;
  g->neighbors = neighbors;
  g->edge_count = write_pos / 2;
}

static int count_edges_to_mark(const Graph *g, int node, const unsigned char *mark) {
  int start = g->offset[node];
  int end = g->offset[node + 1];
  int count = 0;
  int i;
  for (i = start; i < end; ++i) {
    int v = g->neighbors[i];
    if (mark[v]) {
      count++;
    }
  }
  return count;
}

static int component_exists(const ComponentList *list, uint64_t hashA, uint64_t hashB, const int *nodesA, int sizeA, const int *nodesB, int sizeB) {
  int i;
  for (i = 0; i < list->size; ++i) {
    const ComponentRecord *rec = &list->data[i];
    if (rec->sizeA != sizeA || rec->sizeB != sizeB) {
      continue;
    }
    if (rec->hashA != hashA || rec->hashB != hashB) {
      continue;
    }
    if (memcmp(rec->nodesA, nodesA, sizeA * sizeof(int)) != 0) {
      continue;
    }
    if (memcmp(rec->nodesB, nodesB, sizeB * sizeof(int)) != 0) {
      continue;
    }
    return 1;
  }
  return 0;
}

static void detect_components(const Graph *g, int min_con, int min_part, ComponentList *out) {
  unsigned char *markA;
  unsigned char *markB;
  int *counts;
  IntVector setA;
  IntVector setB;
  IntVector touchedA;
  IntVector touchedB;
  IntVector touchedCounts;
  int seed;

  if (g->node_count == 0) {
    return;
  }

  markA = (unsigned char *)calloc(g->node_count, sizeof(unsigned char));
  markB = (unsigned char *)calloc(g->node_count, sizeof(unsigned char));
  counts = (int *)calloc(g->node_count, sizeof(int));
  assert(markA && markB && counts);

  vec_init(&setA);
  vec_init(&setB);
  vec_init(&touchedA);
  vec_init(&touchedB);
  vec_init(&touchedCounts);

  for (seed = 0; seed < g->node_count; ++seed) {
    int start = g->offset[seed];
    int end = g->offset[seed + 1];
    int iter = 0;
    int valid = 1;
    int changed;
    int thresholdA;
    int thresholdB;
    int i;

    if (end - start == 0) {
      continue;
    }

    vec_clear(&setA);
    vec_clear(&setB);
    vec_clear(&touchedA);
    vec_clear(&touchedB);
    vec_clear(&touchedCounts);

    markA[seed] = 1;
    vec_push(&touchedA, seed);
    vec_push(&setA, seed);

    for (i = start; i < end; ++i) {
      int v = g->neighbors[i];
      if (!markB[v]) {
        markB[v] = 1;
        vec_push(&touchedB, v);
        vec_push(&setB, v);
      }
    }

    if (setB.size == 0) {
      goto cleanup_seed;
    }

    while (valid) {
      changed = 0;
      thresholdA = threshold_value(min_con, setB.size);
      if (thresholdA == 0 && setB.size > 0) {
        thresholdA = 1;
      }

      for (i = 0; i < setA.size;) {
        int node = setA.data[i];
        int cnt = count_edges_to_mark(g, node, markB);
        if (cnt < thresholdA) {
          markA[node] = 0;
          setA.data[i] = setA.data[setA.size - 1];
          setA.size--;
          changed = 1;
          continue;
        }
        ++i;
      }

      if (setA.size == 0) {
        valid = 0;
        break;
      }

      thresholdB = threshold_value(min_con, setA.size);
      if (thresholdB == 0 && setA.size > 0) {
        thresholdB = 1;
      }

      for (i = 0; i < setB.size;) {
        int node = setB.data[i];
        int cnt = count_edges_to_mark(g, node, markA);
        if (cnt < thresholdB) {
          markB[node] = 0;
          setB.data[i] = setB.data[setB.size - 1];
          setB.size--;
          changed = 1;
          continue;
        }
        ++i;
      }

      if (setB.size == 0) {
        valid = 0;
        break;
      }

      if (setB.size > 0 && thresholdA > 0) {
        for (i = 0; i < setB.size; ++i) {
          int node = setB.data[i];
          int n;
          for (n = g->offset[node]; n < g->offset[node + 1]; ++n) {
            int v = g->neighbors[n];
            if (markA[v] || markB[v]) {
              continue;
            }
            if (counts[v] == 0) {
              vec_push(&touchedCounts, v);
            }
            counts[v]++;
          }
        }

        for (i = 0; i < touchedCounts.size; ++i) {
          int node = touchedCounts.data[i];
          if (counts[node] >= thresholdA) {
            markA[node] = 1;
            vec_push(&touchedA, node);
            vec_push(&setA, node);
            changed = 1;
          }
          counts[node] = 0;
        }
        vec_clear(&touchedCounts);
      }

      thresholdB = threshold_value(min_con, setA.size);
      if (thresholdB == 0 && setA.size > 0) {
        thresholdB = 1;
      }

      if (setA.size > 0 && thresholdB > 0) {
        for (i = 0; i < setA.size; ++i) {
          int node = setA.data[i];
          int n;
          for (n = g->offset[node]; n < g->offset[node + 1]; ++n) {
            int v = g->neighbors[n];
            if (markA[v] || markB[v]) {
              continue;
            }
            if (counts[v] == 0) {
              vec_push(&touchedCounts, v);
            }
            counts[v]++;
          }
        }

        for (i = 0; i < touchedCounts.size; ++i) {
          int node = touchedCounts.data[i];
          if (counts[node] >= thresholdB) {
            markB[node] = 1;
            vec_push(&touchedB, node);
            vec_push(&setB, node);
            changed = 1;
          }
          counts[node] = 0;
        }
        vec_clear(&touchedCounts);
      }

      if (!changed) {
        break;
      }

      ++iter;
      if (iter > 64) {
        break;
      }
    }

    if (valid && setA.size >= min_part && setB.size >= min_part) {
      int sizeA = setA.size;
      int sizeB = setB.size;
      int64_t edges = 0;
      int *idsA = (int *)malloc(sizeA * sizeof(int));
      int *idsB = (int *)malloc(sizeB * sizeof(int));
      uint64_t hashA;
      uint64_t hashB;

      assert(idsA && idsB);

      for (i = 0; i < sizeA; ++i) {
        int node = setA.data[i];
        edges += count_edges_to_mark(g, node, markB);
        idsA[i] = node;
      }

      for (i = 0; i < sizeB; ++i) {
        idsB[i] = setB.data[i];
      }

      if (edges * 100 >= (int64_t)min_con * sizeA * sizeB) {
        qsort(idsA, sizeA, sizeof(int), cmp_int);
        qsort(idsB, sizeB, sizeof(int), cmp_int);
        if (compare_sets(idsA, sizeA, idsB, sizeB) > 0) {
          int *tmp = idsA;
          int tmp_size = sizeA;
          idsA = idsB;
          idsB = tmp;
          sizeA = sizeB;
          sizeB = tmp_size;
        }
        hashA = hash_ids(idsA, sizeA);
        hashB = hash_ids(idsB, sizeB);
        if (!component_exists(out, hashA, hashB, idsA, sizeA, idsB, sizeB)) {
          ComponentRecord rec;
          rec.sizeA = sizeA;
          rec.sizeB = sizeB;
          rec.nodesA = idsA;
          rec.nodesB = idsB;
          rec.hashA = hashA;
          rec.hashB = hashB;
          component_list_push(out, rec);
        } else {
          free(idsA);
          free(idsB);
        }
      } else {
        free(idsA);
        free(idsB);
      }
    }

cleanup_seed:
    for (i = 0; i < touchedA.size; ++i) {
      markA[touchedA.data[i]] = 0;
    }
    for (i = 0; i < touchedB.size; ++i) {
      markB[touchedB.data[i]] = 0;
    }
    for (i = 0; i < touchedCounts.size; ++i) {
      counts[touchedCounts.data[i]] = 0;
    }
  }

  vec_free(&setA);
  vec_free(&setB);
  vec_free(&touchedA);
  vec_free(&touchedB);
  vec_free(&touchedCounts);
  free(markA);
  free(markB);
  free(counts);
}

static uint64_t make_edge_key(int a, int b) {
  uint32_t ua = (uint32_t)a;
  uint32_t ub = (uint32_t)b;
  if (ua < ub) {
    return ((uint64_t)ua << 32) | (uint64_t)ub;
  }
  return ((uint64_t)ub << 32) | (uint64_t)ua;
}

static int cmp_edge_map(const void *a, const void *b) {
  const EdgeMapEntry *ea = (const EdgeMapEntry *)a;
  const EdgeMapEntry *eb = (const EdgeMapEntry *)b;
  if (ea->key < eb->key) {
    return -1;
  }
  if (ea->key > eb->key) {
    return 1;
  }
  return 0;
}

static int edge_map_find(const EdgeMapEntry *map, int size, int u, int v) {
  uint64_t key = make_edge_key(u, v);
  int lo = 0;
  int hi = size - 1;
  while (lo <= hi) {
    int mid = lo + (hi - lo) / 2;
    if (map[mid].key == key) {
      return map[mid].index;
    }
    if (map[mid].key < key) {
      lo = mid + 1;
    } else {
      hi = mid - 1;
    }
  }
  return -1;
}

static void work_component_init(WorkComponent *comp) {
  vec_init(&comp->nodesA);
  vec_init(&comp->nodesB);
  vec_init(&comp->edges);
  comp->edge_count = 0;
}

static void work_component_free(WorkComponent *comp) {
  vec_free(&comp->nodesA);
  vec_free(&comp->nodesB);
  vec_free(&comp->edges);
  comp->edge_count = 0;
}

static int vector_contains(const IntVector *vec, int value) {
  int lo = 0;
  int hi = vec->size - 1;
  while (lo <= hi) {
    int mid = lo + (hi - lo) / 2;
    int mid_val = vec->data[mid];
    if (mid_val == value) {
      return 1;
    }
    if (mid_val < value) {
      lo = mid + 1;
    } else {
      hi = mid - 1;
    }
  }
  return 0;
}

static void vector_insert_sorted(IntVector *vec, int value) {
  int lo = 0;
  int hi = vec->size;
  while (lo < hi) {
    int mid = lo + (hi - lo) / 2;
    if (vec->data[mid] < value) {
      lo = mid + 1;
    } else {
      hi = mid;
    }
  }
  vec_reserve(vec, vec->size + 1);
  if (lo < vec->size) {
    memmove(&vec->data[lo + 1], &vec->data[lo], (vec->size - lo) * sizeof(int));
  }
  vec->data[lo] = value;
  vec->size++;
}

static EdgeInfo *build_edge_list(const Graph *g, int *out_count) {
  int total = g->edge_count;
  EdgeInfo *edges;
  int idx = 0;
  int u;

  if (total == 0) {
    *out_count = 0;
    return NULL;
  }

  edges = (EdgeInfo *)malloc(total * sizeof(EdgeInfo));
  assert(edges);

  for (u = 0; u < g->node_count; ++u) {
    int start = g->offset[u];
    int end = g->offset[u + 1];
    int i;
    for (i = start; i < end; ++i) {
      int v = g->neighbors[i];
      if (u < v) {
        edges[idx].u = u;
        edges[idx].v = v;
        edges[idx].assigned = -1;
        idx++;
      }
    }
  }

  assert(idx == total);
  *out_count = total;
  return edges;
}

static EdgeMapEntry *build_edge_map(const EdgeInfo *edges, int edge_count) {
  EdgeMapEntry *map;
  int i;
  if (edge_count == 0) {
    return NULL;
  }
  map = (EdgeMapEntry *)malloc(edge_count * sizeof(EdgeMapEntry));
  assert(map);
  for (i = 0; i < edge_count; ++i) {
    map[i].key = make_edge_key(edges[i].u, edges[i].v);
    map[i].index = i;
  }
  qsort(map, edge_count, sizeof(EdgeMapEntry), cmp_edge_map);
  return map;
}

static int collect_edge_candidate(const EdgeInfo *edges, EdgeMapEntry *map, int map_size, int u, int v, int comp_idx, IntVector *list, int *assigned) {
  int idx = edge_map_find(map, map_size, u, v);
  if (idx < 0) {
    return 0;
  }
  if (edges[idx].assigned == comp_idx) {
    return 0;
  }
  if (edges[idx].assigned != -1) {
    return 0;
  }
  vec_push(list, idx);
  (*assigned)++;
  return 1;
}

static int evaluate_orientation(const EdgeInfo *edges, EdgeMapEntry *map, int map_size, WorkComponent *comp, int comp_idx, int nodeA, int nodeB, int min_con, IntVector *tmp_edges, int *addA, int *addB, int *num, int *den) {
  int inA = vector_contains(&comp->nodesA, nodeA);
  int inB = vector_contains(&comp->nodesB, nodeB);
  int add_u = inA ? 0 : 1;
  int add_v = inB ? 0 : 1;
  int new_sizeA;
  int new_sizeB;
  int new_edges = 0;
  int numerator;

  if (!inA && vector_contains(&comp->nodesB, nodeA)) {
    return 0;
  }
  if (!inB && vector_contains(&comp->nodesA, nodeB)) {
    return 0;
  }

  new_sizeA = comp->nodesA.size + add_u;
  new_sizeB = comp->nodesB.size + add_v;
  if (new_sizeA == 0 || new_sizeB == 0) {
    return 0;
  }

  vec_clear(tmp_edges);

  if (add_u) {
    int i;
    for (i = 0; i < comp->nodesB.size; ++i) {
      collect_edge_candidate(edges, map, map_size, nodeA, comp->nodesB.data[i], comp_idx, tmp_edges, &new_edges);
    }
  }

  if (add_v) {
    int i;
    for (i = 0; i < comp->nodesA.size; ++i) {
      collect_edge_candidate(edges, map, map_size, comp->nodesA.data[i], nodeB, comp_idx, tmp_edges, &new_edges);
    }
  }

  if (add_u && add_v) {
    collect_edge_candidate(edges, map, map_size, nodeA, nodeB, comp_idx, tmp_edges, &new_edges);
  }

  if (!add_u && !add_v) {
    collect_edge_candidate(edges, map, map_size, nodeA, nodeB, comp_idx, tmp_edges, &new_edges);
  }

  numerator = comp->edge_count + new_edges;
  *den = new_sizeA * new_sizeB;
  *num = numerator;

  if ((int64_t)numerator * 100 < (int64_t)min_con * (*den)) {
    return 0;
  }

  *addA = add_u;
  *addB = add_v;
  return 1;
}

static void assign_edges_to_component(EdgeInfo *edges, WorkComponent *comp, IntVector *edge_indices, int comp_idx) {
  int i;
  for (i = 0; i < edge_indices->size; ++i) {
    int idx = edge_indices->data[i];
    edges[idx].assigned = comp_idx;
    vec_push(&comp->edges, idx);
    comp->edge_count++;
  }
}

static int compare_core_desc(const void *a, const void *b) {
  const ComponentRecord *ra = (const ComponentRecord *)a;
  const ComponentRecord *rb = (const ComponentRecord *)b;
  int64_t ea = (int64_t)ra->sizeA * (int64_t)ra->sizeB;
  int64_t eb = (int64_t)rb->sizeA * (int64_t)rb->sizeB;
  if (ea > eb) {
    return -1;
  }
  if (ea < eb) {
    return 1;
  }
  return 0;
}

static void build_core_components(EdgeInfo *edges, EdgeMapEntry *map, int map_size, int min_part_size, ComponentList *cores, WorkComponent **out_components, int *out_count) {
  WorkComponent *components;
  int comp_count = 0;
  int capacity = 4;
  int i;

  components = (WorkComponent *)malloc(capacity * sizeof(WorkComponent));
  assert(components);

  for (i = 0; i < cores->size; ++i) {
    ComponentRecord *rec = &cores->data[i];
    int ok = 1;
    int a;
    if (rec->sizeA < min_part_size || rec->sizeB < min_part_size) {
      continue;
    }
    for (a = 0; a < rec->sizeA && ok; ++a) {
      int b;
      for (b = 0; b < rec->sizeB; ++b) {
        int idx = edge_map_find(map, map_size, rec->nodesA[a], rec->nodesB[b]);
        if (idx < 0 || edges[idx].assigned != -1) {
          ok = 0;
          break;
        }
      }
    }
    if (!ok) {
      continue;
    }
    if (comp_count == capacity) {
      capacity *= 2;
      components = (WorkComponent *)realloc(components, capacity * sizeof(WorkComponent));
      assert(components);
    }
    work_component_init(&components[comp_count]);
    for (a = 0; a < rec->sizeA; ++a) {
      vector_insert_sorted(&components[comp_count].nodesA, rec->nodesA[a]);
    }
    for (a = 0; a < rec->sizeB; ++a) {
      vector_insert_sorted(&components[comp_count].nodesB, rec->nodesB[a]);
    }
    {
      int ai;
      for (ai = 0; ai < rec->sizeA; ++ai) {
        int bi;
        for (bi = 0; bi < rec->sizeB; ++bi) {
          int idx = edge_map_find(map, map_size, rec->nodesA[ai], rec->nodesB[bi]);
          assert(idx >= 0 && edges[idx].assigned == -1);
          edges[idx].assigned = comp_count;
          vec_push(&components[comp_count].edges, idx);
          components[comp_count].edge_count++;
        }
      }
    }
    comp_count++;
  }

  *out_components = components;
  *out_count = comp_count;
}

static void expand_components(EdgeInfo *edges, EdgeMapEntry *map, int map_size, WorkComponent *components, int comp_count, int edge_count, int min_con_value) {
  IntVector tmp_edges;
  IntVector best_edges;
  int progress = 1;

  vec_init(&tmp_edges);
  vec_init(&best_edges);

  while (progress) {
    int e;
    progress = 0;
    for (e = 0; e < edge_count; ++e) {
      int u;
      int v;
      int best_comp = -1;
      int best_addA = 0;
      int best_addB = 0;
      int best_num = 0;
      int best_den = 1;
      int best_nodeA = -1;
      int best_nodeB = -1;
      int comp_idx;

      if (edges[e].assigned != -1) {
        continue;
      }
      u = edges[e].u;
      v = edges[e].v;
      vec_clear(&best_edges);

      for (comp_idx = 0; comp_idx < comp_count; ++comp_idx) {
        WorkComponent *comp = &components[comp_idx];
        int addA;
        int addB;
        int num;
        int den;
        if (evaluate_orientation(edges, map, map_size, comp, comp_idx, u, v, min_con_value, &tmp_edges, &addA, &addB, &num, &den)) {
          int better = 0;
          if ((int64_t)num * best_den > (int64_t)best_num * den) {
            better = 1;
          } else if ((int64_t)num * best_den == (int64_t)best_num * den && num > best_num) {
            better = 1;
          }
          if (better) {
            best_comp = comp_idx;
            best_addA = addA;
            best_addB = addB;
            best_num = num;
            best_den = den;
            best_nodeA = u;
            best_nodeB = v;
            vec_clear(&best_edges);
            vec_reserve(&best_edges, tmp_edges.size);
            memcpy(best_edges.data, tmp_edges.data, tmp_edges.size * sizeof(int));
            best_edges.size = tmp_edges.size;
          }
        }
        if (evaluate_orientation(edges, map, map_size, comp, comp_idx, v, u, min_con_value, &tmp_edges, &addA, &addB, &num, &den)) {
          int better = 0;
          if ((int64_t)num * best_den > (int64_t)best_num * den) {
            better = 1;
          } else if ((int64_t)num * best_den == (int64_t)best_num * den && num > best_num) {
            better = 1;
          }
          if (better) {
            best_comp = comp_idx;
            best_addA = addA;
            best_addB = addB;
            best_num = num;
            best_den = den;
            best_nodeA = v;
            best_nodeB = u;
            vec_clear(&best_edges);
            vec_reserve(&best_edges, tmp_edges.size);
            memcpy(best_edges.data, tmp_edges.data, tmp_edges.size * sizeof(int));
            best_edges.size = tmp_edges.size;
          }
        }
      }

      if (best_comp != -1) {
        WorkComponent *comp = &components[best_comp];
        if (best_addA && !vector_contains(&comp->nodesA, best_nodeA)) {
          vector_insert_sorted(&comp->nodesA, best_nodeA);
        }
        if (best_addB && !vector_contains(&comp->nodesB, best_nodeB)) {
          vector_insert_sorted(&comp->nodesB, best_nodeB);
        }
        assign_edges_to_component(edges, comp, &best_edges, best_comp);
        progress = 1;
      }
    }
  }

  vec_free(&tmp_edges);
  vec_free(&best_edges);
}

static SolverContext * solver_run(int *pairs, int pair_count, int min_con_value, int min_part_size) {
  SolverContext *ctx;
  ComponentList cores;
  ctx = (SolverContext *)calloc(1, sizeof(SolverContext));
  assert(ctx);

  graph_build(&ctx->graph, pairs, pair_count);
  ctx->edges = build_edge_list(&ctx->graph, &ctx->edge_count);
  ctx->edge_map = build_edge_map(ctx->edges, ctx->edge_count);

  component_list_init(&cores);
  detect_components(&ctx->graph, 100, min_part_size, &cores);
  if (cores.size > 1) {
    qsort(cores.data, cores.size, sizeof(ComponentRecord), compare_core_desc);
  }
  build_core_components(ctx->edges, ctx->edge_map, ctx->edge_count, min_part_size, &cores, &ctx->components, &ctx->component_count);
  expand_components(ctx->edges, ctx->edge_map, ctx->edge_count, ctx->components, ctx->component_count, ctx->edge_count, min_con_value);
  validate_edge_ownership(ctx);

  component_list_free(&cores);
  return ctx;
}

static int * solver_build_result_array(const SolverContext *ctx) {
  int total_sets = ctx->component_count * 2;
  int total_ints = 1;
  int *result;
  int offset = 1;
  int c;

  for (c = 0; c < ctx->component_count; ++c) {
    total_ints += 1 + ctx->components[c].nodesA.size;
    total_ints += 1 + ctx->components[c].nodesB.size;
  }

  result = (int *)malloc(total_ints * sizeof(int));
  assert(result);
  result[0] = total_sets;

  for (c = 0; c < ctx->component_count; ++c) {
    int i;
    result[offset++] = ctx->components[c].nodesA.size;
    for (i = 0; i < ctx->components[c].nodesA.size; ++i) {
      int node = ctx->components[c].nodesA.data[i];
      result[offset++] = ctx->graph.orig_ids[node];
    }
    result[offset++] = ctx->components[c].nodesB.size;
    for (i = 0; i < ctx->components[c].nodesB.size; ++i) {
      int node = ctx->components[c].nodesB.data[i];
      result[offset++] = ctx->graph.orig_ids[node];
    }
  }

  return result;
}

static void solver_free_context(SolverContext *ctx) {
  int i;
  if (!ctx) {
    return;
  }
  for (i = 0; i < ctx->component_count; ++i) {
    work_component_free(&ctx->components[i]);
  }
  free(ctx->components);
  free(ctx->edges);
  free(ctx->edge_map);
  graph_free(&ctx->graph);
  free(ctx);
}

static void print_components(const SolverContext *ctx) {
  int c;
  if (ctx->component_count == 0) {
    printf("The number of components found is 0.\n");
    return;
  }
  printf("The number of components found is %d:\n", ctx->component_count);
  for (c = 0; c < ctx->component_count; ++c) {
    const WorkComponent *comp = &ctx->components[c];
    int i;
    printf("Component %d:\n", c + 1);
    printf("  { ");
    for (i = 0; i < comp->nodesA.size; ++i) {
      printf("%d ", ctx->graph.orig_ids[comp->nodesA.data[i]]);
    }
    printf("}\n");
    printf("  { ");
    for (i = 0; i < comp->nodesB.size; ++i) {
      printf("%d ", ctx->graph.orig_ids[comp->nodesB.data[i]]);
    }
    printf("}\n");

    printf("      ");
    for (i = 0; i < comp->nodesA.size; ++i) {
      printf("%6d", ctx->graph.orig_ids[comp->nodesA.data[i]]);
    }
    printf("\n");
    {
      int row;
      for (row = 0; row < comp->nodesB.size; ++row) {
        int nodeB = comp->nodesB.data[row];
        int col;
        printf("%6d", ctx->graph.orig_ids[nodeB]);
        for (col = 0; col < comp->nodesA.size; ++col) {
          int nodeA = comp->nodesA.data[col];
          int idx = edge_map_find(ctx->edge_map, ctx->edge_count, nodeA, nodeB);
          int mark = 0;
          if (idx >= 0 && ctx->edges[idx].assigned == c) {
            mark = 1;
          }
          printf("%6c", mark ? 'x' : ' ');
        }
        printf("\n");
      }
    }
    printf("\n");
  }
}

int * compute_bipartite_subgraphs(int *pArray, int nSize, int min_con_value, int min_part_size, int fVerbose) {
  SolverContext *ctx = solver_run(pArray, nSize, min_con_value, min_part_size);
  int *result = solver_build_result_array(ctx);
  if ( fVerbose ) print_components(ctx);
  solver_free_context(ctx);
  return result;
}

/*

static int * read_edge_list(const char *filename, int *out_size) {
  FILE *fp = fopen(filename, "r");
  int capacity = 1024;
  int count = 0;
  int value;
  int *data;
  assert(fp);

  data = (int *)malloc(capacity * sizeof(int));
  assert(data);
  while (fscanf(fp, "%d", &value) == 1) {
    if (count == capacity) {
      capacity *= 2;
      data = (int *)realloc(data, capacity * sizeof(int));
      assert(data);
    }
    data[count++] = value;
  }
  fclose(fp);
  assert((count & 1) == 0);
  *out_size = count;
  return data;
}

static void usage(void) {
  printf("Usage: bipart <min_con_value> <min_part_size> <filename>\n");
  printf("   or: bipart -C <min_con_value> -M <min_part_size> <filename>\n");
}

int main(int argc, char **argv) {
  int min_con_value = 0;
  int min_part_size = 0;
  const char *filename = NULL;
  int i;
  int *edges_data;
  int edge_count;
  SolverContext *ctx;
  clock_t start;
  clock_t end;
  double seconds;
  int *result_array;

  if (argc == 4) {
    min_con_value = atoi(argv[1]);
    min_part_size = atoi(argv[2]);
    filename = argv[3];
  } else {
    for (i = 1; i < argc; ++i) {
      if (strcmp(argv[i], "-C") == 0 && i + 1 < argc) {
        min_con_value = atoi(argv[++i]);
      } else if (strcmp(argv[i], "-M") == 0 && i + 1 < argc) {
        min_part_size = atoi(argv[++i]);
      } else if (argv[i][0] != '-') {
        filename = argv[i];
      }
    }
  }

  if (!filename || min_con_value < 50 || min_con_value > 100 || min_part_size <= 0) {
    usage();
    return 1;
  }

  printf("Computing bi-partite components of the graph \"%s\".\n", filename);
  printf("Assuming minimum connectivity %d%%.\n", min_con_value);
  printf("Assuming minimum partition size %d nodes.\n\n", min_part_size);

  edges_data = read_edge_list(filename, &edge_count);

  start = clock();
  ctx = solver_run(edges_data, edge_count, min_con_value, min_part_size);
  end = clock();
  seconds = (double)(end - start) / (double)CLOCKS_PER_SEC;

  printf("The problem is solved in %.2f sec.\n\n", seconds);

  print_components(ctx);

  result_array = solver_build_result_array(ctx);
  free(result_array);

  solver_free_context(ctx);
  free(edges_data);
  return 0;
}
*/

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

