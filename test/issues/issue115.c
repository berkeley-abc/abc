#include "sat/bsat/satSolver.h"
ABC_NAMESPACE_USING_NAMESPACE
#define CHECK(c) do { if (!(c)) { fprintf(stderr, "Failed at line %d\n", __LINE__); return 1; } } while (0)

static int TestPages(void)
{
    Sat_Mem_t m, *pMem = &m;
    clause *c;
    int ids[400], handles[400], sizes[400], nKeep, nPrefix, round, j, i, k, h;
    for (round = 0; round < 8; round++)
    {
        Sat_MemAlloc_(&m, 9);
        Sat_MemAppend(&m, NULL, 2, 0, 0); /* reserved binary clause */
        nKeep = nPrefix = 0;
        for (j = 0; j < 400; j++)
        {
            int size = j < 20 ? 500 + j : (j % 3 ? 3 + j % 25 : 510 + j * 7);
            if (j == 121) Sat_MemBookMark(&m);
            h = Sat_MemAppend(&m, NULL, size, 1, 0);
            c = Sat_MemClauseHand(&m, h);
            for (k = 0; k < size; k++) c->lits[k] = 10000*j + k;
            c->mark = (j + round) % 4 == 0;
            if (!c->mark)
            {
                ids[nKeep] = j; sizes[nKeep++] = size;
                nPrefix += j < 121;
            }
        }
        CHECK(Sat_MemCountL(&m) == 400);
        CHECK(Sat_MemCompactLearned(&m, 0) == nKeep);
        j = 0;
        Sat_MemForEachLearned(pMem, c, i, k)
            if (!c->mark) handles[j++] = clause_id(c);
        CHECK(j == nKeep);
        CHECK(Sat_MemCompactLearned(&m, 1) == nKeep);
        j = 0;
        Sat_MemForEachLearned(pMem, c, i, k)
        {
            int t;
            CHECK(j < nKeep && (int)c->size == sizes[j]);
            CHECK(c == Sat_MemClauseHand(&m, handles[j]));
            CHECK(clause_id(c) == j);
            for (t = 0; t < sizes[j]; t++) CHECK(c->lits[t] == 10000*ids[j] + t);
            j++;
        }
        CHECK(j == nKeep);
        Sat_MemRollBack(&m);
        CHECK(Sat_MemCountL(&m) == nPrefix);
        h = Sat_MemAppend(&m, NULL, 4096, 1, 0);
        CHECK(Sat_MemClauseHand(&m, h)->size == 4096);
        Sat_MemRestart(&m);
        CHECK(Sat_MemCountL(&m) == 0);
        Sat_MemAppend(&m, NULL, 2, 0, 0);
        for (j = 0; j < 4; j++)
            Sat_MemAppend(&m, NULL, 1000+j, 0, 1);
        j = 0;
        Sat_MemForEachClause2(pMem, c, i, k) { CHECK(c->size == 1000+j); j++; }
        CHECK(j == 4);
        Sat_MemFree_(&m);
    }
    return 0;
}

static int TestSolver(int n)
{
    sat_solver *s = sat_solver_new();
    int *lits = ABC_ALLOC(int, n), i, result;
    sat_solver_setnvars(s, n);
    /* Binary equalities propagate all inputs before scanning the long clause. */
    for (i = 1; i < n; i++)
    {
        int pair[2] = { toLit(0), lit_neg(toLit(i)) };
        CHECK(sat_solver_addclause(s, pair, pair+2));
        pair[0] = lit_neg(toLit(0)); pair[1] = toLit(i);
        CHECK(sat_solver_addclause(s, pair, pair+2));
    }
    for (i = 0; i < n; i++) lits[i] = toLit(i);
    CHECK(sat_solver_addclause(s, lits, lits+n));
    result = sat_solver_solve(s, lits, lits+1, 0, 0, 0, 0);
    CHECK(result == l_True && sat_solver_var_value(s, n-1) == 1);
    lits[0] = lit_neg(toLit(0));
    result = sat_solver_solve(s, lits, lits+1, 0, 0, 0, 0);
    CHECK(result == l_False);
    result = sat_solver_solve(s, NULL, NULL, 0, 0, 0, 0);
    CHECK(result == l_True);
    sat_solver_delete(s);
    ABC_FREE(lits);
    return 0;
}
int main(void)
{
    CHECK(TestPages() == 0);
    CHECK(TestSolver(131065) == 0);
    CHECK(TestSolver(131072) == 0);
    CHECK(TestSolver(300000) == 0);
    puts("PASS: Issue #115 (large clauses, compaction, rollback, SAT/UNSAT)");
    return 0;
}
