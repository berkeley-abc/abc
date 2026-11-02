// Command-owned Strict SEQ wall budget. CBS, discovery and ODC are outside it.
// A deadline is cooperative: one unroll/replay/cleanup can cross it. It never
// turns a partial inductive closure into a certificate.
typedef struct Cec_TranSeqBudget_t_ {
    int Milliseconds, Exhausted, Running, Aborted;
    int Calls, Skipped, AbortedCalls;
    long long Proved, Known, Unknown;
    abctime Limit, Spent, Started, Deadline;
} Cec_TranSeqBudget_t;
static Cec_TranSeqBudget_t * Cec_TranSeqBudgetCurrent = NULL;

static Cec_TranSeqBudget_t Cec_TranSeqBudgetStart( int Milliseconds )
{
    Cec_TranSeqBudget_t b;
    memset(&b, 0, sizeof(b));
    b.Milliseconds = Milliseconds;
    b.Limit = (abctime)Milliseconds * CLOCKS_PER_SEC / 1000;
    return b;
}

static int Cec_TranSeqBudgetRead()
{
    char const * s = getenv("ABC_SRESUB_SEQ_BUDGET_MS");
    char const * p;
    long long value = 0;
    if ( !s || !strcmp(s, "-1") ) return -1;
    if ( !*s ) goto invalid;
    for ( p = s; *p; ++p )
    {
        if ( *p < '0' || *p > '9' ) goto invalid;
        value = value * 10 + (*p - '0');
        if ( value > INT_MAX ) goto invalid;
    }
    return (int)value;
invalid:
    Abc_Print(-1, "ABC_SRESUB_SEQ_BUDGET_MS must be -1 or an integer in [0, INT_MAX]\n");
    exit(2); return -1;
}

static int Cec_TranSeqBudgetBegin()
{
    Cec_TranSeqBudget_t * b = Cec_TranSeqBudgetCurrent;
    if ( !b ) return 1;
    assert(!b->Running);
    if ( b->Exhausted || b->Spent >= b->Limit )
    {
        b->Exhausted = 1; ++b->Skipped; return 0;
    }
    b->Started = Abc_Clock();
    b->Deadline = b->Started + (b->Limit - b->Spent);
    b->Running = 1; b->Aborted = 0; ++b->Calls;
    return 1;
}

static int Cec_TranSeqBudgetStop()
{
    Cec_TranSeqBudget_t * b = Cec_TranSeqBudgetCurrent;
    if ( !b || !b->Running ) return 0;
    if ( !b->Exhausted && Abc_Clock() < b->Deadline ) return 0;
    b->Exhausted = b->Aborted = 1;
    return 1;
}

static void Cec_TranSeqBudgetSetSolver( sat_solver * s )
{
    Cec_TranSeqBudget_t * b = Cec_TranSeqBudgetCurrent;
    if ( b && b->Running ) sat_solver_set_runtime_limit(s, b->Deadline);
}

static void Cec_TranSeqBudgetEnd( Vec_Int_t * Status )
{
    Cec_TranSeqBudget_t * b = Cec_TranSeqBudgetCurrent;
    int i, value;
    if ( !b ) return;
    if ( b->Running )
    {
        b->Spent += Abc_Clock() - b->Started;
        b->Exhausted |= b->Spent >= b->Limit;
        b->AbortedCalls += b->Aborted;
        b->Running = 0;
    }
    Vec_IntForEachEntry(Status, value, i)
    {
        b->Proved += value == 1;
        b->Known += value == 1 && Cec_TranRelClosedKnown(i);
        b->Unknown += value < 0;
    }
}

static Vec_Int_t * Cec_TranSeqBudgetUnproved( int n )
{
    Vec_Int_t * Status = Vec_IntStart(n);
    int i;
    for ( i = 0; i < n; ++i )
        Vec_IntWriteEntry(Status, i, Cec_TranRelClosedKnown(i) ? 1 : -1);
    return Status;
}

static void Cec_TranSeqBudgetPrint( Cec_TranSeqBudget_t * b )
{
    Abc_Print(1, "sresub-seq-budget profile: schema=1 scope=command budget-ms=%d spent-ms=%.3f calls=%d skipped=%d aborted=%d exhausted=%d proved=%lld known=%lld unknown=%lld\n",
        b->Milliseconds, 1000.0*b->Spent/CLOCKS_PER_SEC, b->Calls,
        b->Skipped, b->AbortedCalls, b->Exhausted, b->Proved, b->Known, b->Unknown);
}
