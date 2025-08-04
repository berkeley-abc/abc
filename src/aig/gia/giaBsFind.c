/**CFile****************************************************************

  FileName    [giaBsFind.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaBsFind.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

// Cost function: sum of squared differences between all pairs
int cost_sum_squares(int* subset, int K, void * pData) {
    double cost = 0;
    for (int i = 0; i < K - 1; i++) {
        for (int j = i + 1; j < K; j++) {
            int diff = subset[i] - subset[j];
            cost += diff * diff;
        }
    }
    // Normalize to be between 2 and 100
    return (int)(2.0 + (cost / (K * K)) * 0.98);
}

// Compare function for qsort - for sorting individual subsets
int compare_ints(const void* a, const void* b) {
    return *(int*)a - *(int*)b;
}

// Compare function for qsort - for sorting subsets by cost
// Subset format: [K, element1, element2, ..., elementK, cost]
int compare_subsets_by_cost(const void* a, const void* b) {
    const int* subset_a = (const int*)a;
    const int* subset_b = (const int*)b;
    int K_a = subset_a[0];
    int K_b = subset_b[0];
    assert( K_a == K_b );
    // Cost is at position K+1 (after K and K elements)
    return subset_a[K_a + 1] - subset_b[K_b + 1];
}

// Generate a random subset of K numbers from 0 to N-1
// Format: [K, element1, element2, ..., elementK, cost]
void generate_random_subset(int* subset, int K, int N) {
    subset[0] = K;  // Store K in first position
    int count = 0;
    
    // First, generate K unique random numbers
    while (count < K) {
        int num = rand() % N;
        
        // Check if number already exists in subset
        int exists = 0;
        for (int i = 0; i < count; i++) {
            if (subset[i + 1] == num) {
                exists = 1;
                break;
            }
        }
        
        if (!exists) {
            subset[count + 1] = num;
            count++;
        }
    }
    
    // Then, sort the subset using bubble sort
    for (int i = 1; i < K; i++) {
        for (int j = 1; j < K - i + 1; j++) {
            if (subset[j] > subset[j + 1]) {
                int temp = subset[j];
                subset[j] = subset[j + 1];
                subset[j + 1] = temp;
            }
        }
    }
}

// Create offspring from two parent subsets
// Uses pre-allocated arrays to avoid repeated memory allocation
void create_offspring(int* parent1, int* parent2, int* offspring, int K, int N,
                     int* in_offspring, int* in_parent1, int* in_parent2, int* candidates) {
    int count = 0;
    offspring[0] = K;  // Store K in first position
    
    // Mark which numbers are in each parent (skip first element which is K)
    for (int i = 1; i <= K; i++) {
        in_parent1[parent1[i]] = 1;
        in_parent2[parent2[i]] = 1;
    }
    
    // First, add numbers that appear in both parents
    for (int i = 0; i < N && count < K; i++) {
        if (in_parent1[i] && in_parent2[i]) {
            offspring[count + 1] = i;
            count++;
            in_offspring[i] = 1;
        }
    }
    
    // Create array of numbers that appear in exactly one parent
    int num_candidates = 0;
    
    for (int i = 0; i < N; i++) {
        if ((in_parent1[i] || in_parent2[i]) && !in_offspring[i]) {
            candidates[num_candidates++] = i;
        }
    }
    
    // Randomly add from candidates until we have K numbers
    while (count < K && num_candidates > 0) {
        int idx = rand() % num_candidates;
        offspring[count + 1] = candidates[idx];
        count++;
        in_offspring[candidates[idx]] = 1;
        
        // Remove selected candidate
        candidates[idx] = candidates[--num_candidates];
    }
    
    // Sort the offspring elements (not including the first K value)
    qsort(&offspring[1], K, sizeof(int), compare_ints);
    
    // Clean up the intean arrays for next use - only clean used entries
    for (int i = 1; i <= K; i++) {
        in_parent1[parent1[i]] = 0;
        in_parent2[parent2[i]] = 0;
    }
    for (int i = 1; i <= K; i++) {
        in_offspring[offspring[i]] = 0;
    }
}

// Count unique subsets in a sorted array of subsets
// Returns the number of unique subsets and prints the percentage
int count_unique_subsets(int* sorted_subsets, int num_subsets, int subset_size, const char* label) {
    if (num_subsets == 0) return 0;
    
    int unique_count = 1;  // First subset is always unique
    int K = sorted_subsets[0];  // Get K from first subset
    
    // Compare each subset with the previous one
    for (int i = 1; i < num_subsets; i++) {
        int* current = &sorted_subsets[i * subset_size];
        int* previous = &sorted_subsets[(i - 1) * subset_size];
        
        // Compare all K elements (skip position 0 which has K, and K+1 which has cost)
        int is_different = 0;
        for (int j = 1; j <= K; j++) {
            if (current[j] != previous[j]) {
                is_different = 1;
                break;
            }
        }
        
        if (is_different) {
            unique_count++;
        }
    }
    
    double percentage = (unique_count * 100.0) / num_subsets;
    printf("%s: %d unique subsets out of %d (%.1f%%)\n", 
           label, unique_count, num_subsets, percentage);
    
    return unique_count;
}

// Main genetic algorithm
int genetic_subset_selection(int N, int K, int B, int L, 
                           int verbose,
                           int (*cost_function)(int*, int, void *),
                           int** best_subsets_history,
                           int* iterations_used,
                           void * pUserData) {
    int print_unique = 0;
    int M = B * (B - 1) / 2;
    int subset_size = K + 2;  // K value + K elements + cost
    
    // Allocate arrays
    int* current_generation = (int*)malloc(M * subset_size * sizeof(int));
    int* next_generation = (int*)malloc(M * subset_size * sizeof(int));
    int* all_best_subsets = (int*)calloc(B * L * subset_size, sizeof(int));
    
    // Pre-allocate reusable arrays for create_offspring
    int* in_offspring = (int*)calloc(N, sizeof(int));
    int* in_parent1 = (int*)calloc(N, sizeof(int));
    int* in_parent2 = (int*)calloc(N, sizeof(int));
    int* candidates = (int*)malloc(K * 2 * sizeof(int));
    
    // Generate initial population
    for (int i = 0; i < M; i++) {
        int* subset = &current_generation[i * subset_size];
        generate_random_subset(subset, K, N);
        // Cost function uses elements starting at position 1
        subset[K + 1] = cost_function(&subset[1], K, pUserData);
    }
    
    // Sort to get best B subsets
    qsort(current_generation, M, subset_size * sizeof(int), compare_subsets_by_cost);
    if ( print_unique ) count_unique_subsets(current_generation, M, subset_size, "Initial population");
    
    int best_cost = current_generation[K + 1];
    int generation = 0;
    int total_best_count = 0;
    
    // Main evolutionary loop
    while (generation < L) {
        // Store best B subsets from current generation
        for (int i = 0; i < B && total_best_count < B * L; i++) {
            memcpy(&all_best_subsets[total_best_count * subset_size],
                   &current_generation[i * subset_size],
                   subset_size * sizeof(int));
            total_best_count++;
        }

        if ( verbose ) {
            printf( "Iter %d\n", generation );
            for (int i = 0; i < B; i++ ) {
                printf( "Subset %2d : {", i );
                for (int k = 0; k < K; k++ )
                    printf( " %2d", (&current_generation[i * subset_size])[k+1] );
                printf( " }  " );
                printf( "Cost %2d\n", (&current_generation[i * subset_size])[K+1] );
            }
        }
        
        // Create next generation from pairs of best B subsets
        int offspring_idx = 0;
        for (int i = 0; i < B; i++) {
            for (int j = i + 1; j < B; j++) {
                int* parent1 = &current_generation[i * subset_size];
                int* parent2 = &current_generation[j * subset_size];
                int* offspring = &next_generation[offspring_idx * subset_size];
                
                create_offspring(parent1, parent2, offspring, K, N,
                               in_offspring, in_parent1, in_parent2, candidates);
                offspring[K + 1] = cost_function(&offspring[1], K, pUserData);
                offspring_idx++;
            }
        }
        
        // Sort next generation
        qsort(next_generation, M, subset_size * sizeof(int), compare_subsets_by_cost);
        if ( print_unique ) count_unique_subsets(next_generation, M, subset_size, "Next generation");
        
        generation++;
        
        // Check for improvement
        int new_best_cost = next_generation[K + 1];
        if (new_best_cost >= best_cost) {
            break; // No improvement
        }
        
        best_cost = new_best_cost;
        
        // Swap generations
        int* temp = current_generation;
        current_generation = next_generation;
        next_generation = temp;
    }
    
    // Sort all best subsets collected using qsort
    qsort(all_best_subsets, total_best_count, subset_size * sizeof(int), compare_subsets_by_cost);
    if ( print_unique ) count_unique_subsets(all_best_subsets, total_best_count, subset_size, "All best subsets");
      
    if ( verbose ) {
        printf( "Final best\n" );
        for (int i = 0; i < B; i++ ) {
            printf( "Subset %2d : {", i );
            for (int k = 0; k < K; k++ )
                printf( " %2d", (&all_best_subsets[i * subset_size])[k+1] );
            printf( " }  " );
            printf( "Cost %2d\n", (&all_best_subsets[i * subset_size])[K+1] );
        }
    }
    
    // Free pre-allocated arrays
    free(in_offspring);
    free(in_parent1);
    free(in_parent2);
    free(candidates);
    
    // Return results
    if (best_subsets_history != NULL) {
        *best_subsets_history = all_best_subsets;
    } else {
        free(all_best_subsets);
    }
    
    if (iterations_used != NULL) {
        *iterations_used = generation + 1;
    }
    
    free(current_generation);
    free(next_generation);
    
    return best_cost;
}

// Test bench
/*
int bs_find_test() {
    srand(time(NULL));
    
    // Test parameters
    int N = 30;  // Total numbers (0 to 29)
    int K = 6;   // Subset size
    int B = 10;  // Number of best subsets to keep
    int L = 50;  // Maximum iterations
    
    printf("Genetic Algorithm for Subset Selection\n");
    printf("======================================\n");
    printf("Parameters:\n");
    printf("  N (total numbers): %d\n", N);
    printf("  K (subset size): %d\n", K);
    printf("  B (best subsets): %d\n", B);
    printf("  L (max iterations): %d\n", L);
    printf("\n");
    
    // Run the algorithm
    int* best_subsets_history = NULL;
    int iterations_used = 0;
    int best_cost = genetic_subset_selection(N, K, B, L, 0,
                                           cost_sum_squares, 
                                           &best_subsets_history,
                                           &iterations_used);
    
    printf("Best cost found: %d\n", best_cost);
    printf("Iterations until convergence: %d\n\n", iterations_used);
    
    // Display top 5 best subsets
    printf("Top 5 best subsets:\n");
    int subset_size = K + 2;
    for (int i = 0; i < 5 && i < B * L; i++) {
        int* subset = &best_subsets_history[i * subset_size];
        if (subset[K + 1] == 0) break;  // Check if cost is 0 (uninitialized)
        
        printf("Subset %d: {", i + 1);
        for (int j = 1; j <= K; j++) {
            printf("%d", subset[j]);
            if (j < K) printf(", ");
        }
        printf("} - Cost: %d\n", subset[K + 1]);
    }
    
    // Test with different parameters
    printf("\n\nTesting with different parameters:\n");
    printf("==================================\n");
    
    // Test 1: Smaller problem
    N = 20; K = 4; B = 6; L = 30;
    free(best_subsets_history);
    best_subsets_history = NULL;
    iterations_used = 0;
    
    best_cost = genetic_subset_selection(N, K, B, L, 0,
                                       cost_sum_squares, 
                                       &best_subsets_history,
                                       &iterations_used);
    
    printf("\nTest 1 - N=%d, K=%d, B=%d, L=%d\n", N, K, B, L);
    printf("Best cost: %d\n", best_cost);
    printf("Iterations until convergence: %d\n", iterations_used);
    printf("Best subset: {");
    for (int j = 1; j <= K; j++) {
        printf("%d", best_subsets_history[j]);
        if (j < K) printf(", ");
    }
    printf("}\n");
    
    // Test 2: Larger problem
    N = 50; K = 8; B = 15; L = 100;
    free(best_subsets_history);
    best_subsets_history = NULL;
    iterations_used = 0;
    
    best_cost = genetic_subset_selection(N, K, B, L, 0,
                                       cost_sum_squares, 
                                       &best_subsets_history,
                                       &iterations_used);
    
    printf("\nTest 2 - N=%d, K=%d, B=%d, L=%d\n", N, K, B, L);
    printf("Best cost: %d\n", best_cost);
    printf("Iterations until convergence: %d\n", iterations_used);
    printf("Best subset: {");
    for (int j = 1; j <= K; j++) {
        printf("%d", best_subsets_history[j]);
        if (j < K) printf(", ");
    }
    printf("}\n");
    
    // Test 3: Test convergence speed with different B values
    printf("\n\nConvergence Speed Analysis:\n");
    printf("===========================\n");
    N = 40; K = 7; L = 100;
    
    for (int B_test = 5; B_test <= 20; B_test += 5) {
        free(best_subsets_history);
        best_subsets_history = NULL;
        iterations_used = 0;
        
        best_cost = genetic_subset_selection(N, K, B_test, L, 0,
                                           cost_sum_squares, 
                                           &best_subsets_history,
                                           &iterations_used);
        
        printf("B=%2d: Best cost=%3d, Iterations=%3d\n", 
               B_test, best_cost, iterations_used);
    }
    
    free(best_subsets_history);
    
    return 0;
}
*/

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Wrd_t * Gia_ManBsFindStart( Gia_Man_t * pGia, int nWords )
{
    Vec_Wrd_t * vSims = Vec_WrdStartRandom( (Gia_ManCiNum(pGia) + 1) * nWords );
    Vec_WrdFillExtra( vSims, Gia_ManObjNum(pGia) * nWords, 0 );
    Abc_TtClear( Vec_WrdArray(vSims), nWords );
    return vSims;
}
void Gia_ManBsFindNext( Gia_Man_t * pGia, int nWords, Vec_Wrd_t * vSims, Vec_Wrd_t * vSimsOuts, int iMint )
{
    Gia_Obj_t * pObj; int i;
    word * pSims[2], * pSim;
    Gia_ManForEachAnd( pGia, pObj, i ) {
        pSim     = Vec_WrdEntryP( vSims, i * nWords );
        pSims[0] = Vec_WrdEntryP( vSims, Gia_ObjFaninId0(pObj, i) * nWords );
        pSims[1] = Vec_WrdEntryP( vSims, Gia_ObjFaninId1(pObj, i) * nWords );
        Abc_TtAndCompl( pSim, pSims[0], Gia_ObjFaninC0(pObj), pSims[1], Gia_ObjFaninC1(pObj), nWords );
    }
    Gia_ManForEachCo( pGia, pObj, i ) {
        pSim     = Vec_WrdEntryP( vSimsOuts, (iMint * Gia_ManCoNum(pGia) + i) * nWords );
        pSims[0] = Vec_WrdEntryP( vSims, Gia_ObjFaninId0p(pGia, pObj) * nWords );
        Abc_TtCopy( pSim, pSims[0], nWords, Gia_ObjFaninC0(pObj) );
    }
}
int Gia_ManBsFindMyu( Gia_Man_t * p, int nWords, Vec_Wrd_t * vSims, Vec_Wrd_t * vSimsOuts, Vec_Int_t * vVarNums, Vec_Wrd_t * vTemp )
{
    int nMints = 1 << Vec_IntSize(vVarNums);
    int nWordsAll = Gia_ManCoNum(p) * nWords;
    int nMyu = 0, pMyu[256], i, k, Var;
    assert( nMints <= 256 );
    assert( Vec_WrdSize(vTemp) == nWords * Vec_IntSize(vVarNums) );
    assert( Vec_WrdSize(vSimsOuts) == nMints * nWordsAll );
    Vec_IntForEachEntry( vVarNums, Var, i )
        Abc_TtCopy( Vec_WrdEntryP(vTemp, i * nWords), Vec_WrdEntryP(vSims, Gia_ManCiIdToId(p, Var) * nWords), nWords, 0 );
    for ( int m = 0; m < nMints; m++ ) {
        Vec_IntForEachEntry( vVarNums, Var, i )
            Abc_TtConst( Vec_WrdEntryP(vSims, Gia_ManCiIdToId(p, Var) * nWords), nWords, (m >> i) & 1 );
        Gia_ManBsFindNext( p, nWords, vSims, vSimsOuts, m );
    }
    Vec_IntForEachEntry( vVarNums, Var, i )
        Abc_TtCopy( Vec_WrdEntryP(vSims, Gia_ManCiIdToId(p, Var) * nWords), Vec_WrdEntryP(vTemp, i * nWords), nWords, 0 );
    for ( i = 0; i < nMints; i++ ) {
        word * pSim = Vec_WrdEntryP(vSimsOuts, nWordsAll * i);
        for ( k = 0; k < nMyu; k++ )
            if ( Abc_TtEqual(pSim, Vec_WrdEntryP(vSimsOuts, nWordsAll * pMyu[k]), nWordsAll) )
                break;
        if ( k == nMyu )
            pMyu[nMyu++] = i;
    }
    return nMyu;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

typedef struct BsFind_UserData_t_ {
    Gia_Man_t * pGia;
    int nWords;
    Vec_Wrd_t * vSims;
    Vec_Wrd_t * vSimsOuts;
    Vec_Int_t * vVarNums;
    Vec_Wrd_t * vTemp;
} BsFind_UserData_t;

BsFind_UserData_t * Gia_ManBsFindMyuFunctionStart( Gia_Man_t * pGia, int nWords, int nLutSize )
{
    BsFind_UserData_t * p = ABC_CALLOC( BsFind_UserData_t, 1 );
    p->pGia      = pGia;
    p->nWords    = nWords;
    p->vSims     = Gia_ManBsFindStart( pGia, nWords );
    p->vSimsOuts = Vec_WrdStart( (1 << nLutSize) * Gia_ManCoNum(pGia) * nWords );
    p->vVarNums  = Vec_IntAlloc( nLutSize );
    p->vTemp     = Vec_WrdStart( nLutSize * nWords );
    return p;
}
int Gia_ManBsFindMyuFunction( int * subset, int K, void * pUserData )
{
    BsFind_UserData_t * p = (BsFind_UserData_t *)pUserData;
    Vec_IntClear( p->vVarNums );
    for ( int i = 0; i < K; i++ )
        Vec_IntPush( p->vVarNums, subset[i] );
    return Gia_ManBsFindMyu( p->pGia, p->nWords, p->vSims, p->vSimsOuts, p->vVarNums, p->vTemp );
}
void Gia_ManBsFindMyuFunctionStop( BsFind_UserData_t * p )
{
    Vec_WrdFree( p->vSims );
    Vec_WrdFree( p->vSimsOuts );
    Vec_WrdFree( p->vTemp );
    Vec_IntFree( p->vVarNums );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManBsFindBest( Gia_Man_t * pGia, int nWords, int nLutSize, int nBest, int nIterMax, int fVerbose )
{
    abctime clk = Abc_Clock();
    Abc_Random(1);
    BsFind_UserData_t * p = Gia_ManBsFindMyuFunctionStart( pGia, nWords, nLutSize );
    int nIters = 0, Res = genetic_subset_selection( Gia_ManCiNum(pGia), nLutSize, nBest, nIterMax, fVerbose, Gia_ManBsFindMyuFunction, NULL, &nIters, (void *)p );
    printf( "The best Myu %d was found after considering %d bound-sets in %d iterations.  ", Res, nIters*nBest*(nBest-1)/2, nIters );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    Gia_ManBsFindMyuFunctionStop( p );
    return Res;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

