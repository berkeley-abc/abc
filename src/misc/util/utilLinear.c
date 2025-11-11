/**CFile****************************************************************

  FileName    [utilLinear.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Handling counter-examples.]

  Synopsis    [Handling counter-examples.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: utilColor.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

//#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "misc/util/abc_global.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define EPSILON 1e-12
#define VERIFY_TOLERANCE 1e-9
#define INTEGER_TOLERANCE 1e-9

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

// Reads a full line from the file, allocating memory dynamically.
static char *read_line(FILE *fp) {
    size_t capacity = 128;
    size_t length = 0;
    char *buffer = (char *)malloc(capacity);
    if (!buffer) {
        errno = ENOMEM;
        return NULL;
    }

    int ch;
    while ((ch = fgetc(fp)) != EOF) {
        if (ch == '\r') {
            continue;
        }
        if (ch == '\n') {
            break;
        }
        if (length + 1 >= capacity) {
            size_t new_capacity = capacity * 2;
            char *tmp = (char *)realloc(buffer, new_capacity);
            if (!tmp) {
                free(buffer);
                errno = ENOMEM;
                return NULL;
            }
            buffer = tmp;
            capacity = new_capacity;
        }
        buffer[length++] = (char)ch;
    }

    if (length == 0 && ch == EOF) {
        free(buffer);
        return NULL;
    }

    buffer[length] = '\0';
    return buffer;
}

// Loads the augmented matrix from a text file.
static int load_augmented_matrix(const char *path, double **outMatrix, int *outEqus, int *outVars) {
    FILE *fp = fopen(path, "r");
    if (!fp) {
        perror("fopen");
        return 0;
    }

    double *data = NULL;
    size_t capacity = 0;
    size_t count = 0;
    int row_width = -1;
    int rows = 0;

    while (1) {
        char *line = read_line(fp);
        if (!line) {
            if (feof(fp)) {
                break;
            }
            fprintf(stderr, "Failed to read line from input file.\n");
            free(data);
            fclose(fp);
            return 0;
        }

        char *ptr = line;
        int columns = 0;
        while (*ptr != '\0') {
            char *end_ptr;
            double value = strtod(ptr, &end_ptr);
            if (end_ptr == ptr) {
                if (*ptr == '\0') {
                    break;
                }
                ++ptr;
                continue;
            }

            if (count == capacity) {
                size_t new_capacity = capacity == 0 ? 64 : capacity * 2;
                double *tmp = (double *)realloc(data, new_capacity * sizeof(double));
                if (!tmp) {
                    fprintf(stderr, "Out of memory while loading matrix.\n");
                    free(data);
                    free(line);
                    fclose(fp);
                    return 0;
                }
                data = tmp;
                capacity = new_capacity;
            }

            data[count++] = value;
            ++columns;
            ptr = end_ptr;
        }

        free(line);

        if (columns == 0) {
            continue;
        }

        if (row_width == -1) {
            row_width = columns;
        } else if (columns != row_width) {
            fprintf(stderr, "Row %d has %d entries, expected %d.\n", rows + 1, columns, row_width);
            free(data);
            fclose(fp);
            return 0;
        }

        ++rows;
    }

    fclose(fp);

    if (rows == 0) {
        fprintf(stderr, "Input file is empty or contains no data rows.\n");
        free(data);
        return 0;
    }

    if (row_width <= 1) {
        fprintf(stderr, "Each row must contain at least two numbers.\n");
        free(data);
        return 0;
    }

    if ((size_t)rows * (size_t)row_width != count) {
        fprintf(stderr, "Internal error: unexpected data size.\n");
        free(data);
        return 0;
    }

    *outMatrix = data;
    *outEqus = rows;
    *outVars = row_width - 1;

    return 1;
}

// Swaps two rows in-place.
static void swap_rows(double *matrix, int cols, int row_a, int row_b) {
    if (row_a == row_b) {
        return;
    }
    for (int c = 0; c < cols; ++c) {
        double tmp = matrix[row_a * cols + c];
        matrix[row_a * cols + c] = matrix[row_b * cols + c];
        matrix[row_b * cols + c] = tmp;
    }
}

// Clears values that are numerically close to zero.
static void prune_small_values(double *row, int count) {
    for (int i = 0; i < count; ++i) {
        if (fabs(row[i]) < EPSILON) {
            row[i] = 0.0;
        }
    }
}

// Computes a solution vector given assignments for the free variables.
static void compute_solution_from_free(
    const double *rref,
    int nVars,
    const int *pivot_cols,
    int rank,
    const int *free_cols,
    int free_count,
    const double *free_values,
    double *solution_out) {
    int row_len = nVars + 1;

    for (int i = 0; i < nVars; ++i) {
        solution_out[i] = 0.0;
    }

    for (int i = 0; i < free_count; ++i) {
        int col = free_cols[i];
        double value = free_values ? free_values[i] : 0.0;
        solution_out[col] = value;
    }

    for (int r = 0; r < rank; ++r) {
        int pivot_col = pivot_cols[r];
        double value = rref[r * row_len + nVars];
        for (int j = 0; j < free_count; ++j) {
            int free_col = free_cols[j];
            value -= rref[r * row_len + free_col] * solution_out[free_col];
        }
        solution_out[pivot_col] = value;
    }
}

// Verifies that the solution satisfies the original system.
static int verify_solution(
    const double *matrix,
    int nEqus,
    int nVars,
    const double *solution,
    double tolerance,
    double *out_max_residual) {
    int row_len = nVars + 1;
    double max_residual = 0.0;
    int ok = 1;

    for (int r = 0; r < nEqus; ++r) {
        double lhs = 0.0;
        for (int c = 0; c < nVars; ++c) {
            lhs += (double)matrix[r * row_len + c] * (double)solution[c];
        }
        double rhs = matrix[r * row_len + nVars];
        double residual = fabs(lhs - rhs);
        if ((double)residual > max_residual) {
            max_residual = (double)residual;
        }
        if ((double)residual > tolerance) {
            ok = 0;
        }
    }

    if (out_max_residual) {
        *out_max_residual = max_residual;
    }

    return ok;
}

// Checks whether a particular free-variable assignment yields an integer solution.
// Optionally enforces that the first four variables differ once rounded to integers.
static int assign_and_check_integer(
    const double *rref,
    int nVars,
    const int *pivot_cols,
    int rank,
    const int *free_cols,
    int free_count,
    const double *free_values,
    const double *original_matrix,
    int nEqus,
    double verify_tolerance,
    double *workspace,
    double *rounded,
    double *out_solution,
    int require_nonzero,
    int require_distinct_first_four) {
    compute_solution_from_free(
        rref,
        nVars,
        pivot_cols,
        rank,
        free_cols,
        free_count,
        free_values,
        workspace);

    for (int i = 0; i < nVars; ++i) {
        double candidate = workspace[i];
        double nearest = round(candidate);
        if (fabs(candidate - nearest) > INTEGER_TOLERANCE) {
            return 0;
        }
        rounded[i] = nearest;
    }

    int all_zero = 1;
    int has_zero_component = 0;
    int has_positive_component = 0;
    int has_negative_component = 0;
    for (int i = 0; i < nVars; ++i) {
        if (rounded[i] != 0.0) {
            all_zero = 0;
        } else {
            has_zero_component = 1;
        }
        if (rounded[i] > 0.0) {
            has_positive_component = 1;
        } else if (rounded[i] < 0.0) {
            has_negative_component = 1;
        }
    }
    if (require_nonzero) {
        if (all_zero || has_negative_component || !has_positive_component || !has_zero_component) {
            return 0;
        }
    }

    if (require_distinct_first_four && nVars >= 4) {
        for (int i = 0; i < 4; ++i) {
            for (int j = i + 1; j < 4; ++j) {
                if (fabs(rounded[i] - rounded[j]) < INTEGER_TOLERANCE) {
                    return 0;
                }
            }
        }
    }

    if (verify_solution(original_matrix, nEqus, nVars, rounded, verify_tolerance, NULL)) {
        memcpy(out_solution, rounded, (size_t)nVars * sizeof(double));
        return 1;
    }

    return 0;
}

// Recursively explores integer assignments for free variables while propagating optional constraints.
static int search_integer_solutions(
    int depth,
    int free_count,
    double *free_values,
    const int *candidates,
    int candidate_count,
    const double *rref,
    int nEqus,
    int nVars,
    const int *pivot_cols,
    int rank,
    const int *free_cols,
    const double *original_matrix,
    double verify_tolerance,
    double *workspace,
    double *rounded,
    double *out_solution,
    int require_nonzero,
    int require_distinct_first_four,
    int *explored,
    int exploration_limit) {
    if (*explored >= exploration_limit) {
        return 0;
    }

    if (depth == free_count) {
        (*explored)++;
        return assign_and_check_integer(
            rref,
            nVars,
            pivot_cols,
            rank,
            free_cols,
            free_count,
            free_values,
            original_matrix,
            nEqus,
            verify_tolerance,
            workspace,
            rounded,
            out_solution,
            require_nonzero,
            require_distinct_first_four);
    }

    for (int i = 0; i < candidate_count; ++i) {
        free_values[depth] = (double)candidates[i];
        if (search_integer_solutions(
                depth + 1,
                free_count,
                free_values,
                candidates,
                candidate_count,
                rref,
                nEqus,
                nVars,
                pivot_cols,
                rank,
                free_cols,
                original_matrix,
                verify_tolerance,
                workspace,
                rounded,
                out_solution,
                require_nonzero,
                require_distinct_first_four,
                explored,
                exploration_limit)) {
            return 1;
        }
    }

    return 0;
}

// Attempts to locate an integer solution when free variables are present.
// Searches a small integer lattice and enforces optional constraints such as distinct first variables.
static int try_integer_solution(
    const double *rref,
    int nEqus,
    int nVars,
    const int *pivot_cols,
    int rank,
    const int *free_cols,
    int free_count,
    const double *original_matrix,
    double verify_tolerance,
    double *workspace,
    double *rounded,
    double *out_solution,
    int require_nonzero,
    int require_distinct_first_four) {
    if (free_count == 0) {
        return 0;
    }

    // Expand search radius to allow moderately sized integer assignments (up to |20|).
    const int candidates[] = {
        0,
        1, -1,
        2, -2,
        3, -3,
        4, -4,
        5, -5,
        6, -6,
        7, -7,
        8, -8,
        9, -9,
        10, -10,
        11, -11,
        12, -12,
        13, -13,
        14, -14,
        15, -15,
        16, -16,
        17, -17,
        18, -18,
        19, -19,
        20, -20
    };
    const int candidate_count = (int)(sizeof(candidates) / sizeof(candidates[0]));
    int exploration_limit = 200000;
    int explored = 0;

    double *free_values = (double *)malloc((size_t)free_count * sizeof(double));
    if (!free_values) {
        return 0;
    }
    for (int i = 0; i < free_count; ++i) {
        free_values[i] = 0.0;
    }

    if (assign_and_check_integer(
            rref,
            nVars,
            pivot_cols,
            rank,
            free_cols,
            free_count,
            free_values,
            original_matrix,
            nEqus,
            verify_tolerance,
            workspace,
            rounded,
            out_solution,
            require_nonzero,
            require_distinct_first_four)) {
        free(free_values);
        return 1;
    }

    int found = search_integer_solutions(
        0,
        free_count,
        free_values,
        candidates,
        candidate_count,
        rref,
        nEqus,
        nVars,
        pivot_cols,
        rank,
        free_cols,
        original_matrix,
        verify_tolerance,
        workspace,
        rounded,
        out_solution,
        require_nonzero,
        require_distinct_first_four,
        &explored,
        exploration_limit);

    free(free_values);
    return found;
}

// Gaussian-elimination-based solver that optionally searches for integer solutions.
double *linear_equation_solver(double *pMatrix, int nEqus, int nVars) {
    if (!pMatrix || nEqus <= 0 || nVars <= 0) {
        fprintf(stderr, "Invalid matrix dimensions provided to solver.\n");
        return NULL;
    }

    int row_len = nVars + 1;
    size_t matrix_bytes = (size_t)nEqus * (size_t)row_len * sizeof(double);

    double *matrix_copy = NULL;
    double *solution = NULL;
    double *workspace = NULL;
    double *rounded = NULL;
    double *result = NULL;
    int *pivot_cols = NULL;
    int *pivot_column_used = NULL;
    int *free_cols = NULL;
    int free_count = 0;
    int homogeneous_rhs = 0;
    int require_nonzero_integer = 0;
    int require_distinct_first_four = 0;
    int pivot_row_index = 0;
    int rank = 0;
    double max_residual = 0.0;

    matrix_copy = (double *)malloc(matrix_bytes);
    if (!matrix_copy) {
        fprintf(stderr, "Unable to allocate memory for solver workspace.\n");
        goto cleanup;
    }
    memcpy(matrix_copy, pMatrix, matrix_bytes);

    pivot_cols = (int *)malloc((size_t)nEqus * sizeof(int));
    if (!pivot_cols) {
        fprintf(stderr, "Unable to allocate memory for pivot tracking.\n");
        goto cleanup;
    }
    for (int i = 0; i < nEqus; ++i) {
        pivot_cols[i] = -1;
    }

    pivot_row_index = 0;
    for (int col = 0; col < nVars && pivot_row_index < nEqus; ++col) {
        int best_row = pivot_row_index;
        double max_value = fabs(matrix_copy[best_row * row_len + col]);
        for (int r = pivot_row_index + 1; r < nEqus; ++r) {
            double value = fabs(matrix_copy[r * row_len + col]);
            if (value > max_value) {
                max_value = value;
                best_row = r;
            }
        }

        if (max_value < EPSILON) {
            continue;
        }

        swap_rows(matrix_copy, row_len, pivot_row_index, best_row);

        double pivot_value = matrix_copy[pivot_row_index * row_len + col];
        for (int c = 0; c < row_len; ++c) {
            matrix_copy[pivot_row_index * row_len + c] /= pivot_value;
        }
        matrix_copy[pivot_row_index * row_len + col] = 1.0;
        prune_small_values(&matrix_copy[pivot_row_index * row_len], row_len);

        for (int r = 0; r < nEqus; ++r) {
            if (r == pivot_row_index) {
                continue;
            }
            double factor = matrix_copy[r * row_len + col];
            if (fabs(factor) < EPSILON) {
                continue;
            }
            for (int c = 0; c < row_len; ++c) {
                matrix_copy[r * row_len + c] -= factor * matrix_copy[pivot_row_index * row_len + c];
            }
            matrix_copy[r * row_len + col] = 0.0;
            prune_small_values(&matrix_copy[r * row_len], row_len);
        }

        pivot_cols[pivot_row_index] = col;
        ++pivot_row_index;
    }

    rank = pivot_row_index;
    //printf("Rank: %d\n", rank);

    for (int r = 0; r < nEqus; ++r) {
        int zero_row = 1;
        for (int c = 0; c < nVars; ++c) {
            if (fabs(matrix_copy[r * row_len + c]) > EPSILON) {
                zero_row = 0;
                break;
            }
        }
        if (zero_row && fabs(matrix_copy[r * row_len + nVars]) > EPSILON) {
            printf("Verification: inconsistent system detected.\n");
            goto cleanup;
        }
    }

    pivot_column_used = (int *)calloc((size_t)nVars, sizeof(int));
    if (!pivot_column_used) {
        fprintf(stderr, "Unable to allocate memory for pivot metadata.\n");
        goto cleanup;
    }
    for (int r = 0; r < rank; ++r) {
        int col = pivot_cols[r];
        if (col >= 0 && col < nVars) {
            pivot_column_used[col] = 1;
        }
    }

    free_count = 0;
    for (int c = 0; c < nVars; ++c) {
        if (!pivot_column_used[c]) {
            ++free_count;
        }
    }

    if (free_count > 0) {
        free_cols = (int *)malloc((size_t)free_count * sizeof(int));
        if (!free_cols) {
            fprintf(stderr, "Unable to allocate memory for free column list.\n");
            goto cleanup;
        }
        int idx = 0;
        for (int c = 0; c < nVars; ++c) {
            if (!pivot_column_used[c]) {
                free_cols[idx++] = c;
            }
        }
    }

    homogeneous_rhs = 1;
    for (int r = 0; r < nEqus; ++r) {
        if (fabs(pMatrix[r * row_len + nVars]) > EPSILON) {
            homogeneous_rhs = 0;
            break;
        }
    }
    // Only demand integer solutions when the system is homogeneous with free variables.
    require_nonzero_integer = homogeneous_rhs && free_count > 0;
    // Enforce distinct first two variables whenever multiple variables remain free.
    require_distinct_first_four = (free_count > 0 && nVars >= 4);

    solution = (double *)malloc((size_t)nVars * sizeof(double));
    workspace = (double *)malloc((size_t)nVars * sizeof(double));
    rounded = (double *)malloc((size_t)nVars * sizeof(double));
    if (!solution || !workspace || !rounded) {
        fprintf(stderr, "Unable to allocate solver buffers.\n");
        goto cleanup;
    }

    if (free_count == 0) {
        compute_solution_from_free(
            matrix_copy,
            nVars,
            pivot_cols,
            rank,
            free_cols,
            free_count,
            NULL,
            solution);
    } else {
        if (free_count >= 6) {
            printf("Warning: large nullspace (%d free variables); integer search radius +/-20 may be expensive.\n", free_count);
        }
        if (!try_integer_solution(
                matrix_copy,
                nEqus,
                nVars,
                pivot_cols,
                rank,
                free_cols,
                free_count,
                pMatrix,
                VERIFY_TOLERANCE,
                workspace,
                rounded,
                solution,
                require_nonzero_integer,
                require_distinct_first_four)) {
            for (int i = 0; i < free_count; ++i) {
                workspace[i] = 0.0;
            }
            compute_solution_from_free(
                matrix_copy,
                nVars,
                pivot_cols,
                rank,
                free_cols,
                free_count,
                workspace,
                solution);
            if (require_nonzero_integer && require_distinct_first_four) {
                printf("Note: integer solution meeting non-negative and distinct-first-four constraints not found; returning floating-point solution.\n");
            } else if (require_nonzero_integer) {
                printf("Note: non-negative integer solution with mixed zero/positive entries not found; returning floating-point solution.\n");
            } else if (require_distinct_first_four) {
                printf("Note: integer solution with distinct first four variables not found; returning floating-point solution.\n");
            } else {
                printf("Note: integer solution not found; returning floating-point solution.\n");
            }
        }
    }

    max_residual = 0.0;
    if (!verify_solution(pMatrix, nEqus, nVars, solution, VERIFY_TOLERANCE, &max_residual)) {
        printf("Verification: failure (max residual = %.6f)\n", max_residual);
        goto cleanup;
    }
    //printf("Verification: success (max residual = %.6f)\n", max_residual);

    result = solution;
    solution = NULL;

cleanup:
    free(matrix_copy);
    free(pivot_cols);
    free(pivot_column_used);
    free(free_cols);
    free(workspace);
    free(rounded);
    free(solution);
    return result;
}

/*

int main(int argc, char **argv) {
    if (argc != 2) {
        fprintf(stderr, "Usage: %s <matrix_file>\n", argv[0]);
        return EXIT_FAILURE;
    }

    double *matrix = NULL;
    int nEqus = 0;
    int nVars = 0;

    if (!load_augmented_matrix(argv[1], &matrix, &nEqus, &nVars)) {
        return EXIT_FAILURE;
    }

    printf("Equations: %d, Variables: %d\n", nEqus, nVars);

    struct timespec start_time;
    struct timespec end_time;
    if (clock_gettime(CLOCK_MONOTONIC, &start_time) != 0) {
        perror("clock_gettime");
        free(matrix);
        return EXIT_FAILURE;
    }

    double *solution = linear_equation_solver(matrix, nEqus, nVars);

    if (clock_gettime(CLOCK_MONOTONIC, &end_time) != 0) {
        perror("clock_gettime");
        free(matrix);
        free(solution);
        return EXIT_FAILURE;
    }

    if (!solution) {
        free(matrix);
        return EXIT_FAILURE;
    }

    double elapsed = (double)(end_time.tv_sec - start_time.tv_sec);
    elapsed += (double)(end_time.tv_nsec - start_time.tv_nsec) / 1e9;
    printf("Solve time: %.6f seconds\n", elapsed);

    for (int i = 0; i < nVars; ++i) {
        printf("x%d = %.6f\n", i, solution[i]);
    }

    free(matrix);
    free(solution);

    return EXIT_SUCCESS;
}
*/

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

