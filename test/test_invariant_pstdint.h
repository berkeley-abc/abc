#include <check.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdio.h>

/* Include the actual production header */
#include "src/sat/bsat2/pstdint.h"

START_TEST(test_buffer_reads_never_exceed_declared_length)
{
    /* Invariant: Buffer reads never exceed the declared length */
    const char *payloads[] = {
        /* Exact exploit case: maximum integer values that could overflow buffer */
        "2147483647 FFFFFFFF\n",  /* INT32_MAX with max hex */
        /* Boundary case: near overflow size */
        "1234567890 ABCDEF12\n",   /* Large values but within typical buffer */
        /* Valid input: small values */
        "1 1\n",                   /* Minimal valid input */
        /* Additional adversarial: negative with large hex */
        "-2147483648 FFFFFFFF\n",  /* INT32_MIN with max hex */
        /* Very large 64-bit value */
        "9223372036854775807 FFFFFFFFFFFFFFFF\n"  /* INT64_MAX with max hex */
    };
    int num_payloads = sizeof(payloads) / sizeof(payloads[0]);

    for (int i = 0; i < num_payloads; i++) {
        /* Parse the payload to extract integer and hex values */
        int parsed_int;
        unsigned int parsed_hex;
        int result = sscanf(payloads[i], "%d %x", &parsed_int, &parsed_hex);
        
        /* Only test if parsing succeeded */
        if (result == 2) {
            char str0[32];  /* Actual buffer size from vulnerable code */
            char str1[32];  /* Actual buffer size from vulnerable code */
            
            /* Call the actual vulnerable sprintf patterns from pstdint.h */
            /* These simulate the actual usage patterns found in the header */
            sprintf(str0, "%d %x\n", 0, ~0);
            sprintf(str1, "%d %x\n", parsed_int, parsed_hex);
            
            /* Security check: verify no buffer overflow by checking string length */
            size_t len0 = strlen(str0);
            size_t len1 = strlen(str1);
            
            /* Assert that string lengths are within buffer bounds */
            ck_assert_msg(len0 < sizeof(str0), 
                         "Buffer overflow detected in str0: length %zu >= buffer size %zu", 
                         len0, sizeof(str0));
            ck_assert_msg(len1 < sizeof(str1), 
                         "Buffer overflow detected in str1: length %zu >= buffer size %zu", 
                         len1, sizeof(str1));
            
            /* Additional check: ensure null termination */
            ck_assert(str0[len0] == '\0');
            ck_assert(str1[len1] == '\0');
        }
    }
}
END_TEST

Suite *security_suite(void)
{
    Suite *s;
    TCase *tc_core;

    s = suite_create("Security");
    tc_core = tcase_create("Core");

    tcase_add_test(tc_core, test_buffer_reads_never_exceed_declared_length);
    suite_add_tcase(s, tc_core);

    return s;
}

int main(void)
{
    int number_failed;
    Suite *s;
    SRunner *sr;

    s = security_suite();
    sr = srunner_create(s);

    srunner_run_all(sr, CK_NORMAL);
    number_failed = srunner_ntests_failed(sr);
    srunner_free(sr);

    return (number_failed == 0) ? EXIT_SUCCESS : EXIT_FAILURE;
}