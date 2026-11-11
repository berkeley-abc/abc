add_subdirectory(gia)

add_executable(eslim_replace eslim_replace.cpp)
target_link_libraries(eslim_replace PRIVATE libabc)
add_test(NAME eslim_replace COMMAND eslim_replace)
set_tests_properties(eslim_replace PROPERTIES SKIP_RETURN_CODE 77)

# The eSLIM2 oracles are local, uncommitted test assets. A fresh checkout must
# still configure and build when those files are absent.
set(ESLIM2_LOCAL_TEST_NAMES small_exact small_timing small_order area_refinement windows instances)
set(ESLIM2_LOCAL_TESTS_AVAILABLE TRUE)
if(NOT EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/eslim2_test_util.h")
    set(ESLIM2_LOCAL_TESTS_AVAILABLE FALSE)
endif()
foreach(name ${ESLIM2_LOCAL_TEST_NAMES})
    if(NOT EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/eslim2_${name}.cpp")
        set(ESLIM2_LOCAL_TESTS_AVAILABLE FALSE)
    endif()
endforeach()
if(ESLIM2_LOCAL_TESTS_AVAILABLE)
    foreach(name ${ESLIM2_LOCAL_TEST_NAMES})
        add_executable(eslim2_${name} eslim2_${name}.cpp)
        target_link_libraries(eslim2_${name} PRIVATE libabc)
    endforeach()
    add_test(NAME eslim2_small_exact COMMAND eslim2_small_exact)
    add_test(NAME eslim2_small_exact_sat COMMAND eslim2_small_exact sat)
    add_test(NAME eslim2_small_timing_prune COMMAND eslim2_small_timing 2 prune)
    add_test(NAME eslim2_small_timing_neutral COMMAND eslim2_small_timing 2 neutral)
    add_test(NAME eslim2_small_timing_refine COMMAND eslim2_small_timing 2 refine)
    add_test(NAME eslim2_small_order COMMAND eslim2_small_order)
    add_test(NAME eslim2_area_refinement COMMAND eslim2_area_refinement)
    add_test(NAME eslim2_windows COMMAND eslim2_windows)
    add_test(NAME eslim2_instances COMMAND eslim2_instances)
endif()

if(UNIX)
    add_test(NAME acec_output_coverage
        COMMAND bash ${CMAKE_CURRENT_SOURCE_DIR}/acec_output_coverage.sh $<TARGET_FILE:abc>)
endif()
find_program(ABC_BASH_EXECUTABLE bash)
if(ABC_BASH_EXECUTABLE)
    add_test(NAME sresub_drw_cleanup
        COMMAND ${CMAKE_COMMAND} -E env "ABC=$<TARGET_FILE:abc>"
            ${ABC_BASH_EXECUTABLE} "${CMAKE_CURRENT_SOURCE_DIR}/sresub_drw_cleanup.sh")
    set_tests_properties(sresub_drw_cleanup PROPERTIES
        SKIP_REGULAR_EXPRESSION "SKIP: python3 is needed")
endif()
