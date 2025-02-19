if(ABC_USE_NAMESPACE)
    set_source_files_properties(gia_test.cc PROPERTIES LANGUAGE CXX)
endif()

add_executable(gia_test gia_test.cc)

target_include_directories(gia_test PUBLIC ${GTEST_INCLUDE_DIRS})
target_compile_options(gia_test PUBLIC ${GTEST_CFLAGS})
target_link_libraries(gia_test PUBLIC
    libabc
    ${GTEST_LIBS}
)

gtest_discover_tests(gia_test
    # the traling directory below is a workaround for generators that append
    # an extra directory name (build type) such as VS on windows
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/${CMAKE_CFG_INTDIR}
)
