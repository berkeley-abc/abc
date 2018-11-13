abc_libabc_add_sources(
    NAME base_main_mod
    SOURCES
        mainFrame.c
        mainInit.c
        mainLib.c
        mainReal.c
        libSupport.c
        mainUtils.c
)

abc_add_executable(
    NAME abc
    SOURCES
        main.c
)

install(TARGETS abc
    RUNTIME DESTINATION "${CMAKE_INSTALL_BINDIR}"
)
if(CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
    install(FILES $<TARGET_PDB_FILE:abc> DESTINATION bin OPTIONAL)
endif()
