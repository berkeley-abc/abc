/**CFile****************************************************************

  FileName    [snMain.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Slang-to-SN RTL frontend.]

  Synopsis    [Command-line driver for elaborating SystemVerilog and writing SN files.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snMain.cpp,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

// Standalone Slang-dependent frontend for ABC's SN binary interchange format.
//
//   sn -M my_top -D WIDTH=8 -t -o design.sn rtl1.sv rtl2.v
//
// All transformations are implemented by the Slang-independent SN package in
// ABC. This executable performs only parsing, elaboration, import, and binary
// serialization.

#include "snSlang.h"

#include <cstdio>
#include <cstring>
#include <exception>
#include <new>
#include <string>
#include <vector>

static void sn_slang_usage(const char* program)
{
    std::fprintf(stderr,
                 "\nusage: %s [-M module] [-D name[=value]]... [-B module]... [-L library]...\n"
                 "       [-I directory]... [-F file]... [-C directory] [-P file.json]\n"
                 "       [-e] [-a] [-g] [-i|-r] [-s|-u] [-p] [-t] [-h] -o file.sn file.sv ...\n"
                 "    -M module\t\tselect the top module [default = unique top]\n"
                 "    -D name[=value]\tspecify a preprocessor definition; may be repeated\n"
                 "    -B module\t\timport a declared module as a black box; may be repeated\n"
                 "    -L library\t\tread a Liberty or SN library; may be repeated\n"
                 "    -I directory\tadd an include directory; may be repeated\n"
                 "    -F file\t\tadd a Verilog library source; may be repeated\n"
                 "    -C directory\tuse this Liberty cache directory\n"
                 "    -P file.json\twrite the top-level port layout as JSON\n"
                 "    -e\t\t\tblack-box empty modules\n"
                 "    -a\t\t\tinfer memories only from attributes\n"
                 "    -g\t\t\tpreserve source metadata\n"
                 "    -i\t\t\tignore assertions [default = warn]\n"
                 "    -r\t\t\treject assertions [default = warn]\n"
                 "    -s\t\t\treject unknown modules\n"
                 "    -u\t\t\twarn and drop unknown modules\n"
                 "    -p\t\t\tpreserve constant and unused state\n"
                 "    -t\t\t\treport frontend timing\n"
                 "    -o file.sn\t\twrite the binary SN design (required)\n"
                 "    -h\t\t\tprint the command usage\n",
                 program);
}

int main(int argc, char** argv)
{
    const char* top = nullptr;
    const char* output = nullptr;
    std::vector<const char*> libraries;
    std::vector<const char*> include_directories, library_sources;
    const char* library_cache = nullptr;
    const char* port_layout = nullptr;
    sn_slang_unknown_module_policy_t unknown_policy = SN_SLANG_UNKNOWN_DEFAULT;
    bool timing = false, preserve_state = false;
    std::vector<const char*> files;
    std::vector<std::string> define_storage;
    std::vector<const char*> blackboxes;
    bool blackbox_empty_modules = false;
    bool memories_from_attributes_only = false;
    bool preserve_metadata = false;
    sn_slang_assertion_policy_t assertion_policy = SN_SLANG_ASSERT_WARN;
    for (int arg = 1; arg < argc;)
    {
        const char* option = argv[arg];
        if (std::strcmp(option, "-M") == 0 && arg + 1 < argc)
        {
            top = argv[arg + 1];
            arg += 2;
        }
        else if (std::strcmp(option, "-L") == 0 && arg + 1 < argc)
        {
            libraries.push_back(argv[arg + 1]);
            arg += 2;
        }
        else if (std::strcmp(option, "-p") == 0)
        {
            preserve_state = true;
            arg++;
        }
        else if (std::strcmp(option, "-I") == 0 && arg + 1 < argc)
        {
            include_directories.push_back(argv[arg + 1]);
            arg += 2;
        }
        else if (std::strcmp(option, "-F") == 0 && arg + 1 < argc)
        {
            library_sources.push_back(argv[arg + 1]);
            arg += 2;
        }
        else if (std::strcmp(option, "-P") == 0 && arg + 1 < argc)
        {
            port_layout = argv[arg + 1];
            arg += 2;
        }
        else if (std::strcmp(option, "-C") == 0 && arg + 1 < argc)
        {
            library_cache = argv[arg + 1];
            arg += 2;
        }
        else if (std::strcmp(option, "-s") == 0)
        {
            unknown_policy = SN_SLANG_UNKNOWN_ERROR;
            arg++;
        }
        else if (std::strcmp(option, "-u") == 0)
        {
            unknown_policy = SN_SLANG_UNKNOWN_WARN_DROP;
            arg++;
        }
        else if (std::strcmp(option, "-o") == 0 && arg + 1 < argc)
        {
            output = argv[arg + 1];
            arg += 2;
        }
        else if (std::strcmp(option, "-t") == 0)
        {
            timing = true;
            arg++;
        }
        else if (std::strcmp(option, "-D") == 0 && arg + 1 < argc)
        {
            define_storage.emplace_back(argv[arg + 1]);
            arg += 2;
        }
        else if (std::strncmp(option, "-D", 2) == 0 && option[2])
        {
            define_storage.emplace_back(option + 2);
            arg++;
        }
        else if (std::strcmp(option, "-B") == 0 && arg + 1 < argc)
        {
            blackboxes.push_back(argv[arg + 1]);
            arg += 2;
        }
        else if (std::strcmp(option, "-e") == 0)
        {
            blackbox_empty_modules = true;
            arg++;
        }
        else if (std::strcmp(option, "-a") == 0)
        {
            memories_from_attributes_only = true;
            arg++;
        }
        else if (std::strcmp(option, "-g") == 0)
        {
            preserve_metadata = true;
            arg++;
        }
        else if (std::strcmp(option, "-i") == 0)
        {
            assertion_policy = SN_SLANG_ASSERT_IGNORE;
            arg++;
        }
        else if (std::strcmp(option, "-r") == 0)
        {
            assertion_policy = SN_SLANG_ASSERT_ERROR;
            arg++;
        }
        else if (std::strcmp(option, "-h") == 0)
        {
            sn_slang_usage(argv[0]);
            return 0;
        }
        else if (option[0] == '-')
        {
            std::fprintf(stderr, "sn: unknown or incomplete option: %s\n", option);
            sn_slang_usage(argv[0]);
            return 1;
        }
        else
            files.push_back(argv[arg++]);
    }
    if (!output || files.empty())
    {
        sn_slang_usage(argv[0]);
        return 1;
    }
    std::string output_name(output);
    if (output_name.size() < 3 || output_name.substr(output_name.size() - 3) != ".sn")
    {
        std::fprintf(stderr, "sn: output file must use the .sn extension; Verilog output is not supported\n");
        return 1;
    }

    sn_slang_timing_t frontend_timing = {};
    std::vector<const char*> defines;
    defines.reserve(define_storage.size());
    for (const std::string& define : define_storage)
        defines.push_back(define.c_str());
    try
    {
        sn_slang_options_t options = {};
        options.preserve_state = preserve_state;
        options.define_count = int(defines.size());
        options.defines = defines.data();
        options.blackbox_count = int(blackboxes.size());
        options.blackboxes = blackboxes.data();
        options.blackbox_empty_modules = blackbox_empty_modules;
        options.memories_from_attributes_only = memories_from_attributes_only;
        options.preserve_metadata = preserve_metadata;
        options.assertion_policy = assertion_policy;
        options.liberty_count = int(libraries.size());
        options.liberty_files = libraries.data();
        options.unknown_module_policy = unknown_policy;
        options.liberty_cache_dir = library_cache;
        options.include_directory_count = int(include_directories.size());
        options.include_directories = include_directories.data();
        options.library_source_count = int(library_sources.size());
        options.library_sources = library_sources.data();
        options.port_layout_file = port_layout;
        if (!sn_slang_write_binary_files_top_options_timed((int)files.size(), files.data(), top, &options,
                                                            output, &frontend_timing))
            return 2;
    }
    catch (const std::bad_alloc&)
    {
        std::remove(output);
        std::fprintf(stderr, "sn: memory allocation failed; no output was written\n");
        return 2;
    }
    catch (const std::exception& exception)
    {
        std::remove(output);
        std::fprintf(stderr, "sn: frontend exception: %s; no output was written\n", exception.what());
        return 2;
    }
    if (timing)
    {
        std::printf("frontend_timing_seconds:\n");
        std::printf("  slang_parse: %.6f\n", frontend_timing.parse_seconds);
        std::printf("  slang_elaborate: %.6f\n", frontend_timing.elaborate_seconds);
        std::printf("  sn_import: %.6f\n", frontend_timing.import_seconds);
    }
    return 0;
}
