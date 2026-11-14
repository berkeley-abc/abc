/**CFile****************************************************************

  FileName    [utilIoStream.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Utilities.]

  Synopsis    [Thread-local C++ streams using the current output destination.]

  Author      [Alan Mishchenko]

  Date        [Ver. 1.0. Started - November 14, 2026.]

***********************************************************************/

#include "abc_io.h"
#include "abc_global.h"
#include <iostream>

#undef cout
#undef cerr

ABC_NAMESPACE_IMPL_START

#if defined(ABC_STDIO_REDIRECT) && ABC_HAS_THREAD_LOCAL
class Abc_IoStreamBuf : public std::streambuf
{
    FILE * pFile;
protected:
    std::streamsize xsputn( const char * pData, std::streamsize Size ) override
    {
        return (std::streamsize)Abc_IoFwrite( pData, 1, (size_t)Size, pFile );
    }
    int_type overflow( int_type c ) override
    {
        if ( traits_type::eq_int_type(c, traits_type::eof()) )
            return traits_type::not_eof( c );
        char Char = traits_type::to_char_type( c );
        return xsputn(&Char, 1) == 1 ? c : traits_type::eof();
    }
    int sync() override { return Abc_IoFflush( pFile ); }
public:
    explicit Abc_IoStreamBuf( FILE * p ) : pFile(p) {}
};

struct Abc_IoStreams
{
    Abc_IoStreamBuf OutBuf, ErrBuf;
    std::ostream Out, Err;
    Abc_IoStreams() : OutBuf(stdout), ErrBuf(stderr), Out(&OutBuf), Err(&ErrBuf)
    {
        Err.setf( std::ios_base::unitbuf );
        Err.tie( &Out );
    }
};
#endif

/**Function*************************************************************

  Synopsis    [Preserves formatting across statements without shared streams.]

***********************************************************************/
std::ostream & Abc_IoStream( int Stream )
{
#if defined(ABC_STDIO_REDIRECT) && ABC_HAS_THREAD_LOCAL
    // Buffers resolve the frame on every write and retain no log pointer.
    static thread_local Abc_IoStreams Streams;
    return Stream == 0 ? Streams.Out : Streams.Err;
#else
    return Stream == 0 ? std::cout : std::cerr;
#endif
}

ABC_NAMESPACE_IMPL_END
