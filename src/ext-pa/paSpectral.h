#ifndef ABC__ext_pa__paSpectral_h
#define ABC__ext_pa__paSpectral_h

#include "base/abc/abc.h"

#include <complex>
#include <vector>

ABC_NAMESPACE_HEADER_START

class Pa_SpectralSolver
{
  public:
    Pa_SpectralSolver( int Bins, double BinSizeX, double BinSizeY );

    void Solve( const std::vector<double> & Density,
                std::vector<double> & FieldX,
                std::vector<double> & FieldY );

  private:
    int GridIndex( int X, int Y ) const;
    void InitializeFftPlan();
    void InitializeSpectralPlan();
    void Fft( bool Inverse );
    void DctForward( const std::vector<double> & Input,
                     std::vector<double> & Output );
    void DctInverse( const std::vector<double> & Input,
                     std::vector<double> & Output );
    void SineInverse( const std::vector<double> & Input,
                      std::vector<double> & Output );

    int bins_;
    int fftSize_;
    double binSizeX_;
    double binSizeY_;
    std::vector<double> spectral_;
    std::vector<double> transformTemp_;
    std::vector<double> transformInput_;
    std::vector<double> transformOutput_;
    std::vector<std::complex<double>> fftWork_;
    std::vector<std::complex<double>> fftTwiddleForward_;
    std::vector<std::complex<double>> fftTwiddleInverse_;
    std::vector<std::complex<double>> dctPhase_;
    std::vector<int> fftBitReverse_;
    std::vector<double> spectralWx_;
    std::vector<double> spectralWy_;
    std::vector<double> inverseLaplacian_;
};

ABC_NAMESPACE_HEADER_END

#endif
