#include "tgLog.h"
/**CFile****************************************************************

  FileName    [paSpectral.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Lightweight placement-aware optimization support.]

  Synopsis    [Self-contained spectral Poisson solver for placement density.]

***********************************************************************/

#include "tgDensity.h"

#include <algorithm>
#include <cmath>

ABC_NAMESPACE_IMPL_START

Tg_SpectralSolver::Tg_SpectralSolver(int Bins, double BinSizeX, double BinSizeY)
    : bins_(Bins), fftSize_(2 * Bins), binSizeX_(BinSizeX), binSizeY_(BinSizeY),
      spectral_(Bins * Bins, 0.0), transformTemp_(Bins * Bins, 0.0), transformInput_(Bins, 0.0),
      transformOutput_(Bins, 0.0), fftWork_(2 * Bins)
{
    InitializeFftPlan();
    InitializeSpectralPlan();
}

int Tg_SpectralSolver::GridIndex(int X, int Y) const
{
    X = std::max(0, std::min(bins_ - 1, X));
    Y = std::max(0, std::min(bins_ - 1, Y));
    return X * bins_ + Y;
}

void Tg_SpectralSolver::InitializeFftPlan()
{
    fftBitReverse_.resize(fftSize_);
    for (int i = 0, j = 0; i < fftSize_; ++i)
    {
        fftBitReverse_[i] = j;
        int Bit = fftSize_ >> 1;
        while (Bit > 0 && (j & Bit))
        {
            j ^= Bit;
            Bit >>= 1;
        }
        if (Bit > 0)
            j ^= Bit;
    }

    const double Pi = std::acos(-1.0);
    fftTwiddleForward_.resize(fftSize_ / 2);
    fftTwiddleInverse_.resize(fftSize_ / 2);
    for (int k = 0; k < fftSize_ / 2; ++k)
    {
        double Angle = 2.0 * Pi * k / fftSize_;
        fftTwiddleForward_[k] = std::complex<double>(std::cos(Angle), -std::sin(Angle));
        fftTwiddleInverse_[k] = std::conj(fftTwiddleForward_[k]);
    }
    dctPhase_.resize(bins_);
    for (int k = 0; k < bins_; ++k)
    {
        double Angle = Pi * k / fftSize_;
        dctPhase_[k] = std::complex<double>(std::cos(Angle), std::sin(Angle));
    }
}

void Tg_SpectralSolver::InitializeSpectralPlan()
{
    const double Pi = std::acos(-1.0);
    spectralWx_.resize(bins_);
    spectralWy_.resize(bins_);
    inverseLaplacian_.resize(bins_ * bins_);
    for (int Kx = 0; Kx < bins_; ++Kx)
        spectralWx_[Kx] = Pi * Kx / (bins_ * binSizeX_);
    for (int Ky = 0; Ky < bins_; ++Ky)
        spectralWy_[Ky] = Pi * Ky / (bins_ * binSizeY_);
    for (int Kx = 0; Kx < bins_; ++Kx)
        for (int Ky = 0; Ky < bins_; ++Ky)
        {
            double Denominator =
                spectralWx_[Kx] * spectralWx_[Kx] + spectralWy_[Ky] * spectralWy_[Ky];
            inverseLaplacian_[GridIndex(Kx, Ky)] = Denominator > 0.0 ? 1.0 / Denominator : 0.0;
        }
}

void Tg_SpectralSolver::Fft(bool Inverse)
{
    for (int i = 0; i < fftSize_; ++i)
        if (i < fftBitReverse_[i])
            std::swap(fftWork_[i], fftWork_[fftBitReverse_[i]]);
    for (int Length = 2; Length <= fftSize_; Length <<= 1)
    {
        int TwiddleStride = fftSize_ / Length;
        for (int Base = 0; Base < fftSize_; Base += Length)
            for (int Offset = 0; Offset < Length / 2; ++Offset)
            {
                const std::complex<double> &Factor =
                    Inverse ? fftTwiddleInverse_[Offset * TwiddleStride]
                            : fftTwiddleForward_[Offset * TwiddleStride];
                std::complex<double> Even = fftWork_[Base + Offset];
                std::complex<double> Odd = Factor * fftWork_[Base + Offset + Length / 2];
                fftWork_[Base + Offset] = Even + Odd;
                fftWork_[Base + Offset + Length / 2] = Even - Odd;
            }
    }
    if (Inverse)
        for (std::complex<double> &Value : fftWork_)
            Value /= fftSize_;
}

void Tg_SpectralSolver::DctForward(const std::vector<double> &Input, std::vector<double> &Output)
{
    for (int i = 0; i < bins_; ++i)
    {
        fftWork_[i] = Input[i];
        fftWork_[fftSize_ - 1 - i] = Input[i];
    }
    Fft(false);
    for (int k = 0; k < bins_; ++k)
        Output[k] = 0.5 * (fftWork_[k] * std::conj(dctPhase_[k])).real();
}

void Tg_SpectralSolver::DctInverse(const std::vector<double> &Input, std::vector<double> &Output)
{
    std::fill(fftWork_.begin(), fftWork_.end(), std::complex<double>(0.0, 0.0));
    fftWork_[0] = 2.0 * Input[0];
    for (int k = 1; k < bins_; ++k)
    {
        fftWork_[k] = 2.0 * Input[k] * dctPhase_[k];
        fftWork_[fftSize_ - k] = std::conj(fftWork_[k]);
    }
    Fft(true);
    for (int i = 0; i < bins_; ++i)
        Output[i] = fftWork_[i].real();
}

void Tg_SpectralSolver::SineInverse(const std::vector<double> &Input, std::vector<double> &Output)
{
    std::fill(fftWork_.begin(), fftWork_.end(), std::complex<double>(0.0, 0.0));
    for (int k = 1; k < bins_; ++k)
    {
        fftWork_[k] = std::complex<double>(0.0, -2.0) * Input[k] * dctPhase_[k];
        fftWork_[fftSize_ - k] = std::conj(fftWork_[k]);
    }
    Fft(true);
    for (int i = 0; i < bins_; ++i)
        Output[i] = fftWork_[i].real();
}

void Tg_SpectralSolver::Solve(const std::vector<double> &Density, std::vector<double> &FieldX,
                              std::vector<double> &FieldY)
{
    // The separable DCT applies Neumann boundary conditions directly on the
    // bins. Mixed sine/cosine inverses differentiate the potential exactly.
    for (int X = 0; X < bins_; ++X)
    {
        for (int Y = 0; Y < bins_; ++Y)
            transformInput_[Y] = Density[GridIndex(X, Y)];
        DctForward(transformInput_, transformOutput_);
        for (int Ky = 0; Ky < bins_; ++Ky)
            transformTemp_[GridIndex(X, Ky)] = transformOutput_[Ky];
    }
    for (int Ky = 0; Ky < bins_; ++Ky)
    {
        for (int X = 0; X < bins_; ++X)
            transformInput_[X] = transformTemp_[GridIndex(X, Ky)];
        DctForward(transformInput_, transformOutput_);
        for (int Kx = 0; Kx < bins_; ++Kx)
            spectral_[GridIndex(Kx, Ky)] =
                transformOutput_[Kx] * inverseLaplacian_[GridIndex(Kx, Ky)];
    }

    // grad(phi) is the negative electric field. The placement optimizer
    // subtracts this gradient, moving cells away from positive charge.
    for (int Ky = 0; Ky < bins_; ++Ky)
    {
        for (int Kx = 0; Kx < bins_; ++Kx)
            transformInput_[Kx] = -spectralWx_[Kx] * spectral_[GridIndex(Kx, Ky)];
        SineInverse(transformInput_, transformOutput_);
        for (int X = 0; X < bins_; ++X)
            transformTemp_[GridIndex(X, Ky)] = transformOutput_[X];
    }
    for (int X = 0; X < bins_; ++X)
    {
        for (int Ky = 0; Ky < bins_; ++Ky)
            transformInput_[Ky] = transformTemp_[GridIndex(X, Ky)];
        DctInverse(transformInput_, transformOutput_);
        for (int Y = 0; Y < bins_; ++Y)
            FieldX[GridIndex(X, Y)] = transformOutput_[Y];
    }

    for (int Ky = 0; Ky < bins_; ++Ky)
    {
        for (int Kx = 0; Kx < bins_; ++Kx)
            transformInput_[Kx] = -spectralWy_[Ky] * spectral_[GridIndex(Kx, Ky)];
        DctInverse(transformInput_, transformOutput_);
        for (int X = 0; X < bins_; ++X)
            transformTemp_[GridIndex(X, Ky)] = transformOutput_[X];
    }
    for (int X = 0; X < bins_; ++X)
    {
        for (int Ky = 0; Ky < bins_; ++Ky)
            transformInput_[Ky] = transformTemp_[GridIndex(X, Ky)];
        SineInverse(transformInput_, transformOutput_);
        for (int Y = 0; Y < bins_; ++Y)
            FieldY[GridIndex(X, Y)] = transformOutput_[Y];
    }
}

ABC_NAMESPACE_IMPL_END
