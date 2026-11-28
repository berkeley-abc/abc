/**CFile****************************************************************

  FileName    [paPlace.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Placement-aware synthesis.]

  Synopsis    [Companion placement of an AIG or a mapped network.]

  Author      [Anqi Lu]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 27, 2026.]

  Revision    [$Id: paPlace.cpp,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

#include "paInt.h"
#include "paDensity.h"
#include "paMath.h"
#include "map/mio/mio.h"

#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <limits>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

namespace
{

struct Pa_Point
{
    Abc_Obj_t * object = nullptr;
    double x = 0.0;
    double y = 0.0;
    double width = 1.0;
    double densityHalfX = 0.5;
    double densityHalfY = 0.5;
    double densityScale = 1.0;
    bool movable = false;
};

struct Pa_MappedSeed
{
    double x = 0.0;
    double y = 0.0;
};

struct Pa_Net
{
    std::vector<int> pins;
};

// Fixed placement settings; AGR varies the initial step.
struct Pa_Parameters
{
    int iterations = 500;
    int extraIterations = 500;
    int refineRounds = 12;
    double utilization = 0.70;
    double step = PA_PLACE_STEP;
    double densityWeight = 0.00008;
    double momentum = 0.95;
};

class Pa_Placement
{
  public:
    Pa_Placement( Abc_Ntk_t * pNtk, const Pa_Parameters & Pars )
        : pNtk_(pNtk), pars_(Pars), points_(Abc_NtkObjNumMax(pNtk))
    {
        nodeCount_ = Abc_NtkNodeNum(pNtk_);
        InitializeCellSizes();
        double IdealArea = totalCellArea_ / pars_.utilization;
        height_ = std::max(1.0, std::floor(std::sqrt(IdealArea)));
        // Unmapping can leave only constants/buffers and no movable AIG nodes.
        // Keep the density grid well-defined even when the total area is zero.
        width_ = std::max(1.0, std::ceil(IdealArea / height_));
        bins_ = ChooseBinCount();
        binSizeX_ = width_ / bins_;
        binSizeY_ = height_ / bins_;
        targetAreaPerBin_ = binSizeX_ * binSizeY_;
        rawDensity_.resize(bins_ * bins_, 0.0);
        density_.resize(bins_ * bins_, 0.0);
        fieldX_.resize(bins_ * bins_, 0.0);
        fieldY_.resize(bins_ * bins_, 0.0);
        spectralSolver_.reset(new Pa_SpectralSolver(bins_, binSizeX_, binSizeY_));
        gradientX_.resize(points_.size(), 0.0);
        gradientY_.resize(points_.size(), 0.0);
        densityGradientX_.resize(points_.size(), 0.0);
        densityGradientY_.resize(points_.size(), 0.0);
        BuildNetlist();
        InitializeDensityModel();
        InitializeCoordinates();
        fingerprint_ = ComputeFingerprint(pNtk_);
    }

    void Run()
    {
        UpdateDensity();
        double DensityPenalty = 0.0;
        int Iter = 0;
        int TargetReachedAt = -1;
        bool FineGrid = bins_ >= 512;
        for ( ; Iter < pars_.iterations + pars_.extraIterations; ++Iter )
        {
            double Overflow = UpdateDensity();
            if ( Iter >= pars_.iterations && Overflow <= 0.095 )
            {
                if ( TargetReachedAt < 0 )
                    TargetReachedAt = Iter;
                else if ( Iter - TargetReachedAt >= (FineGrid ? 100 : 50) )
                    break;
            }
            std::fill(gradientX_.begin(), gradientX_.end(), 0.0);
            std::fill(gradientY_.begin(), gradientY_.end(), 0.0);
            std::fill(densityGradientX_.begin(), densityGradientX_.end(), 0.0);
            std::fill(densityGradientY_.begin(), densityGradientY_.end(), 0.0);
            AddWirelengthGradient(Overflow);
            double Progress = pars_.iterations > 1
                ? std::min(1.0, Iter / static_cast<double>(pars_.iterations - 1)) : 1.0;
            AddDensityGradient();

            double WireNorm = 0.0, DensityNorm = 0.0;
            for ( int Id = 0; Id < static_cast<int>(points_.size()); ++Id )
            {
                if ( !points_[Id].movable )
                    continue;
                WireNorm += std::fabs(gradientX_[Id]) + std::fabs(gradientY_[Id]);
                DensityNorm += std::fabs(densityGradientX_[Id]) + std::fabs(densityGradientY_[Id]);
            }
            if ( Iter == 0 )
            {
                double ReferenceNorm = WireNorm > 1.0e-12 ? WireNorm : 1.0;
                DensityPenalty = pars_.densityWeight * ReferenceNorm
                               / std::max(1.0e-12, DensityNorm);
            }
            else if ( Overflow > 0.95 )
                DensityPenalty *= 1.05;
            else if ( Overflow > 0.60 )
                DensityPenalty *= 1.03;
            else if ( Overflow > 0.095 )
                DensityPenalty *= FineGrid ? 1.02 : 1.05;
            else
                DensityPenalty *= 0.98;
            for ( int Id = 0; Id < static_cast<int>(points_.size()); ++Id )
            {
                gradientX_[Id] += DensityPenalty * densityGradientX_[Id];
                gradientY_[Id] += DensityPenalty * densityGradientY_[Id];
            }
            Move(Progress, DensityPenalty);
        }
        SpreadToOverflow(0.095);
        RefineHpwlWithCapacity(pars_.refineRounds, 0.099);
        finalHpwl_ = Hpwl();
        finalOverflow_ = UpdateDensity();
        RebuildObjectIndex();
    }

    bool ImportMappedCoordinates(
        const std::unordered_map<Abc_Obj_t *, Pa_MappedSeed> & Seeds,
        double SourceWidth, double SourceHeight )
    {
        if ( !Abc_NtkIsStrash(pNtk_) || SourceWidth <= 0.0 || SourceHeight <= 0.0 )
            return false;
        const double MarginX = std::min(1.5, 0.5 * width_);
        const double Scale = std::min(width_ / SourceWidth,
                                      height_ / SourceHeight);
        const double OffsetX = 0.5 * (width_ - Scale * SourceWidth);
        const double OffsetY = 0.5 * (height_ - Scale * SourceHeight);
        Abc_Obj_t * pObj;
        int i;
        Abc_NtkForEachNode( pNtk_, pObj, i )
        {
            auto It = Seeds.find(pObj);
            if ( It == Seeds.end() )
                return false;
            Pa_Point & Point = points_[pObj->Id];
            Point.x = Clamp(OffsetX + Scale * It->second.x,
                            MarginX, width_ - MarginX);
            Point.y = Clamp(OffsetY + Scale * It->second.y,
                            0.5, height_ - 0.5);
        }
        inheritedClusters_ = true;
        finalHpwl_ = Hpwl();
        finalOverflow_ = UpdateDensity();
        RebuildObjectIndex();
        return true;
    }

    bool HasInheritedClusters( Abc_Ntk_t * pNtk ) const
    {
        return inheritedClusters_ && Matches(pNtk);
    }

    bool BeginEdit( Abc_Ntk_t * pNtk )
    {
        if ( editing_ || pNtk != pNtk_
          || (!passActive_ && !Matches(pNtk)) )
            return false;
        stagedRemoved_.clear();
        stagedRefreshed_.clear();
        stagedWritten_.clear();
        auditCurrentEdit_ = true;
        editing_ = true;
        return true;
    }

    bool BeginPass( Abc_Ntk_t * pNtk )
    {
        if ( editing_ || passActive_ || !Matches(pNtk) )
            return false;
        passHpwlScale_ = std::max(1.0,
            finalHpwl_ / std::max<size_t>(1, nets_.size()));
        passActive_ = true;
        return true;
    }

    bool EndPass( Abc_Ntk_t * pNtk )
    {
        if ( editing_ || !passActive_ || pNtk != pNtk_ )
            return false;
        fingerprint_ = ComputeFingerprint(pNtk);
        passActive_ = false;
        return true;
    }

    bool IsPassActive( Abc_Ntk_t * pNtk ) const
    {
        return passActive_ && !editing_ && pNtk == pNtk_;
    }

    bool IsEditing( Abc_Ntk_t * pNtk ) const
    {
        return editing_ && pNtk == pNtk_;
    }

    bool ReadObjectPosition( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj, double * pX, double * pY ) const
    {
        if ( pNtk != pNtk_ || pObj == nullptr )
            return false;
        auto It = objectPoints_.find(pObj);
        if ( It == objectPoints_.end() || !It->second.movable )
            return false;
        if ( pX ) *pX = It->second.x;
        if ( pY ) *pY = It->second.y;
        return true;
    }

    bool ReadObjectGeometry( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj,
                             double * pX, double * pY, double * pWidth,
                             double * pDensityHalfX, double * pDensityHalfY,
                             double * pDensityScale ) const
    {
        if ( pNtk != pNtk_ || pObj == nullptr )
            return false;
        auto It = objectPoints_.find(pObj);
        if ( It == objectPoints_.end() || !It->second.movable )
            return false;
        const Pa_Point & Point = It->second;
        if ( pX ) *pX = Point.x;
        if ( pY ) *pY = Point.y;
        if ( pWidth ) *pWidth = Point.width;
        if ( pDensityHalfX ) *pDensityHalfX = Point.densityHalfX;
        if ( pDensityHalfY ) *pDensityHalfY = Point.densityHalfY;
        if ( pDensityScale ) *pDensityScale = Point.densityScale;
        return true;
    }

    bool WriteObjectPosition( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj, double X, double Y )
    {
        if ( !IsEditing(pNtk) || pObj == nullptr || !Abc_ObjIsNode(pObj)
          || !std::isfinite(X) || !std::isfinite(Y) )
            return false;
        auto Old = objectPoints_.find(pObj);
        if ( Old != objectPoints_.end() && !stagedRemoved_.count(pObj)
          && !stagedRefreshed_.count(pObj) )
            stagedRefreshed_.emplace(pObj, Old->second);
        Pa_Point & Point = objectPoints_[pObj];
        Point.object = pObj;
        Point.movable = true;
        Point.width = Abc_ObjFaninC0(pObj) && Abc_ObjFaninC1(pObj) ? 2.0 : 3.0;
        Point.x = Clamp(X, 0.5 * Point.width, width_ - 0.5 * Point.width);
        Point.y = Clamp(Y, 0.5, height_ - 0.5);
        const double SqrtTwo = std::sqrt(2.0);
        Point.densityHalfX = std::max(0.5 * Point.width, 0.5 * SqrtTwo * binSizeX_);
        Point.densityHalfY = std::max(0.5, 0.5 * SqrtTwo * binSizeY_);
        Point.densityScale = Point.width /
            (4.0 * Point.densityHalfX * Point.densityHalfY);
        stagedWritten_.insert(pObj);
        return true;
    }

    bool StageObjectRemoval( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj )
    {
        if ( !IsEditing(pNtk) || pObj == nullptr )
            return false;
        auto It = objectPoints_.find(pObj);
        if ( It == objectPoints_.end() )
            return false;
        stagedRefreshed_.erase(pObj);
        stagedRemoved_.emplace(pObj, It->second);
        return true;
    }

    bool StageObjectRefresh( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj )
    {
        if ( !IsEditing(pNtk) || pObj == nullptr
          || stagedRemoved_.count(pObj) )
            return false;
        auto It = objectPoints_.find(pObj);
        if ( It == objectPoints_.end() )
            return false;
        stagedRefreshed_.emplace(pObj, It->second);
        return true;
    }

    bool FinishLocalEdit( Abc_Ntk_t * pNtk, double HpwlReduction )
    {
        if ( !IsEditing(pNtk) || !passActive_ || !std::isfinite(HpwlReduction) )
            return false;

        std::unordered_map<Abc_Obj_t *, Pa_Point> Written;
        for ( Abc_Obj_t * pObject : stagedWritten_ )
        {
            auto It = objectPoints_.find(pObject);
            if ( It == objectPoints_.end() )
                return false;
            Written.emplace(pObject, It->second);
        }

        // Density deposits are applied in geometric order, independent of
        // the pointer-hash order of the staged sets.
        std::vector<std::pair<Pa_Point, double>> Deposits;
        for ( const auto & Entry : stagedRemoved_ )
        {
            Deposits.push_back({Entry.second, -1.0});
            totalCellArea_ -= Entry.second.width;
            objectPoints_.erase(Entry.first);
        }
        for ( const auto & Entry : stagedRefreshed_ )
        {
            Deposits.push_back({Entry.second, -1.0});
            totalCellArea_ -= Entry.second.width;
            if ( Written.count(Entry.first) )
                continue;
            if ( Abc_ObjIsNode(Entry.first) )
            {
                Pa_Point Point = Entry.second;
                SetObjectGeometry(Point, Entry.first);
                objectPoints_[Entry.first] = Point;
                Deposits.push_back({Point, 1.0});
                totalCellArea_ += Point.width;
            }
            else
                objectPoints_.erase(Entry.first);
        }
        for ( const auto & Entry : Written )
        {
            objectPoints_[Entry.first] = Entry.second;
            Deposits.push_back({Entry.second, 1.0});
            totalCellArea_ += Entry.second.width;
        }
        auto Key = []( const std::pair<Pa_Point, double> & d )
        {
            const Pa_Point & x = d.first;
            return std::array<double, 7>{x.x, x.y, x.width, x.densityHalfX, x.densityHalfY,
                                         x.densityScale, d.second};
        };
        std::sort(Deposits.begin(), Deposits.end(),
            [&Key]( const std::pair<Pa_Point, double> & a, const std::pair<Pa_Point, double> & b )
            { return Key(a) < Key(b); });
        for ( const auto & Entry : Deposits )
            UpdateRawDensity(Entry.first, Entry.second);

        finalHpwl_ -= HpwlReduction;
        finalOverflow_ = overflowArea_ / std::max(1.0, totalCellArea_);
        nodeCount_ = static_cast<int>(objectPoints_.size());
        stagedRemoved_.clear();
        stagedRefreshed_.clear();
        stagedWritten_.clear();
        editing_ = false;
        return std::isfinite(finalHpwl_) && std::isfinite(finalOverflow_);
    }

    bool FinishGlobalEdit( Abc_Ntk_t * pNtk )
    {
        if ( !IsEditing(pNtk) || !passActive_ )
            return false;
        auditCurrentEdit_ = false;
        return FinishEdit(pNtk);
    }

    bool FinishEdit( Abc_Ntk_t * pNtk )
    {
        if ( !IsEditing(pNtk) )
            return false;
        double ExpectedHpwl = finalHpwl_;
        bool AuditHpwl = passActive_ && auditCurrentEdit_;
        std::vector<Pa_Point> NewPoints(Abc_NtkObjNumMax(pNtk));
        Abc_Obj_t * pObj;
        int i;
        Abc_NtkForEachNode( pNtk, pObj, i )
        {
            auto It = objectPoints_.find(pObj);
            if ( It == objectPoints_.end() )
            {
                editing_ = false;
                return false;
            }
            Pa_Point Point = It->second;
            Point.object = pObj;
            NewPoints[pObj->Id] = Point;
        }
        points_.swap(NewPoints);
        nodeCount_ = Abc_NtkNodeNum(pNtk);
        totalCellArea_ = 0.0;
        bool IsMapped = Abc_NtkHasMapping(pNtk);
        for ( Pa_Point & Point : points_ )
        {
            if ( !Point.movable || Point.object == nullptr )
                continue;
            if ( IsMapped )
            {
                Mio_Gate_t * pGate = static_cast<Mio_Gate_t *>(Point.object->pData);
                Point.width = pGate ? std::max(0.0, Mio_GateReadArea(pGate)) : 0.0;
            }
            else
                Point.width = Abc_ObjFaninC0(Point.object) && Abc_ObjFaninC1(Point.object) ? 2.0 : 3.0;
            totalCellArea_ += Point.width;
        }
        // Fillers keep their positions across the rebuild.
        auto PreviousFillers = fillers_;
        InitializeDensityModel();
        for ( size_t k = 0; k < std::min(PreviousFillers.size(), fillers_.size()); ++k )
        {
            fillers_[k].x = PreviousFillers[k].x;
            fillers_[k].y = PreviousFillers[k].y;
        }
        nets_.clear();
        incidentNets_.clear();
        wirePrecondition_.clear();
        BuildNetlist();
        gradientX_.assign(points_.size(), 0.0);
        gradientY_.assign(points_.size(), 0.0);
        densityGradientX_.assign(points_.size(), 0.0);
        densityGradientY_.assign(points_.size(), 0.0);
        finalHpwl_ = Hpwl();
        finalOverflow_ = UpdateDensity();
        if ( !passActive_ )
            fingerprint_ = ComputeFingerprint(pNtk);
        RebuildObjectIndex();
        editing_ = false;
        if ( AuditHpwl && std::fabs(finalHpwl_ - ExpectedHpwl)
             > 1.0e-7 * (1.0 + std::max(std::fabs(finalHpwl_), std::fabs(ExpectedHpwl))) )
        {
            Abc_Print( -1, "placement error: incremental HPWL %.9f, recomputed %.9f.\n",
                ExpectedHpwl, finalHpwl_ );
            return false;
        }
        return true;
    }

    bool ReadCanvas( Abc_Ntk_t * pNtk, double * pWidth, double * pHeight,
                     int * pBins, double * pBinSizeX, double * pBinSizeY ) const
    {
        if ( pNtk != pNtk_ || (!editing_ && !passActive_ && !Matches(pNtk)) )
            return false;
        if ( pWidth ) *pWidth = width_;
        if ( pHeight ) *pHeight = height_;
        if ( pBins ) *pBins = bins_;
        if ( pBinSizeX ) *pBinSizeX = binSizeX_;
        if ( pBinSizeY ) *pBinSizeY = binSizeY_;
        return true;
    }

    bool ReadDensityBin( Abc_Ntk_t * pNtk, int BinX, int BinY,
                         double * pCellArea, double * pTargetArea ) const
    {
        if ( pNtk != pNtk_ || (!editing_ && !passActive_ && !Matches(pNtk))
          || BinX < 0 || BinX >= bins_ || BinY < 0 || BinY >= bins_ )
            return false;
        if ( pCellArea ) *pCellArea = rawDensity_[BinX * bins_ + BinY];
        if ( pTargetArea ) *pTargetArea = targetAreaPerBin_;
        return true;
    }

    bool ReadMetrics( Abc_Ntk_t * pNtk, double * pHpwl,
                      double * pOverflow, double * pHpwlScale,
                      double * pCellArea ) const
    {
        if ( pNtk != pNtk_ || (!editing_ && !passActive_ && !Matches(pNtk)) )
            return false;
        if ( pHpwl ) *pHpwl = finalHpwl_;
        if ( pOverflow ) *pOverflow = finalOverflow_;
        if ( pHpwlScale )
            *pHpwlScale = passActive_ ? passHpwlScale_
                : std::max(1.0, finalHpwl_ / std::max<size_t>(1, nets_.size()));
        if ( pCellArea ) *pCellArea = totalCellArea_;
        return true;
    }

    bool Matches( Abc_Ntk_t * pNtk ) const
    {
        return pNtk == pNtk_
            && pNtk != nullptr
            && Abc_NtkNodeNum(pNtk) == nodeCount_
            && Abc_NtkObjNumMax(pNtk) == static_cast<int>(points_.size())
            && ComputeFingerprint(pNtk) == fingerprint_;
    }

  private:
    static uint64_t ComputeFingerprint( Abc_Ntk_t * pNtk )
    {
        uint64_t HashValue = 1469598103934665603ULL;
        auto Mix = [&]( uint64_t Value ) {
            HashValue ^= Value;
            HashValue *= 1099511628211ULL;
        };
        Mix(static_cast<uint64_t>(Abc_NtkNodeNum(pNtk)));
        Mix(static_cast<uint64_t>(Abc_NtkObjNumMax(pNtk)));
        Mix(static_cast<uint64_t>(Abc_NtkHasMapping(pNtk)));
        Abc_Obj_t * pObj;
        int i;
        Abc_NtkForEachNode( pNtk, pObj, i )
        {
            Mix(static_cast<uint64_t>(pObj->Id));
            Mix(static_cast<uint64_t>(Abc_ObjFaninNum(pObj)));
            for ( int k = 0; k < Abc_ObjFaninNum(pObj); ++k )
                Mix(static_cast<uint64_t>(Abc_ObjFaninId(pObj, k)));
            if ( Abc_NtkIsStrash(pNtk) )
            {
                Mix(static_cast<uint64_t>(Abc_ObjFaninC0(pObj)));
                Mix(static_cast<uint64_t>(Abc_ObjFaninC1(pObj)));
            }
            else if ( Abc_NtkHasMapping(pNtk) )
                Mix(static_cast<uint64_t>(reinterpret_cast<uintptr_t>(pObj->pData)));
        }
        return HashValue;
    }

    int ChooseBinCount() const
    {
        double AverageCellArea = totalCellArea_ / std::max(1, nodeCount_);
        double IdealBinCount = width_ * height_ / std::max(1.0e-12, AverageCellArea);
        int Bins = 8;
        // Finer grids make every spectral solve more expensive without
        // better placements; 128 bins is RePlAce's default scale.
        while ( Bins < 128 && 4.0 * Bins * Bins <= IdealBinCount )
            Bins *= 2;
        return Bins;
    }

    static unsigned Hash( unsigned Value )
    {
        Value ^= Value >> 16;
        Value *= 0x7feb352dU;
        Value ^= Value >> 15;
        Value *= 0x846ca68bU;
        Value ^= Value >> 16;
        return Value;
    }

    void InitializeCellSizes()
    {
        bool IsMapped = Abc_NtkHasMapping(pNtk_);
        Abc_Obj_t * pObj;
        int i;
        Abc_NtkForEachNode( pNtk_, pObj, i )
        {
            Pa_Point & Point = points_[pObj->Id];
            Point.object = pObj;
            Point.movable = true;
            if ( IsMapped )
            {
                Mio_Gate_t * pGate = static_cast<Mio_Gate_t *>(pObj->pData);
                Point.width = pGate ? std::max(0.0, Mio_GateReadArea(pGate)) : 0.0;
            }
            else
                Point.width = Abc_ObjFaninC0(pObj) && Abc_ObjFaninC1(pObj) ? 2.0 : 3.0;
            totalCellArea_ += Point.width;
        }
    }

    void RebuildObjectIndex()
    {
        objectPoints_.clear();
        for ( const Pa_Point & Point : points_ )
            if ( Point.movable && Point.object != nullptr )
                objectPoints_.emplace(Point.object, Point);
    }

    void BuildNetlist()
    {
        incidentNets_.resize(points_.size());
        wirePrecondition_.resize(points_.size(), 0.0);
        Abc_Obj_t * pObj;
        int i;
        std::vector<int> Pins;
        Abc_NtkForEachObj( pNtk_, pObj, i )
        {
            if ( !Abc_ObjIsNode(pObj) && !Abc_ObjIsCi(pObj) )
                continue;
            CollectNetPins(pObj, Pins);
            if ( Pins.size() < 2 )
                continue;
            int NetIndex = static_cast<int>(nets_.size());
            nets_.push_back(Pa_Net{Pins});
            for ( int Id : Pins )
                incidentNets_[Id].push_back(NetIndex);
        }
        for ( int Id = 0; Id < static_cast<int>(points_.size()); ++Id )
            if ( points_[Id].movable )
                wirePrecondition_[Id] = std::max(1.0, static_cast<double>(incidentNets_[Id].size()));
    }

    void InitializeDensityModel()
    {
        const double SqrtTwo = std::sqrt(2.0);
        for ( Pa_Point & Point : points_ )
        {
            if ( !Point.movable )
                continue;
            Point.densityHalfX = std::max(0.5 * Point.width, 0.5 * SqrtTwo * binSizeX_);
            Point.densityHalfY = std::max(0.5, 0.5 * SqrtTwo * binSizeY_);
            Point.densityScale = Point.width /
                (4.0 * Point.densityHalfX * Point.densityHalfY);
        }

        std::vector<double> Widths;
        Widths.reserve(nodeCount_);
        for ( const Pa_Point & Point : points_ )
            if ( Point.movable )
                Widths.push_back(Point.width);
        std::sort(Widths.begin(), Widths.end());
        size_t Begin = static_cast<size_t>(0.05 * Widths.size());
        size_t End = static_cast<size_t>(0.95 * Widths.size());
        if ( End <= Begin )
        {
            Begin = 0;
            End = Widths.size();
        }
        double FillerWidth = 0.0;
        for ( size_t i = Begin; i < End; ++i )
            FillerWidth += Widths[i];
        FillerWidth /= std::max<size_t>(1, End - Begin);
        // A pass may remove every AND. Zero-area mapped cells also have no
        // positive representative filler width; do not divide by it or cast
        // an infinite/NaN filler count to int. Discard any old fillers as well.
        if ( FillerWidth <= 0.0 )
        {
            fillers_.clear();
            return;
        }
        double FillerArea = std::max(0.0, width_ * height_ - totalCellArea_);
        int FillerCount = static_cast<int>(FillerArea / FillerWidth + 0.5);
        fillers_.resize(FillerCount);
        for ( int i = 0; i < FillerCount; ++i )
        {
            Pa_Point & Filler = fillers_[i];
            Filler.width = FillerWidth;
            Filler.densityHalfX = std::max(0.5 * Filler.width, 0.5 * SqrtTwo * binSizeX_);
            Filler.densityHalfY = std::max(0.5, 0.5 * SqrtTwo * binSizeY_);
            Filler.densityScale = Filler.width /
                (4.0 * Filler.densityHalfX * Filler.densityHalfY);
            Filler.movable = true;
            unsigned HashX = Hash(static_cast<unsigned>(i) ^ 0x68bc21ebU);
            unsigned HashY = Hash(HashX ^ 0x9e3779b9U);
            double UnitX = (HashX + 0.5) / 4294967296.0;
            double UnitY = (HashY + 0.5) / 4294967296.0;
            Filler.x = Filler.densityHalfX
                + UnitX * std::max(0.0, width_ - 2.0 * Filler.densityHalfX);
            Filler.y = Filler.densityHalfY
                + UnitY * std::max(0.0, height_ - 2.0 * Filler.densityHalfY);
        }
    }

    void InitializeCoordinates()
    {
        Abc_Obj_t * pObj;
        int i;
        Abc_NtkForEachNode( pNtk_, pObj, i )
        {
            Pa_Point & Point = points_[pObj->Id];
            unsigned HashX = Hash(static_cast<unsigned>(pObj->Id));
            unsigned HashY = Hash(HashX ^ 0x9e3779b9U);
            double JitterX = ((HashX & 65535U) / 65535.0 - 0.5) * 0.25 * binSizeX_;
            double JitterY = ((HashY & 65535U) / 65535.0 - 0.5) * 0.25 * binSizeY_;
            Point.x = Clamp(0.5 * width_ + JitterX,
                            Point.densityHalfX, width_ - Point.densityHalfX);
            Point.y = Clamp(0.5 * height_ + JitterY,
                            Point.densityHalfY, height_ - Point.densityHalfY);
        }
    }

    static double Clamp( double Value, double Low, double High )
    {
        return std::max(Low, std::min(High, Value));
    }

    void CollectNetPins( Abc_Obj_t * pDriver, std::vector<int> & Pins ) const
    {
        Abc_Obj_t * pFanout;
        int k;
        Pins.clear();
        if ( Abc_ObjIsNode(pDriver) && points_[pDriver->Id].movable )
            Pins.push_back(pDriver->Id);
        Abc_ObjForEachFanout( pDriver, pFanout, k )
            if ( Abc_ObjIsNode(pFanout) && points_[pFanout->Id].movable )
                Pins.push_back(pFanout->Id);
    }

    double Hpwl() const
    {
        double Total = 0.0;
        for ( const Pa_Net & Net : nets_ )
        {
            double MinX = std::numeric_limits<double>::max();
            double MinY = std::numeric_limits<double>::max();
            double MaxX = std::numeric_limits<double>::lowest();
            double MaxY = std::numeric_limits<double>::lowest();
            for ( int Id : Net.pins )
            {
                MinX = std::min(MinX, points_[Id].x);
                MinY = std::min(MinY, points_[Id].y);
                MaxX = std::max(MaxX, points_[Id].x);
                MaxY = std::max(MaxY, points_[Id].y);
            }
            Total += MaxX - MinX + MaxY - MinY;
        }
        return Total;
    }

    // The weighted-average wirelength gradient specialized to two-pin nets,
    // which dominate AIG placement.
    static void AddTwoPinAxis( double X0, double X1, double Coefficient,
                               double & Gradient0, double & Gradient1 )
    {
        double Low = std::min(X0, X1), High = std::max(X0, X1);
        double Span = Low == High ? 1.0 : std::exp((Low - High) * Coefficient);
        double Pos0 = X0 == High ? 1.0 : Span;
        double Pos1 = X1 == High ? 1.0 : Span;
        double Neg0 = X0 == Low ? 1.0 : Span;
        double Neg1 = X1 == Low ? 1.0 : Span;
        double SumPos = Pos0 + Pos1, SumNeg = Neg0 + Neg1;
        double NumPos = X0 * Pos0, NumNeg = X0 * Neg0;
        NumPos += X1 * Pos1; NumNeg += X1 * Neg1;
        double WeightedMax = NumPos / SumPos, WeightedMin = NumNeg / SumNeg;
        double GradMax0 = Pos0 / SumPos * (1.0 + Coefficient * (X0 - WeightedMax));
        double GradMin0 = Neg0 / SumNeg * (1.0 - Coefficient * (X0 - WeightedMin));
        double GradMax1 = Pos1 / SumPos * (1.0 + Coefficient * (X1 - WeightedMax));
        double GradMin1 = Neg1 / SumNeg * (1.0 - Coefficient * (X1 - WeightedMin));
        Gradient0 += GradMax0 - GradMin0;
        Gradient1 += GradMax1 - GradMin1;
    }

    void AddWirelengthGradient( double Overflow )
    {
        double BinAverage = 0.5 * (binSizeX_ + binSizeY_);
        double WlMultiplier = Overflow > 1.0 ? 0.1
            : Overflow < 0.1 ? 100.0
            : 1.0 / std::pow(10.0, (Overflow - 0.1) * 10.0 / 3.0 - 2.0);
        double Coefficient = 0.1 * WlMultiplier / BinAverage;

        auto & PosX = wirePosX_; auto & NegX = wireNegX_;
        auto & PosY = wirePosY_; auto & NegY = wireNegY_;
        for ( const Pa_Net & Net : nets_ )
        {
            size_t Count = Net.pins.size();
            if ( Count == 2 )
            {
                int Id0 = Net.pins[0], Id1 = Net.pins[1];
                AddTwoPinAxis(points_[Id0].x, points_[Id1].x, Coefficient,
                              gradientX_[Id0], gradientX_[Id1]);
                AddTwoPinAxis(points_[Id0].y, points_[Id1].y, Coefficient,
                              gradientY_[Id0], gradientY_[Id1]);
                continue;
            }
            if ( PosX.size() < Count ) {
                PosX.resize(Count); NegX.resize(Count);
                PosY.resize(Count); NegY.resize(Count);
            }
            double MaxX = std::numeric_limits<double>::lowest();
            double MaxY = std::numeric_limits<double>::lowest();
            double MinX = std::numeric_limits<double>::max();
            double MinY = std::numeric_limits<double>::max();
            for ( int Id : Net.pins )
            {
                MaxX = std::max(MaxX, points_[Id].x);
                MaxY = std::max(MaxY, points_[Id].y);
                MinX = std::min(MinX, points_[Id].x);
                MinY = std::min(MinY, points_[Id].y);
            }
            // Both extrema use the same exp((min-max)*coefficient); compute it
            // once per axis.
            double SpanX = MinX == MaxX ? 1.0 : std::exp((MinX - MaxX) * Coefficient);
            double SpanY = MinY == MaxY ? 1.0 : std::exp((MinY - MaxY) * Coefficient);
            double SumPosX = 0.0, SumNegX = 0.0, SumPosY = 0.0, SumNegY = 0.0;
            double NumPosX = 0.0, NumNegX = 0.0, NumPosY = 0.0, NumNegY = 0.0;
            for ( size_t k = 0; k < Count; ++k )
            {
                const Pa_Point & Point = points_[Net.pins[k]];
                PosX[k] = Point.x == MaxX ? 1.0 : Point.x == MinX ? SpanX
                    : std::exp((Point.x - MaxX) * Coefficient);
                NegX[k] = Point.x == MinX ? 1.0 : Point.x == MaxX ? SpanX
                    : std::exp((MinX - Point.x) * Coefficient);
                PosY[k] = Point.y == MaxY ? 1.0 : Point.y == MinY ? SpanY
                    : std::exp((Point.y - MaxY) * Coefficient);
                NegY[k] = Point.y == MinY ? 1.0 : Point.y == MaxY ? SpanY
                    : std::exp((MinY - Point.y) * Coefficient);
                SumPosX += PosX[k]; NumPosX += Point.x * PosX[k];
                SumNegX += NegX[k]; NumNegX += Point.x * NegX[k];
                SumPosY += PosY[k]; NumPosY += Point.y * PosY[k];
                SumNegY += NegY[k]; NumNegY += Point.y * NegY[k];
            }
            double WeightedMaxX = NumPosX / SumPosX;
            double WeightedMinX = NumNegX / SumNegX;
            double WeightedMaxY = NumPosY / SumPosY;
            double WeightedMinY = NumNegY / SumNegY;
            for ( size_t k = 0; k < Count; ++k )
            {
                int Id = Net.pins[k];
                const Pa_Point & Point = points_[Id];
                double GradMaxX = PosX[k] / SumPosX
                    * (1.0 + Coefficient * (Point.x - WeightedMaxX));
                double GradMinX = NegX[k] / SumNegX
                    * (1.0 - Coefficient * (Point.x - WeightedMinX));
                double GradMaxY = PosY[k] / SumPosY
                    * (1.0 + Coefficient * (Point.y - WeightedMaxY));
                double GradMinY = NegY[k] / SumNegY
                    * (1.0 - Coefficient * (Point.y - WeightedMinY));
                gradientX_[Id] += GradMaxX - GradMinX;
                gradientY_[Id] += GradMaxY - GradMinY;
            }
        }
    }

    int BinIndexX( double Coord ) const
    {
        return std::max(0, std::min(bins_ - 1, static_cast<int>(Coord / binSizeX_)));
    }

    int BinIndexY( double Coord ) const
    {
        return std::max(0, std::min(bins_ - 1, static_cast<int>(Coord / binSizeY_)));
    }

    void SetObjectGeometry( Pa_Point & Point, Abc_Obj_t * pObject ) const
    {
        Point.object = pObject;
        Point.movable = true;
        if ( Abc_NtkHasMapping(pNtk_) )
        {
            Mio_Gate_t * pGate = static_cast<Mio_Gate_t *>(pObject->pData);
            Point.width = pGate ? std::max(0.0, Mio_GateReadArea(pGate)) : 0.0;
        }
        else
            Point.width = Abc_ObjFaninC0(pObject) && Abc_ObjFaninC1(pObject) ? 2.0 : 3.0;
        const double SqrtTwo = std::sqrt(2.0);
        Point.densityHalfX = std::max(0.5 * Point.width, 0.5 * SqrtTwo * binSizeX_);
        Point.densityHalfY = std::max(0.5, 0.5 * SqrtTwo * binSizeY_);
        Point.densityScale = Point.width /
            (4.0 * Point.densityHalfX * Point.densityHalfY);
    }

    void UpdateRawDensity( const Pa_Point & Point, double Sign )
    {
        std::vector<std::pair<int, double>> Contributions;
        CellContributions(Point, Point.x, Point.y, Contributions);
        for ( const auto & Entry : Contributions )
        {
            double Before = rawDensity_[Entry.first];
            double After = Before + Sign * Entry.second;
            overflowArea_ += std::max(0.0, After - targetAreaPerBin_)
                           - std::max(0.0, Before - targetAreaPerBin_);
            rawDensity_[Entry.first] = std::fabs(After) < 1.0e-12 ? 0.0 : After;
        }
    }

    void AddDensityContribution( const Pa_Point & Point,
                                 std::vector<double> & Grid ) const
    {
        double X0 = Point.x - Point.densityHalfX;
        double X1 = Point.x + Point.densityHalfX;
        double Y0 = Point.y - Point.densityHalfY;
        double Y1 = Point.y + Point.densityHalfY;
        int BinX0 = BinIndexX(X0);
        int BinX1 = BinIndexX(Pa_PreviousBoundary(X1, X0));
        int BinY0 = BinIndexY(Y0);
        int BinY1 = BinIndexY(Pa_PreviousBoundary(Y1, Y0));
        for ( int X = BinX0; X <= BinX1; ++X )
        for ( int Y = BinY0; Y <= BinY1; ++Y )
        {
            double OverlapX = std::max(0.0, std::min(X1, (X + 1) * binSizeX_)
                                          - std::max(X0, X * binSizeX_));
            double OverlapY = std::max(0.0, std::min(Y1, (Y + 1) * binSizeY_)
                                          - std::max(Y0, Y * binSizeY_));
            Grid[X * bins_ + Y] += OverlapX * OverlapY * Point.densityScale;
        }
    }

    double UpdateDensity()
    {
        std::fill(rawDensity_.begin(), rawDensity_.end(), 0.0);
        std::fill(density_.begin(), density_.end(), 0.0);
        for ( const Pa_Point & Point : points_ )
            if ( Point.movable )
                AddDensityContribution(Point, rawDensity_);
        for ( const Pa_Point & Filler : fillers_ )
            AddDensityContribution(Filler, density_);

        double OverflowArea = 0.0;
        for ( int Bin = 0; Bin < bins_ * bins_; ++Bin )
        {
            OverflowArea += std::max(0.0, rawDensity_[Bin] - targetAreaPerBin_);
            density_[Bin] = (density_[Bin] + rawDensity_[Bin])
                          / std::max(1.0e-9, targetAreaPerBin_);
        }
        overflowArea_ = OverflowArea;
        return OverflowArea / std::max(1.0, totalCellArea_);
    }

    int GridIndex( int X, int Y ) const
    {
        X = std::max(0, std::min(bins_ - 1, X));
        Y = std::max(0, std::min(bins_ - 1, Y));
        return X * bins_ + Y;
    }

    double InterpolateField( const std::vector<double> & Field, double X, double Y ) const
    {
        double GridX = X / binSizeX_ - 0.5;
        double GridY = Y / binSizeY_ - 0.5;
        int X0 = static_cast<int>(std::floor(GridX));
        int Y0 = static_cast<int>(std::floor(GridY));
        double Fx = GridX - X0;
        double Fy = GridY - Y0;
        return (1.0 - Fx) * (1.0 - Fy) * Field[GridIndex(X0, Y0)]
             + Fx * (1.0 - Fy) * Field[GridIndex(X0 + 1, Y0)]
             + (1.0 - Fx) * Fy * Field[GridIndex(X0, Y0 + 1)]
             + Fx * Fy * Field[GridIndex(X0 + 1, Y0 + 1)];
    }

    void CellContributions( const Pa_Point & Point, double CenterX, double CenterY,
                            std::vector<std::pair<int, double>> & Contributions ) const
    {
        Contributions.clear();
        double X0 = CenterX - Point.densityHalfX;
        double X1 = CenterX + Point.densityHalfX;
        double Y0 = CenterY - Point.densityHalfY;
        double Y1 = CenterY + Point.densityHalfY;
        int BinX0 = BinIndexX(X0);
        int BinX1 = BinIndexX(Pa_PreviousBoundary(X1, X0));
        int BinY0 = BinIndexY(Y0);
        int BinY1 = BinIndexY(Pa_PreviousBoundary(Y1, Y0));
        for ( int X = BinX0; X <= BinX1; ++X )
        for ( int Y = BinY0; Y <= BinY1; ++Y )
        {
            double OverlapX = std::max(0.0, std::min(X1, (X + 1) * binSizeX_)
                                          - std::max(X0, X * binSizeX_));
            double OverlapY = std::max(0.0, std::min(Y1, (Y + 1) * binSizeY_)
                                          - std::max(Y0, Y * binSizeY_));
            Contributions.emplace_back(GridIndex(X, Y),
                                       OverlapX * OverlapY * Point.densityScale);
        }
    }

    // During one cell move the other pins are fixed. Retain one box per
    // incident net instead of rescanning every pin for all six trial moves.
    // Rebuild for the next cell, since an accepted move changes its neighbors.
    struct Pa_FixedBox
    {
        double minX = std::numeric_limits<double>::max();
        double minY = std::numeric_limits<double>::max();
        double maxX = std::numeric_limits<double>::lowest();
        double maxY = std::numeric_limits<double>::lowest();
        void Add( const Pa_Point & Point )
        {
            minX = std::min(minX, Point.x); minY = std::min(minY, Point.y);
            maxX = std::max(maxX, Point.x); maxY = std::max(maxY, Point.y);
        }
    };

    static double LocalHpwl( const std::vector<Pa_FixedBox> & Boxes,
                             double X, double Y )
    {
        double Total = 0.0;
        for ( const Pa_FixedBox & Box : Boxes )
            Total += std::max(Box.maxX, X) - std::min(Box.minX, X)
                   + std::max(Box.maxY, Y) - std::min(Box.minY, Y);
        return Total;
    }

    void RefineHpwlWithCapacity( int Rounds, double OverflowLimit )
    {
        if ( Rounds == 0 )
            return;
        std::vector<double> Occupancy(bins_ * bins_, 0.0);
        std::vector<std::pair<int, double>> Contributions;
        for ( const Pa_Point & Point : points_ )
        {
            if ( !Point.movable )
                continue;
            CellContributions(Point, Point.x, Point.y, Contributions);
            for ( const auto & Entry : Contributions )
                Occupancy[Entry.first] += Entry.second;
        }
        double OverflowArea = 0.0;
        for ( double Value : Occupancy )
            OverflowArea += std::max(0.0, Value - targetAreaPerBin_);
        double LimitArea = OverflowLimit * totalCellArea_;

        std::vector<int> Ids;
        Ids.reserve(nodeCount_);
        for ( int Id = 0; Id < static_cast<int>(points_.size()); ++Id )
            if ( points_[Id].movable )
                Ids.push_back(Id);
        std::vector<double> CandidateXs, CandidateYs;
        std::vector<Pa_FixedBox> FixedBoxes;
        std::vector<std::pair<int, double>> OldParts, NewParts, Deltas;
        for ( int Round = 0; Round < Rounds; ++Round )
        {
            int Moved = 0;
            if ( Round & 1 )
                std::reverse(Ids.begin(), Ids.end());
            for ( int Id : Ids )
            {
                Pa_Point & Point = points_[Id];
                const std::vector<int> & IncidentNets = incidentNets_[Id];
                CandidateXs.clear();
                CandidateYs.clear();
                FixedBoxes.clear();
                for ( int NetIndex : IncidentNets )
                {
                    FixedBoxes.emplace_back();
                    const std::vector<int> & NetPins = nets_[NetIndex].pins;
                    for ( int Other : NetPins )
                    {
                        if ( Other == Id )
                            continue;
                        FixedBoxes.back().Add(points_[Other]);
                        CandidateXs.push_back(points_[Other].x);
                        CandidateYs.push_back(points_[Other].y);
                    }
                }
                if ( CandidateXs.empty() )
                    continue;
                size_t Middle = CandidateXs.size() / 2;
                std::nth_element(CandidateXs.begin(), CandidateXs.begin() + Middle, CandidateXs.end());
                std::nth_element(CandidateYs.begin(), CandidateYs.begin() + Middle, CandidateYs.end());
                double TargetX = Clamp(CandidateXs[Middle], Point.densityHalfX,
                                       width_ - Point.densityHalfX);
                double TargetY = Clamp(CandidateYs[Middle], Point.densityHalfY,
                                       height_ - Point.densityHalfY);
                double OldCost = LocalHpwl(FixedBoxes, Point.x, Point.y);
                CellContributions(Point, Point.x, Point.y, OldParts);
                for ( double Alpha = 1.0; Alpha >= 0.03125; Alpha *= 0.5 )
                {
                    double NewX = (1.0 - Alpha) * Point.x + Alpha * TargetX;
                    double NewY = (1.0 - Alpha) * Point.y + Alpha * TargetY;
                    if ( LocalHpwl(FixedBoxes, NewX, NewY) >= OldCost - 1.0e-9 )
                        continue;
                    CellContributions(Point, NewX, NewY, NewParts);
                    Deltas.clear();
                    auto AddDelta = [&]( int Bin, double Delta ) {
                        for ( auto & Entry : Deltas )
                            if ( Entry.first == Bin )
                            {
                                Entry.second += Delta;
                                return;
                            }
                        Deltas.emplace_back(Bin, Delta);
                    };
                    for ( const auto & Entry : OldParts ) AddDelta(Entry.first, -Entry.second);
                    for ( const auto & Entry : NewParts ) AddDelta(Entry.first, Entry.second);
                    double NewOverflowArea = OverflowArea;
                    for ( const auto & Entry : Deltas )
                    {
                        double OldOverflow = std::max(0.0, Occupancy[Entry.first] - targetAreaPerBin_);
                        double NewOverflow = std::max(0.0, Occupancy[Entry.first] + Entry.second - targetAreaPerBin_);
                        NewOverflowArea += NewOverflow - OldOverflow;
                    }
                    if ( NewOverflowArea > LimitArea + 1.0e-9 )
                        continue;
                    for ( const auto & Entry : Deltas )
                        Occupancy[Entry.first] += Entry.second;
                    OverflowArea = NewOverflowArea;
                    Point.x = NewX;
                    Point.y = NewY;
                    ++Moved;
                    break;
                }
            }
            if ( Round & 1 )
                std::reverse(Ids.begin(), Ids.end());
            if ( Moved == 0 )
                break;
        }
    }

    void SpreadToOverflow( double TargetOverflow )
    {
        double CurrentOverflow = UpdateDensity();
        if ( CurrentOverflow <= TargetOverflow )
            return;
        std::vector<double> BaseX(points_.size()), BaseY(points_.size());
        for ( int Id = 0; Id < static_cast<int>(points_.size()); ++Id )
        {
            BaseX[Id] = points_[Id].x;
            BaseY[Id] = points_[Id].y;
        }
        auto ApplyScale = [&]( double Scale ) {
            for ( int Id = 0; Id < static_cast<int>(points_.size()); ++Id )
            {
                Pa_Point & Point = points_[Id];
                if ( !Point.movable )
                    continue;
                Point.x = Clamp(0.5 * width_ + Scale * (BaseX[Id] - 0.5 * width_),
                                Point.densityHalfX, width_ - Point.densityHalfX);
                Point.y = Clamp(0.5 * height_ + Scale * (BaseY[Id] - 0.5 * height_),
                                Point.densityHalfY, height_ - Point.densityHalfY);
            }
            return UpdateDensity();
        };

        double Low = 1.0, High = 1.0;
        double BestScale = 1.0, BestOverflow = CurrentOverflow;
        for ( int Step = 1; Step <= 50; ++Step )
        {
            double Scale = 1.0 + 0.01 * Step;
            double Overflow = ApplyScale(Scale);
            if ( Overflow < BestOverflow )
            {
                BestOverflow = Overflow;
                BestScale = Scale;
            }
            if ( Overflow <= TargetOverflow )
            {
                High = Scale;
                Low = Scale - 0.01;
                break;
            }
        }
        if ( High > 1.0 )
        {
            for ( int Iter = 0; Iter < 12; ++Iter )
            {
                double Middle = 0.5 * (Low + High);
                if ( ApplyScale(Middle) <= TargetOverflow )
                    High = Middle;
                else
                    Low = Middle;
            }
            ApplyScale(High);
        }
        else
            ApplyScale(BestScale);
    }

    void AddDensityGradient()
    {
        spectralSolver_->Solve(density_, fieldX_, fieldY_);
        for ( int Id = 0; Id < static_cast<int>(points_.size()); ++Id )
        {
            Pa_Point & Point = points_[Id];
            if ( !Point.movable )
                continue;
            double GradX = InterpolateField(fieldX_, Point.x, Point.y);
            double GradY = InterpolateField(fieldY_, Point.x, Point.y);
            densityGradientX_[Id] = Point.width * GradX;
            densityGradientY_[Id] = Point.width * GradY;
        }
    }

    void Move( double Progress, double DensityPenalty )
    {
        double Scale = std::min(binSizeX_, binSizeY_);
        size_t PointOffset = points_.size();
        size_t OptimizerSize = points_.size() + fillers_.size();
        if ( optimizerGradientX_.size() != OptimizerSize )
        {
            optimizerGradientX_.resize(OptimizerSize, 0.0);
            optimizerGradientY_.resize(OptimizerSize, 0.0);
            optimizerBaseX_.resize(OptimizerSize, 0.0);
            optimizerBaseY_.resize(OptimizerSize, 0.0);
            optimizerPreviousX_.resize(OptimizerSize, 0.0);
            optimizerPreviousY_.resize(OptimizerSize, 0.0);
            optimizerPreviousGradientX_.resize(OptimizerSize, 0.0);
            optimizerPreviousGradientY_.resize(OptimizerSize, 0.0);
            for ( int Id = 0; Id < static_cast<int>(points_.size()); ++Id )
            {
                optimizerBaseX_[Id] = points_[Id].x;
                optimizerBaseY_[Id] = points_[Id].y;
            }
            for ( size_t i = 0; i < fillers_.size(); ++i )
            {
                optimizerBaseX_[PointOffset + i] = fillers_[i].x;
                optimizerBaseY_[PointOffset + i] = fillers_[i].y;
            }
        }
        double SumSquaredGradient = 0.0;
        int GradientCount = 0;
        for ( int Id = 0; Id < static_cast<int>(points_.size()); ++Id )
        {
            const Pa_Point & Point = points_[Id];
            if ( !Point.movable )
                continue;
            double Precondition = std::max(1.0,
                wirePrecondition_[Id] + DensityPenalty * Point.width);
            double GradX = gradientX_[Id] / Precondition;
            double GradY = gradientY_[Id] / Precondition;
            optimizerGradientX_[Id] = GradX;
            optimizerGradientY_[Id] = GradY;
            SumSquaredGradient += GradX * GradX + GradY * GradY;
            GradientCount += 2;
        }
        for ( size_t i = 0; i < fillers_.size(); ++i )
        {
            optimizerGradientX_[PointOffset + i] =
                InterpolateField(fieldX_, fillers_[i].x, fillers_[i].y);
            optimizerGradientY_[PointOffset + i] =
                InterpolateField(fieldY_, fillers_[i].x, fillers_[i].y);
        }
        double GradientRms = std::sqrt(SumSquaredGradient /
            std::max(1, GradientCount));
        double NormalizedStep = pars_.step * Scale * (1.0 - 0.8 * Progress)
                              / std::max(1.0e-6, GradientRms);
        if ( !optimizerHasPrevious_ )
            optimizerStep_ = NormalizedStep;
        else
        {
            double PositionDifference = 0.0;
            double GradientDifference = 0.0;
            for ( int Id = 0; Id < static_cast<int>(points_.size()); ++Id )
            {
                if ( !points_[Id].movable )
                    continue;
                double Dx = points_[Id].x - optimizerPreviousX_[Id];
                double Dy = points_[Id].y - optimizerPreviousY_[Id];
                double Dgx = optimizerGradientX_[Id] - optimizerPreviousGradientX_[Id];
                double Dgy = optimizerGradientY_[Id] - optimizerPreviousGradientY_[Id];
                PositionDifference += Dx * Dx + Dy * Dy;
                GradientDifference += Dgx * Dgx + Dgy * Dgy;
            }
            double LipschitzStep = std::sqrt(PositionDifference /
                std::max(1.0e-24, GradientDifference));
            double Low = 0.5 * optimizerStep_;
            double High = 1.5 * optimizerStep_;
            optimizerStep_ = Clamp(LipschitzStep, Low, High);
            optimizerStep_ = std::min(optimizerStep_, 2.0 * NormalizedStep);
        }
        double NewNesterovT = 0.5 * (1.0 + std::sqrt(1.0 + 4.0 * optimizerT_ * optimizerT_));
        double Momentum = std::min(pars_.momentum, (optimizerT_ - 1.0) / NewNesterovT);
        double MaxDisplacement = 0.5 * Scale;
        for ( int Id = 0; Id < static_cast<int>(points_.size()); ++Id )
        {
            Pa_Point & Point = points_[Id];
            if ( !Point.movable )
                continue;
            optimizerPreviousX_[Id] = Point.x;
            optimizerPreviousY_[Id] = Point.y;
            optimizerPreviousGradientX_[Id] = optimizerGradientX_[Id];
            optimizerPreviousGradientY_[Id] = optimizerGradientY_[Id];
            double NewX = Point.x - optimizerStep_ * optimizerGradientX_[Id];
            double NewY = Point.y - optimizerStep_ * optimizerGradientY_[Id];
            NewX = Clamp(NewX, optimizerBaseX_[Id] - MaxDisplacement,
                        optimizerBaseX_[Id] + MaxDisplacement);
            NewY = Clamp(NewY, optimizerBaseY_[Id] - MaxDisplacement,
                        optimizerBaseY_[Id] + MaxDisplacement);
            double ExtrapolatedX = NewX + Momentum * (NewX - optimizerBaseX_[Id]);
            double ExtrapolatedY = NewY + Momentum * (NewY - optimizerBaseY_[Id]);
            optimizerBaseX_[Id] = Clamp(NewX, Point.densityHalfX,
                                        width_ - Point.densityHalfX);
            optimizerBaseY_[Id] = Clamp(NewY, Point.densityHalfY,
                                        height_ - Point.densityHalfY);
            Point.x = Clamp(ExtrapolatedX, Point.densityHalfX,
                            width_ - Point.densityHalfX);
            Point.y = Clamp(ExtrapolatedY, Point.densityHalfY,
                            height_ - Point.densityHalfY);
        }
        for ( size_t i = 0; i < fillers_.size(); ++i )
        {
            size_t Index = PointOffset + i;
            Pa_Point & Filler = fillers_[i];
            optimizerPreviousX_[Index] = Filler.x;
            optimizerPreviousY_[Index] = Filler.y;
            optimizerPreviousGradientX_[Index] = optimizerGradientX_[Index];
            optimizerPreviousGradientY_[Index] = optimizerGradientY_[Index];
            double NewX = Filler.x - optimizerStep_ * optimizerGradientX_[Index];
            double NewY = Filler.y - optimizerStep_ * optimizerGradientY_[Index];
            NewX = Clamp(NewX, optimizerBaseX_[Index] - MaxDisplacement,
                        optimizerBaseX_[Index] + MaxDisplacement);
            NewY = Clamp(NewY, optimizerBaseY_[Index] - MaxDisplacement,
                        optimizerBaseY_[Index] + MaxDisplacement);
            double ExtrapolatedX = NewX + Momentum * (NewX - optimizerBaseX_[Index]);
            double ExtrapolatedY = NewY + Momentum * (NewY - optimizerBaseY_[Index]);
            optimizerBaseX_[Index] = Clamp(NewX, Filler.densityHalfX,
                                           width_ - Filler.densityHalfX);
            optimizerBaseY_[Index] = Clamp(NewY, Filler.densityHalfY,
                                           height_ - Filler.densityHalfY);
            Filler.x = Clamp(ExtrapolatedX, Filler.densityHalfX,
                             width_ - Filler.densityHalfX);
            Filler.y = Clamp(ExtrapolatedY, Filler.densityHalfY,
                             height_ - Filler.densityHalfY);
        }
        optimizerT_ = NewNesterovT;
        optimizerHasPrevious_ = true;
    }

    Abc_Ntk_t * pNtk_;
    Pa_Parameters pars_;
    std::vector<Pa_Point> points_;
    std::vector<Pa_Point> fillers_;
    std::vector<Pa_Net> nets_;
    std::vector<std::vector<int>> incidentNets_;
    std::vector<double> wirePrecondition_;
    std::vector<double> wirePosX_, wireNegX_, wirePosY_, wireNegY_;
    std::vector<double> rawDensity_;
    std::vector<double> density_;
    std::vector<double> fieldX_;
    std::vector<double> fieldY_;
    std::unique_ptr<Pa_SpectralSolver> spectralSolver_;
    std::vector<double> gradientX_;
    std::vector<double> gradientY_;
    std::vector<double> densityGradientX_;
    std::vector<double> densityGradientY_;
    std::vector<double> optimizerGradientX_;
    std::vector<double> optimizerGradientY_;
    std::vector<double> optimizerBaseX_;
    std::vector<double> optimizerBaseY_;
    std::vector<double> optimizerPreviousX_;
    std::vector<double> optimizerPreviousY_;
    std::vector<double> optimizerPreviousGradientX_;
    std::vector<double> optimizerPreviousGradientY_;
    std::unordered_map<Abc_Obj_t *, Pa_Point> objectPoints_;
    std::unordered_map<Abc_Obj_t *, Pa_Point> stagedRemoved_;
    std::unordered_map<Abc_Obj_t *, Pa_Point> stagedRefreshed_;
    std::unordered_set<Abc_Obj_t *> stagedWritten_;
    bool editing_ = false;
    bool passActive_ = false;
    bool inheritedClusters_ = false;
    bool auditCurrentEdit_ = true;
    double passHpwlScale_ = 1.0;
    double overflowArea_ = 0.0;
    bool optimizerHasPrevious_ = false;
    double optimizerStep_ = 0.0;
    double optimizerT_ = 1.0;
    int nodeCount_ = 0;
    uint64_t fingerprint_ = 0;
    int bins_ = 0;
    double width_ = 0.0;
    double height_ = 0.0;
    double totalCellArea_ = 0.0;
    double binSizeX_ = 0.0;
    double binSizeY_ = 0.0;
    double targetAreaPerBin_ = 0.0;
    double finalHpwl_ = 0.0;
    double finalOverflow_ = 0.0;
};

struct Pa_UnmapCapture
{
    Abc_Ntk_t * source = nullptr;
    double width = 0.0;
    double height = 0.0;
    std::unordered_map<Abc_Obj_t *, Pa_MappedSeed> cells;
    std::unordered_map<Abc_Obj_t *, Pa_MappedSeed> aigNodes;
};

// The placement of the current frame and the cell centers captured by pa_strash.
struct Pa_PlaceState
{
    std::unique_ptr<Pa_Placement> placement;
    std::unique_ptr<Pa_UnmapCapture> capture;
};
void * Pa_PlaceStateAlloc() { return new Pa_PlaceState; }
void Pa_PlaceStateFree( void * p ) { delete static_cast<Pa_PlaceState *>(p); }
////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the placement state of the current frame.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Pa_PlaceState & PlaceState()
{
    return *static_cast<Pa_PlaceState *>(Pa_FrameState(PA_STATE_PLACE, Pa_PlaceStateAlloc, Pa_PlaceStateFree));
}

} // namespace

/**Function*************************************************************

  Synopsis    [Places the network; replaces the placement of the frame.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManPlace( Abc_Ntk_t * pNtk, double Step )
{
    if ( pNtk == nullptr || Abc_NtkNodeNum(pNtk) == 0 || (!Abc_NtkIsStrash(pNtk) && !Abc_NtkHasMapping(pNtk)) )
        return 0;
    Pa_Parameters Pars;
    Pars.step = Step;
    PlaceState().placement.reset(new Pa_Placement(pNtk, Pars));
    PlaceState().placement->Run();
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the placement belongs to the network.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManHasPlacement( Abc_Ntk_t * pNtk )
{
    Pa_Placement * p = PlaceState().placement.get();
    return p && p->Matches(pNtk);
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the placement was inherited through pa_strash.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManHasInheritedPlacement( Abc_Ntk_t * pNtk )
{
    Pa_Placement * p = PlaceState().placement.get();
    return p && p->HasInheritedClusters(pNtk);
}

/**Function*************************************************************

  Synopsis    [Captures the cell centers of a placed mapped network.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManBeginMappedUnmap( Abc_Ntk_t * pNtk )
{
    PlaceState().capture.reset();
    if ( !pNtk || !Abc_NtkHasMapping(pNtk)
      || !PlaceState().placement || !PlaceState().placement->Matches(pNtk) )
        return 0;
    std::unique_ptr<Pa_UnmapCapture> Capture(new Pa_UnmapCapture);
    Capture->source = pNtk;
    if ( !PlaceState().placement->ReadCanvas(pNtk, &Capture->width, &Capture->height,
                                  nullptr, nullptr, nullptr) )
        return 0;
    Abc_Obj_t * pCell;
    int i;
    Abc_NtkForEachNode( pNtk, pCell, i )
    {
        Pa_MappedSeed Seed;
        if ( !PlaceState().placement->ReadObjectPosition(pNtk, pCell, &Seed.x, &Seed.y) )
            return 0;
        Capture->cells.emplace(pCell, Seed);
    }
    PlaceState().capture = std::move(Capture);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Records the mapped cell of the AIG nodes created for it.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pa_ManCaptureUnmappedCell( Abc_Obj_t * pCell )
{
    if ( !PlaceState().capture || !pCell || pCell->pNtk != PlaceState().capture->source )
        return;
    auto Cell = PlaceState().capture->cells.find(pCell);
    if ( Cell == PlaceState().capture->cells.end() || !pCell->pData )
        return;
    std::vector<Hop_Obj_t *> Stack;
    std::unordered_set<Hop_Obj_t *> Visited;
    Stack.push_back(Hop_Regular(static_cast<Hop_Obj_t *>(pCell->pData)));
    while ( !Stack.empty() )
    {
        Hop_Obj_t * pHop = Stack.back();
        Stack.pop_back();
        if ( !Hop_ObjIsNode(pHop) || !Visited.insert(pHop).second )
            continue;
        if ( pHop->pData )
        {
            Abc_Obj_t * pAig = Abc_ObjRegular(static_cast<Abc_Obj_t *>(pHop->pData));
            if ( Abc_ObjIsNode(pAig) )
                // A shared AIG node has one position. The last mapped cell
                // visiting it owns its center.
                PlaceState().capture->aigNodes[pAig] = Cell->second;
        }
        Stack.push_back(Hop_ObjFanin0(pHop));
        Stack.push_back(Hop_ObjFanin1(pHop));
    }
}

/**Function*************************************************************

  Synopsis    [Places the new AIG at the captured cell centers.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManFinishMappedUnmap( Abc_Ntk_t * pAig )
{
    if ( !PlaceState().capture || !pAig || !Abc_NtkIsStrash(pAig) )
    {
        PlaceState().capture.reset();
        return 0;
    }
    Pa_Parameters Pars;
    std::unique_ptr<Pa_Placement> NewPlacement(new Pa_Placement(pAig, Pars));
    bool Ok = NewPlacement->ImportMappedCoordinates(
        PlaceState().capture->aigNodes, PlaceState().capture->width, PlaceState().capture->height);
    PlaceState().capture.reset();
    if ( !Ok )
        return 0;
    PlaceState().placement = std::move(NewPlacement);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Drops the captured cell centers.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pa_ManAbortMappedUnmap()
{
    PlaceState().capture.reset();
}

/**Function*************************************************************

  Synopsis    [Begins an optimization pass on the placement.]

  Description [The placement belongs to one network and uses object IDs for
               lookup. A pass validates the structural fingerprint once;
               accepted edits are bracketed by Pa_ManBeginEdit and a
               Finish*Edit call and give every new node a position.
               Pa_ManEndPass audits the accumulated HPWL.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManBeginPass( Abc_Ntk_t * pNtk )
{
    Pa_Placement * p = PlaceState().placement.get();
    return p && p->BeginPass(pNtk);
}

/**Function*************************************************************

  Synopsis    [Ends an optimization pass on the placement.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManEndPass( Abc_Ntk_t * pNtk )
{
    Pa_Placement * p = PlaceState().placement.get();
    return p && p->EndPass(pNtk);
}

/**Function*************************************************************

  Synopsis    [Returns 1 during a pass on the network.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManIsPassActive( Abc_Ntk_t * pNtk )
{
    Pa_Placement * p = PlaceState().placement.get();
    return p && p->IsPassActive(pNtk);
}

/**Function*************************************************************

  Synopsis    [Begins an edit of the placement.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManBeginEdit( Abc_Ntk_t * pNtk )
{
    Pa_Placement * p = PlaceState().placement.get();
    return p && p->BeginEdit(pNtk);
}

/**Function*************************************************************

  Synopsis    [Reads the position of an object.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManReadObjectPosition( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj, double * pX, double * pY )
{
    Pa_Placement * p = PlaceState().placement.get();
    return p && p->ReadObjectPosition(pNtk, pObj, pX, pY);
}

/**Function*************************************************************

  Synopsis    [Reads the position, width and density footprint of an object.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManReadObjectGeometry( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj,
    double * pX, double * pY, double * pWidth, double * pDensityHalfX,
    double * pDensityHalfY, double * pDensityScale )
{
    Pa_Placement * p = PlaceState().placement.get();
    return p && p->ReadObjectGeometry(pNtk, pObj, pX, pY,
        pWidth, pDensityHalfX, pDensityHalfY, pDensityScale);
}

/**Function*************************************************************

  Synopsis    [Stages the removal of an object in the current edit.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManStageObjectRemoval( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj )
{
    Pa_Placement * p = PlaceState().placement.get();
    return p && p->StageObjectRemoval(pNtk, pObj);
}

/**Function*************************************************************

  Synopsis    [Stages the refresh of an object in the current edit.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManStageObjectRefresh( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj )
{
    Pa_Placement * p = PlaceState().placement.get();
    return p && p->StageObjectRefresh(pNtk, pObj);
}

/**Function*************************************************************

  Synopsis    [Writes the position of a node in the current edit.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManWriteObjectPosition( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj, double X, double Y )
{
    Pa_Placement * p = PlaceState().placement.get();
    return p && p->WriteObjectPosition(pNtk, pObj, X, Y);
}

/**Function*************************************************************

  Synopsis    [Finishes an edit with a known HPWL reduction.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManFinishLocalEdit( Abc_Ntk_t * pNtk, double HpwlReduction )
{
    Pa_Placement * p = PlaceState().placement.get();
    return p && p->FinishLocalEdit(pNtk, HpwlReduction);
}

/**Function*************************************************************

  Synopsis    [Finishes an edit without the HPWL audit.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManFinishGlobalEdit( Abc_Ntk_t * pNtk )
{
    Pa_Placement * p = PlaceState().placement.get();
    return p && p->FinishGlobalEdit(pNtk);
}

/**Function*************************************************************

  Synopsis    [Finishes an edit and rebuilds the placement of the network.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManFinishEdit( Abc_Ntk_t * pNtk )
{
    Pa_Placement * p = PlaceState().placement.get();
    return p && p->FinishEdit(pNtk);
}

/**Function*************************************************************

  Synopsis    [Reads the canvas and the density grid.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManReadCanvas( Abc_Ntk_t * pNtk, double * pWidth, double * pHeight,
                      int * pBins, double * pBinSizeX, double * pBinSizeY )
{
    Pa_Placement * p = PlaceState().placement.get();
    return p && p->ReadCanvas(pNtk, pWidth, pHeight, pBins, pBinSizeX, pBinSizeY);
}

/**Function*************************************************************

  Synopsis    [Reads the cell area and the target area of a density bin.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManReadDensityBin( Abc_Ntk_t * pNtk, int BinX, int BinY,
    double * pCellArea, double * pTargetArea )
{
    Pa_Placement * p = PlaceState().placement.get();
    return p && p->ReadDensityBin(pNtk, BinX, BinY,
        pCellArea, pTargetArea);
}

/**Function*************************************************************

  Synopsis    [Reads the HPWL, overflow, HPWL scale and cell area.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManReadMetrics( Abc_Ntk_t * pNtk, double * pHpwl,
    double * pOverflow, double * pHpwlScale, double * pCellArea )
{
    Pa_Placement * p = PlaceState().placement.get();
    return p && p->ReadMetrics(pNtk, pHpwl,
        pOverflow, pHpwlScale, pCellArea);
}

/**Function*************************************************************

  Synopsis    [Drops the placement of the frame.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pa_ManClearPlacement()
{
    PlaceState().capture.reset();
    PlaceState().placement.reset();
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
