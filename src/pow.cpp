// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2018 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <pow.h>

#include <arith_uint256.h>
#include <chain.h>
#include <primitives/block.h>
#include <uint256.h>
#include <util.h>

#include <consensus/consensus.h>

unsigned int GetNextWorkRequired(const CBlockIndex* pindexLast, const CBlockHeader *pblock, const Consensus::Params& params)
{
    assert(pindexLast != nullptr);

    if (pindexLast->nHeight+1 == params.BCDHeight)
        return UintToArith256(params.powLimit).GetCompact();;

    if (pindexLast->nHeight+1 == params.BCDHeight+1)
        return UintToArith256(params.BCDBeginPowLimit).GetCompact();

    if (pindexLast->nHeight+1 < params.ZawyLWMAHeight) {
        return BCDGetNextWorkRequired(pindexLast, pblock, params);
    }

    return LwmaGetNextWorkRequired(pindexLast, pblock, params);
}

unsigned int BCDGetNextWorkRequired(const CBlockIndex* pindexLast, const CBlockHeader *pblock, const Consensus::Params& params)
{
    int height, interval;
    if (pindexLast->nHeight+1 > params.BCDHeight) {
        height = pindexLast->nHeight+1 - params.BCDHeight;
        interval = 72;
    }else{
        height = pindexLast->nHeight+1;
        interval = params.DifficultyAdjustmentInterval();
    }

    // Only change once per difficulty adjustment interval
    if (height % interval != 0)
    {
        if (params.fPowAllowMinDifficultyBlocks)
        {
            unsigned int nProofOfWorkLimit = UintToArith256(params.powLimit).GetCompact();
            // Special difficulty rule for testnet:
            // If the new block's timestamp is more than 2* 10 minutes
            // then allow mining of a min-difficulty block.
            if (pblock->GetBlockTime() > pindexLast->GetBlockTime() + params.nPowTargetSpacing*2)
                return nProofOfWorkLimit;
            else
            {
                // Return the last non-special-min-difficulty-rules-block
                const CBlockIndex* pindex = pindexLast;
                while (pindex->pprev && pindex->nHeight % params.DifficultyAdjustmentInterval() != 0 && pindex->nBits == nProofOfWorkLimit)
                    pindex = pindex->pprev;
                return pindex->nBits;
            }
        }
        return pindexLast->nBits;
    }

    // Go back by what we want to be 14 days worth of blocks
    int nHeightFirst = pindexLast->nHeight - (interval-1);
    assert(nHeightFirst >= 0);
    const CBlockIndex* pindexFirst = pindexLast->GetAncestor(nHeightFirst);
    assert(pindexFirst);

    return CalculateNextWorkRequired(pindexLast, pindexFirst->GetBlockTime(), params);
}

unsigned int CalculateNextWorkRequired(const CBlockIndex* pindexLast, int64_t nFirstBlockTime, const Consensus::Params& params)
{
    if (params.fPowNoRetargeting)
        return pindexLast->nBits;

    int limit, powTargetTimespan;
    if (pindexLast->nHeight+1 > params.BCDHeight) {
        powTargetTimespan = 72 * params.nPowTargetSpacing;
        limit = 2;
    }else{
        powTargetTimespan = params.nPowTargetTimespan;
        limit = 4;
    }
    // Limit adjustment step
    int64_t nActualTimespan = pindexLast->GetBlockTime() - nFirstBlockTime;
    int64_t realActualTimespan = nActualTimespan;
    if (nActualTimespan < powTargetTimespan/limit)
        nActualTimespan = powTargetTimespan/limit;
    if (nActualTimespan > powTargetTimespan*limit)
        nActualTimespan = powTargetTimespan*limit;

    // Retarget
    const arith_uint256 bnPowLimit = UintToArith256(params.powLimit);
    arith_uint256 bnNew;
    arith_uint256 bnOld;
    bnNew.SetCompact(pindexLast->nBits);
    bnOld = bnNew;
    bnNew *= nActualTimespan;
    bnNew /= powTargetTimespan;

    if (bnNew > bnPowLimit)
        bnNew = bnPowLimit;

    LogPrintf("BCDGetNextWorkRequired RETARGET at nHeight = %d\n", pindexLast->nHeight+1);
    LogPrintf("params.nPowTargetTimespan = %d    nActualTimespan = %d    realActualTimespan = %d\n", powTargetTimespan, nActualTimespan, realActualTimespan);
    LogPrintf("Before: %08x  %s\n", pindexLast->nBits, bnOld.ToString());
    LogPrintf("After:  %08x  %s\n", bnNew.GetCompact(), bnNew.ToString());
    return bnNew.GetCompact();
}

unsigned int LwmaGetNextWorkRequired(const CBlockIndex* pindexLast, const CBlockHeader *pblock, const Consensus::Params& params) {
    // Special difficulty rule for testnet:
    // If the new block's timestamp is more than 2 * 10 minutes
    // then allow mining of a min-difficulty block.
    if (params.fPowAllowMinDifficultyBlocks &&
        pblock->GetBlockTime() > pindexLast->GetBlockTime() + params.nPowTargetSpacing * 2) {
        return UintToArith256(params.BCDBeginPowLimit).GetCompact();
    }
    return LwmaCalculateNextWorkRequired(pindexLast, params);
}

unsigned int LwmaCalculateNextWorkRequired(const CBlockIndex* pindexLast, const Consensus::Params& params)
{
    if (params.fPowNoRetargeting) {
        return pindexLast->nBits;
    }

    const int height = pindexLast->nHeight;
    const int64_t T  = params.nPowTargetSpacing;
    const int64_t N = params.nZawyLwmaAveragingWindow;
    const int64_t k = N * (N + 1) / 2 * T;
    const int64_t dnorm = params.nZawyLwmaMinDenominator;
    const arith_uint256 powLimit = UintToArith256(params.BCDBeginPowLimit);

    if (height < N) {
        return powLimit.GetCompact();
    }

    arith_uint256 sumTarget, nextTarget;
    int64_t thisTimestamp, previousTimestamp;
    int t = 0, j = 0;

    const CBlockIndex* blockPreviousTimestamp = pindexLast->GetAncestor(height - N);
    previousTimestamp = blockPreviousTimestamp->GetBlockTime();

    // Loop through N most recent blocks.
    for (int i = height - N + 1; i <= height; i++) {
        const CBlockIndex* block = pindexLast->GetAncestor(i);
        thisTimestamp = (block->GetBlockTime() > previousTimestamp) ? block->GetBlockTime() : previousTimestamp + 1;
        int64_t solvetime = std::min(6 * T, thisTimestamp - previousTimestamp);
        previousTimestamp = thisTimestamp;

        j++;
        t += solvetime * j;  // Weighted solvetime sum.

        // Target sum divided by a factor, (k N).
        // The factor is a part of the final equation. However we divide sum_target here to avoid potential overflow.
        arith_uint256 target;
        target.SetCompact(block->nBits);
        sumTarget += target / (k * N);
    }
    // Keep t reasonable in case strange solvetimes occurred.
    // if (t < k / dnorm) {
    //     t = k / dnorm;
    // }

    nextTarget = t * sumTarget;
    if (nextTarget > powLimit) {
        nextTarget = powLimit;
    }

    LogPrintf("LWMAGetNextWorkRequired RETARGET at nHeight = %d\n", pindexLast->nHeight+1);
    LogPrintf("Next target:  %08x  %s\n", nextTarget.GetCompact(), nextTarget.ToString());

    return nextTarget.GetCompact();
}

bool CheckProofOfWork(uint256 hash, unsigned int nBits, const Consensus::Params& params)
{
    bool fNegative;
    bool fOverflow;
    arith_uint256 bnTarget;

    bnTarget.SetCompact(nBits, &fNegative, &fOverflow);

    // Check range
    if (fNegative || bnTarget == 0 || fOverflow || bnTarget > UintToArith256(params.powLimit))
        return false;

    // Check proof of work matches claimed amount
    if (UintToArith256(hash) > bnTarget)
        return false;

    return true;
}
