#include <stddef.h>   // size_t
#include <stdint.h>   // uint8_t, uint64_t
#include <stdlib.h>   // malloc, free


#define R_OK                            0
#define R_DST_OVERFLOW                  1
#define R_SRC_OVERFLOW                  2
#define R_MEM_RANOUT                    3

#define RET_WHEN_ERR(err_code)          { int ec = (err_code); if (ec)  return ec; }
#define RET_ERR_IF(err_code,condition)  { if (condition) return err_code; }

#define MIN_COMPRESSED_BLOCK_SIZE       13
#define MAX_COMPRESSED_BLOCK_SIZE       4194304

#define ML_MIN                  4
#define ML_MAX                  65535
#define ML_SKIP_THRESH          36
#define OF_MIN                  1
#define OF_MAX                  65535
#define N_HASH                  6543
#define N_HASH1_ROW             16
#define N_HASH2_ROW             16
#define N_HASH3_ROW             4
#define COST_LIT                1

static size_t LZ4_cost_match (/*size_t ll,*/ uint16_t ml) {
    size_t cost = 3;
    // if (ll >= 15) {
    //     ll -= 15;
    //     cost += 1;
    // }
    // for (; ll>=255; ll-=255) cost ++;
    ml -= ML_MIN;
    if (ml >= 15) {
        ml -= 15;
        cost += 1;
    }
    for (; ml>=255; ml-=255) cost ++;
    return cost;
}


static int LZ4_write (uint8_t **pp_dst, uint8_t *p_dst_limit, uint8_t byte) {
    RET_ERR_IF(R_DST_OVERFLOW, (*pp_dst >= p_dst_limit));
    *((*pp_dst)++) = byte;
    return R_OK;
}


static int LZ4_write_vlc (uint8_t **pp_dst, uint8_t *p_dst_limit, uint64_t value) {
    for (;;) {
        if (value < 255) {
            RET_WHEN_ERR(LZ4_write(pp_dst, p_dst_limit, value));
            break;
        } else {
            RET_WHEN_ERR(LZ4_write(pp_dst, p_dst_limit, 255));
            value -= 255;
        }
    }
    return R_OK;
}


static int LZ4_copy (uint8_t *p_src, uint8_t *p_src_end, uint8_t **pp_dst, uint8_t *p_dst_limit) {
    RET_ERR_IF(R_DST_OVERFLOW, (p_src_end - p_src > p_dst_limit - *pp_dst));
    for (; p_src<p_src_end; p_src++) {
        *((*pp_dst)++) = *p_src;
    }
    return R_OK;
}


static int LZ4_compress_seqence (uint8_t *p_src_lit, uint8_t *p_src, uint64_t ml, uint64_t of, uint8_t **pp_dst, uint8_t *p_dst_limit) {
    uint64_t ll = p_src - p_src_lit;
    uint8_t *p_token = *pp_dst;
    RET_WHEN_ERR(LZ4_write(pp_dst, p_dst_limit, 0));
    if (ll < 15) {
        (*p_token) = (ll << 4);
    } else {
        (*p_token) = (15 << 4);
        RET_WHEN_ERR(LZ4_write_vlc(pp_dst, p_dst_limit, ll-15));
    }
    RET_WHEN_ERR(LZ4_copy(p_src_lit, p_src, pp_dst, p_dst_limit));
    if (of) {      // when of==0, encode literal only
        RET_WHEN_ERR(LZ4_write(pp_dst, p_dst_limit, of&0xFF));
        RET_WHEN_ERR(LZ4_write(pp_dst, p_dst_limit, of>>8));
        ml -= ML_MIN;
        if (ml < 15) {
            (*p_token) |= ml;
        } else {
            (*p_token) |= 15;
            RET_WHEN_ERR(LZ4_write_vlc(pp_dst, p_dst_limit, ml-15));
        }
    }
    return R_OK;
}


typedef struct {
    uint16_t ml [MAX_COMPRESSED_BLOCK_SIZE];
    uint16_t of [MAX_COMPRESSED_BLOCK_SIZE];
    union {
        struct {
            const uint8_t* hash1_tab [N_HASH] [N_HASH1_ROW];
            const uint8_t* hash2_tab [N_HASH] [N_HASH2_ROW];
            const uint8_t* hash3_tab [N_HASH] [N_HASH3_ROW];
        };
        size_t cost [MAX_COMPRESSED_BLOCK_SIZE+1];
    };
} LZ4_compress_workspace_t;


static int LZ4_compress_block (uint8_t *p_src, uint8_t *p_src_end, uint8_t **pp_dst, uint8_t *p_dst_limit, LZ4_compress_workspace_t *wksp) {
    size_t src_len = p_src_end - p_src;
    size_t i, skip=0;
    int k;

    // memset(wksp->hash1_tab, 0, sizeof(wksp->hash1_tab));
    // memset(wksp->hash2_tab, 0, sizeof(wksp->hash2_tab));
    
    for (i=0; i+MIN_COMPRESSED_BLOCK_SIZE+1<src_len; i++) {
        const uint8_t *p = p_src + i;
        
        uint64_t byte012345 = 0x555555555555ULL ^ ((((uint64_t)p[0]) | ((uint64_t)p[1] << 8) | ((uint64_t)p[2] << 16) | ((uint64_t)p[3] << 24)) | ((uint64_t)p[4] << 32) | ((uint64_t)p[5] << 40));
        uint32_t hash1 = (byte012345 & 0x0000FFFFFFFFULL) % N_HASH;
        uint32_t hash2 = (byte012345 & 0x00FFFFFFFFFFULL) % N_HASH;
        uint32_t hash3 =  byte012345                      % N_HASH;
        
        wksp->ml[i] = 0;
        
        if (skip > 0) {
            skip --;
        } else {
            size_t len_max = src_len - (MIN_COMPRESSED_BLOCK_SIZE+1) - i;
            if (len_max > ML_MAX) {
                len_max = ML_MAX;
            }
            
            for (k=0; k<(N_HASH1_ROW+N_HASH2_ROW+N_HASH3_ROW); k++) {
                const uint8_t *p_match = (k < N_HASH1_ROW)             ? wksp->hash1_tab[hash1][k] : 
                                         (k < N_HASH1_ROW+N_HASH2_ROW) ? wksp->hash2_tab[hash2][k-N_HASH1_ROW] :
                                                                         wksp->hash3_tab[hash3][k-N_HASH1_ROW-N_HASH2_ROW] ;
                if (p_src <= p_match && p_match < p) {
                    size_t of = p - p_match;
                    if (OF_MIN <= of && of <= OF_MAX) {
                        size_t ml;
                        for (ml=0; ml<len_max && p_match[ml]==p[ml]; ml++);
                        if (ml >= ML_MIN && ml > wksp->ml[i]) {
                            wksp->ml[i] = ml;
                            wksp->of[i] = of;
                            if (ml >= ML_SKIP_THRESH) {
                                skip = ml - 1;
                            }
                        }
                    }
                }
            }
        }
        
        for (k=0; k<N_HASH1_ROW-1; k++) {
            wksp->hash1_tab[hash1][k] = wksp->hash1_tab[hash1][k+1];
        }
        wksp->hash1_tab[hash1][N_HASH1_ROW-1] = p;

        for (k=0; k<N_HASH2_ROW-1; k++) {
            wksp->hash2_tab[hash2][k] = wksp->hash2_tab[hash2][k+1];
        }
        wksp->hash2_tab[hash2][N_HASH2_ROW-1] = p;

        for (k=0; k<N_HASH3_ROW-1; k++) {
            wksp->hash3_tab[hash3][k] = wksp->hash3_tab[hash3][k+1];
        }
        wksp->hash3_tab[hash3][N_HASH3_ROW-1] = p;
    }
    
    for (; i<src_len; i++) {
        wksp->ml[i] = 0;
    }

    wksp->cost[src_len] = 0;
    
    for (i=src_len; i>0;) {
        i --;
        wksp->cost[i] = wksp->cost[i+1] + COST_LIT;
        {
            uint16_t ml = wksp->ml[i];
            if (ml > 0) {
                size_t match_cost = wksp->cost[i+ml] + LZ4_cost_match(ml);
                if (wksp->cost[i] > match_cost) {
                    wksp->cost[i] = match_cost;
                } else {
                    wksp->ml[i] = 0;
                    wksp->of[i] = 0;
                }
            }
        }
    }
    
    {
        uint8_t *p_last_start = p_src;
        for (i=0; i<src_len; i++) {
            if (wksp->ml[i] > 0) {
                RET_WHEN_ERR(LZ4_compress_seqence(p_last_start, &p_src[i], wksp->ml[i], wksp->of[i], pp_dst, p_dst_limit));
                i += wksp->ml[i];
                p_last_start = p_src + i;
                i --;
            }
        }
        RET_WHEN_ERR(LZ4_compress_seqence(p_last_start, &p_src[src_len], 0, 0, pp_dst, p_dst_limit));
    }

    return R_OK;
}


static int LZ4_compress_or_copy_block_with_csize (uint8_t *p_src, uint8_t *p_src_end, uint8_t **pp_dst, uint8_t *p_dst_limit, LZ4_compress_workspace_t *wksp) {
    uint64_t csize = p_src_end - p_src;
    uint8_t *p_dst_base = (*pp_dst) + 4;
    RET_ERR_IF(R_DST_OVERFLOW, (p_dst_limit-(*pp_dst) < 4));
    (*pp_dst) += 4;
    if (csize <= MIN_COMPRESSED_BLOCK_SIZE) {
        RET_WHEN_ERR(LZ4_copy(p_src, p_src_end, pp_dst, p_dst_limit));
        csize |= 0x80000000U;
    } else {
        RET_WHEN_ERR(LZ4_compress_block(p_src, p_src_end, pp_dst, p_dst_limit, wksp));
        if (csize > (*pp_dst) - p_dst_base) {
            csize = (*pp_dst) - p_dst_base;
        } else {
            *pp_dst = p_dst_base;
            RET_WHEN_ERR(LZ4_copy(p_src, p_src_end, pp_dst, p_dst_limit));
            csize |= 0x80000000U;
        }
    }
    p_dst_base[-4] = 0xFF & (csize      );
    p_dst_base[-3] = 0xFF & (csize >>  8);
    p_dst_base[-2] = 0xFF & (csize >> 16);
    p_dst_base[-1] = 0xFF & (csize >> 24);
    return R_OK;
}


int lz4C (uint8_t *p_src, size_t src_len, uint8_t *p_dst, size_t *p_dst_len) {
    uint8_t  *p_src_limit = p_src + src_len;
    uint8_t  *p_dst_tmp   = p_dst;
    uint8_t **pp_dst      = &p_dst_tmp;
    uint8_t  *p_dst_limit = p_dst + (*p_dst_len);
    LZ4_compress_workspace_t *wksp = (LZ4_compress_workspace_t*)malloc(sizeof(LZ4_compress_workspace_t));
    RET_ERR_IF(R_MEM_RANOUT, (wksp==NULL));
    RET_ERR_IF(R_SRC_OVERFLOW, p_src > p_src_limit);
    RET_ERR_IF(R_DST_OVERFLOW, p_dst > p_dst_limit);
    RET_WHEN_ERR(LZ4_write(pp_dst, p_dst_limit, 0x04));
    RET_WHEN_ERR(LZ4_write(pp_dst, p_dst_limit, 0x22));
    RET_WHEN_ERR(LZ4_write(pp_dst, p_dst_limit, 0x4D));
    RET_WHEN_ERR(LZ4_write(pp_dst, p_dst_limit, 0x18));
    RET_WHEN_ERR(LZ4_write(pp_dst, p_dst_limit, 0x60));
    RET_WHEN_ERR(LZ4_write(pp_dst, p_dst_limit, 0x70)); // block size, 0x40=64kB, 0x50=256kB, 0x60=1MB, 0x70=4MB
    RET_WHEN_ERR(LZ4_write(pp_dst, p_dst_limit, 0x73));
    while (p_src < p_src_limit) {
        uint8_t *p_src_end = p_src_limit;      // block end
        if (p_src_end - p_src > MAX_COMPRESSED_BLOCK_SIZE) {
            p_src_end = p_src + MAX_COMPRESSED_BLOCK_SIZE;
        }
        RET_WHEN_ERR(LZ4_compress_or_copy_block_with_csize(p_src, p_src_end, pp_dst, p_dst_limit, wksp));
        p_src = p_src_end;
    }
    free(wksp);
    RET_WHEN_ERR(LZ4_write(pp_dst, p_dst_limit, 0x00));
    RET_WHEN_ERR(LZ4_write(pp_dst, p_dst_limit, 0x00));
    RET_WHEN_ERR(LZ4_write(pp_dst, p_dst_limit, 0x00));
    RET_WHEN_ERR(LZ4_write(pp_dst, p_dst_limit, 0x00));
    *p_dst_len = (*pp_dst) - p_dst;
    return R_OK;
}

