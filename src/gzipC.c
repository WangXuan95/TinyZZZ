#include <stddef.h>  // size_t
#include <stdint.h>  // uint8_t, uint32_t
#include <stdlib.h>  // malloc, free


#define R_OK                            0
#define R_DST_OVERFLOW                  1
#define R_SRC_OVERFLOW                  2
#define R_MEM_RANOUT                    3

#define RET_WHEN_ERR(err_code)          { int ec = (err_code); if (ec)  return ec; }
#define RET_ERR_IF(err_code,condition)  { if (condition) return err_code; }


#define N_LITERAL              256                               // literal      (symbol = 0-255  )
#define SYMBOL_END             N_LITERAL                         // end_of_block (symbol = 256    )
#define N_LZ77_ML              29                                // LZ77_len     (symbol = 257-285)
#define N_SYMBOL               ( (N_LITERAL) + 1 + (N_LZ77_ML) )
#define N_LZ77_OF              30

#define MIN_LZ77_ML            3
#define MAX_LZ77_ML            258
#define SKIP_LZ77_ML           64
#define MIN_LZ77_OF            1
#define MAX_LZ77_OF            32767

#define MAX_HUFFMAN_BITS_LEN   15

#define SYMBOL_TREE_MERGE_INC  20
#define OFFSET_TREE_MERGE_INC  7

#define MAX_BLOCK_LEN          32768

#define N_HASH                 16381
#define N_HASH1_ROW            4
#define N_HASH2_ROW            2
#define N_HASH3_ROW            2
#define N_HASH_ROW             (N_HASH1_ROW + N_HASH2_ROW + N_HASH3_ROW)

static const uint32_t static_symbol_huffman_bits [N_SYMBOL] = {0x00c, 0x08c, 0x04c, 0x0cc, 0x02c, 0x0ac, 0x06c, 0x0ec, 0x01c, 0x09c, 0x05c, 0x0dc, 0x03c, 0x0bc, 0x07c, 0x0fc, 0x002, 0x082, 0x042, 0x0c2, 0x022, 0x0a2, 0x062, 0x0e2, 0x012, 0x092, 0x052, 0x0d2, 0x032, 0x0b2, 0x072, 0x0f2, 0x00a, 0x08a, 0x04a, 0x0ca, 0x02a, 0x0aa, 0x06a, 0x0ea, 0x01a, 0x09a, 0x05a, 0x0da, 0x03a, 0x0ba, 0x07a, 0x0fa, 0x006, 0x086, 0x046, 0x0c6, 0x026, 0x0a6, 0x066, 0x0e6, 0x016, 0x096, 0x056, 0x0d6, 0x036, 0x0b6, 0x076, 0x0f6, 0x00e, 0x08e, 0x04e, 0x0ce, 0x02e, 0x0ae, 0x06e, 0x0ee, 0x01e, 0x09e, 0x05e, 0x0de, 0x03e, 0x0be, 0x07e, 0x0fe, 0x001, 0x081, 0x041, 0x0c1, 0x021, 0x0a1, 0x061, 0x0e1, 0x011, 0x091, 0x051, 0x0d1, 0x031, 0x0b1, 0x071, 0x0f1, 0x009, 0x089, 0x049, 0x0c9, 0x029, 0x0a9, 0x069, 0x0e9, 0x019, 0x099, 0x059, 0x0d9, 0x039, 0x0b9, 0x079, 0x0f9, 0x005, 0x085, 0x045, 0x0c5, 0x025, 0x0a5, 0x065, 0x0e5, 0x015, 0x095, 0x055, 0x0d5, 0x035, 0x0b5, 0x075, 0x0f5, 0x00d, 0x08d, 0x04d, 0x0cd, 0x02d, 0x0ad, 0x06d, 0x0ed, 0x01d, 0x09d, 0x05d, 0x0dd, 0x03d, 0x0bd, 0x07d, 0x0fd, 0x013, 0x113, 0x093, 0x193, 0x053, 0x153, 0x0d3, 0x1d3, 0x033, 0x133, 0x0b3, 0x1b3, 0x073, 0x173, 0x0f3, 0x1f3, 0x00b, 0x10b, 0x08b, 0x18b, 0x04b, 0x14b, 0x0cb, 0x1cb, 0x02b, 0x12b, 0x0ab, 0x1ab, 0x06b, 0x16b, 0x0eb, 0x1eb, 0x01b, 0x11b, 0x09b, 0x19b, 0x05b, 0x15b, 0x0db, 0x1db, 0x03b, 0x13b, 0x0bb, 0x1bb, 0x07b, 0x17b, 0x0fb, 0x1fb, 0x007, 0x107, 0x087, 0x187, 0x047, 0x147, 0x0c7, 0x1c7, 0x027, 0x127, 0x0a7, 0x1a7, 0x067, 0x167, 0x0e7, 0x1e7, 0x017, 0x117, 0x097, 0x197, 0x057, 0x157, 0x0d7, 0x1d7, 0x037, 0x137, 0x0b7, 0x1b7, 0x077, 0x177, 0x0f7, 0x1f7, 0x00f, 0x10f, 0x08f, 0x18f, 0x04f, 0x14f, 0x0cf, 0x1cf, 0x02f, 0x12f, 0x0af, 0x1af, 0x06f, 0x16f, 0x0ef, 0x1ef, 0x01f, 0x11f, 0x09f, 0x19f, 0x05f, 0x15f, 0x0df, 0x1df, 0x03f, 0x13f, 0x0bf, 0x1bf, 0x07f, 0x17f, 0x0ff, 0x1ff, 0x000, 0x040, 0x020, 0x060, 0x010, 0x050, 0x030, 0x070, 0x008, 0x048, 0x028, 0x068, 0x018, 0x058, 0x038, 0x078, 0x004, 0x044, 0x024, 0x064, 0x014, 0x054, 0x034, 0x074, 0x003, 0x083, 0x043, 0x0c3, 0x023, 0x0a3};
static const uint32_t static_symbol_huffman_len  [N_SYMBOL] = {    8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     8,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     9,     7,     7,     7,     7,     7,     7,     7,     7,     7,     7,     7,     7,     7,     7,     7,     7,     7,     7,     7,     7,     7,     7,     7,     7,     8,     8,     8,     8,     8,     8};
//static const uint32_t static_dist_huffman_bits[N_LZ77_OF] = {0x00, 0x10, 0x08, 0x18, 0x04, 0x14, 0x0c, 0x1c, 0x02, 0x12, 0x0a, 0x1a, 0x06, 0x16, 0x0e, 0x1e, 0x01, 0x11, 0x09, 0x19, 0x05, 0x15, 0x0d, 0x1d, 0x03, 0x13, 0x0b, 0x1b, 0x07, 0x17};



struct StreamWriter_t {
    uint8_t *p_buf;
    uint8_t *p_limit;
    uint8_t  byte;
    uint8_t  mask;
};


static struct StreamWriter_t newStreamWriter (uint8_t *p_buf, uint32_t len) {
    struct StreamWriter_t bs = {p_buf, (p_buf+len), 0x00, 0x01};
    return bs;
}


static int appendBits (struct StreamWriter_t *p_bs, uint32_t bits, uint32_t cnt) {
    //assert(cnt <= 32);
    for (; cnt>0; cnt--) {
        if (bits & 1)
            p_bs->byte |= p_bs->mask;
        bits >>= 1;
        p_bs->mask <<= 1;
        if (p_bs->mask == 0x00) {
            RET_ERR_IF(R_DST_OVERFLOW, (p_bs->p_buf >= p_bs->p_limit));
            *(p_bs->p_buf) = p_bs->byte;
            p_bs->p_buf ++;
            p_bs->byte = 0x00;
            p_bs->mask = 0x01;
        }
    }
    return R_OK;
}


static int alignBitsToBytes (struct StreamWriter_t *p_bs) {
    if (p_bs->mask > 0x01) {
        RET_ERR_IF(R_DST_OVERFLOW, (p_bs->p_buf >= p_bs->p_limit));
        *(p_bs->p_buf) = p_bs->byte;
        p_bs->p_buf ++;
        p_bs->byte = 0x00;
        p_bs->mask = 0x01;
    }
    return R_OK;
}


static int writeValue (uint8_t **pp_dst, uint8_t *p_dst_limit, uint32_t value, uint8_t n_bytes) {
    RET_ERR_IF(R_DST_OVERFLOW, (n_bytes > p_dst_limit - *pp_dst));
    for (; n_bytes>0; n_bytes--) {
        *((*pp_dst)++) = value & 0xFF;
        value >>= 8;
    }
    return R_OK;
}


static uint32_t bitsReverse (uint32_t bits, uint32_t len) {
    uint32_t revbits = 0;
    //assert(len <= 32);
    for (; len>0; len--) {
        revbits <<= 1;
        revbits |= (bits & 1);
        bits >>= 1;
    }
    return revbits;
}


static uint32_t calcCrc32 (uint8_t *p_src, uint32_t src_len) {
    static const uint32_t TABLE_CRC32 [] = { 0x00000000, 0x1db71064, 0x3b6e20c8, 0x26d930ac, 0x76dc4190, 0x6b6b51f4, 0x4db26158, 0x5005713c, 0xedb88320, 0xf00f9344, 0xd6d6a3e8, 0xcb61b38c, 0x9b64c2b0, 0x86d3d2d4, 0xa00ae278, 0xbdbdf21c };
    uint32_t crc = 0xFFFFFFFF;
    uint8_t *p_end = p_src + src_len;
    for (; p_src<p_end; p_src++) {
        crc ^= *p_src;
        crc = TABLE_CRC32[crc & 0x0f] ^ (crc >> 4);
        crc = TABLE_CRC32[crc & 0x0f] ^ (crc >> 4);
    }
    return ~crc;
}



static void buildHuffmanLen (uint32_t num, uint32_t count [], uint32_t huffman_len [], uint32_t tree_merge_inc) {
    uint32_t i, group1_no, group2_no;
    
    uint32_t huffman_group [N_SYMBOL];
    
    //assert(0<=num && num<=N_SYMBOL);
    
    for (i=0; i<num; i++) {
        huffman_len  [i] = 0;
        huffman_group[i] = i + 1;                               // initial: all nodes are not in same sub-tree
    }
    
    for (;;) {
        uint32_t m2c = UINT32_MAX;                              // the minimum 2nd value
        uint32_t m2i = UINT32_MAX;                              // the minimum 2nd value's index
        uint32_t m1c = UINT32_MAX;                              // the minimum 1st value 
        uint32_t m1i = UINT32_MAX;                              // the minimum 1st value's index
        
        // find the minimum 2 values in count[] --------------------
        for (i=0; i<num; i++) {
            if (count[i] > 0) {                                 // skip the values that never appear (count=0)
                if        (count[i] < m1c) {
                    m2c = m1c;
                    m2i = m1i;
                    m1c = count[i];
                    m1i = i;
                } else if (count[i] < m2c) {
                    m2c = count[i];
                    m2i = i;
                }
            }
        }
        
        if (m2i == UINT32_MAX) {                                // if there's only one minimum value found, which means all nodes a merged in one sub-tree
            if (m1i != UINT32_MAX && huffman_len[m1i] == 0)     // a special case : there is only one symbol appears, we should assign a one-node huffman tree for it, set its huffman_len to 1
                huffman_len[m1i] = 1;
            break;
        }
        
        //assert (m1i != UINT32_MAX);
        
        // merge the two sub-trees to one sub-tree --------------------
        count[m1i] += tree_merge_inc;                           // NOTE : to make the merged sub-tree's counter be larger, Avoid trees that are too deep
        count[m1i] += count[m2i];                               // merge the 2nd sub-tree's count to the 1st sub-tree
        //count[m1i] *= 1.3;
        count[m2i] = 0;                                         // clear the 2nd sub-tree's count to zero, since it is merged to the 1st sub-tree
        group1_no = huffman_group[m1i];
        group2_no = huffman_group[m2i];
        
        for (i=0; i<num; i++) {
            if (huffman_group[i] == group1_no || huffman_group[i] == group2_no) {
                huffman_len[i] ++;                              // huffman code bits length (tree depth) +1
                huffman_group[i] = group1_no;                   // set the 2nd sub-tree's number to as same as the 1st sub-tree's
            }
        }
    }
}


static void buildHuffmanBits (uint32_t num, uint32_t huffman_len [], uint32_t huffman_bits []) {
    uint32_t bl_count  [1+MAX_HUFFMAN_BITS_LEN];
    uint32_t next_bits [1+MAX_HUFFMAN_BITS_LEN];
    
    uint32_t i;
    
    for (i=0; i<=MAX_HUFFMAN_BITS_LEN; i++) {
        bl_count [i] = 0;
        next_bits[i] = 0;
    }
    
    for (i=0; i<num; i++) {
        //assert(huffman_len[i] <= MAX_HUFFMAN_BITS_LEN);  // exceed the max huffman bits length (tree depth)
        bl_count[huffman_len[i]] ++;
    }
    
    for (i=2; i<=MAX_HUFFMAN_BITS_LEN; i++)
        next_bits[i] = (next_bits[i-1] + bl_count[i-1]) << 1;
    
    for (i=0; i<num; i++)  {
        uint32_t len = huffman_len[i];
        if (len > 0)
            huffman_bits[i] = bitsReverse(next_bits[len]++, len);
        else
            huffman_bits[i] = 0;
    }
}


static uint32_t getLZ77SymbolAndExtraBits (uint32_t ml, uint32_t of, uint32_t *p_ml_ebits, uint32_t *p_ml_elen, uint32_t *p_of_symbol, uint32_t *p_of_ebits, uint32_t *p_of_elen) {
    static const uint32_t TABLE_OF_EXTRA [N_LZ77_OF] = {0,0,0,0,1,1,2, 2, 3, 3, 4, 4, 5, 5,  6,  6,  7,  7,  8,  8,   9,   9,  10,  10,  11,  11,  12,   12,   13,   13};
    static const uint32_t TABLE_OF_START [N_LZ77_OF] = {1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577};
    
    static const uint32_t TABLE_ML_EXTRA [N_LZ77_ML] = {0,0,0,0,0,0,0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4,  4,  5,  5,  5,  5,  0};
    static const uint32_t TABLE_ML_START [N_LZ77_ML] = {3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258};
    
    uint32_t i;
    
    //assert(1 <= of && of <= MAX_LZ77_OF);
    //assert(MIN_LZ77_ML <= ml && ml <= MAX_LZ77_ML);
    
    for (i=N_LZ77_OF-1; ; i--)
        if (TABLE_OF_START[i] <= of)
            break;
    
    *p_of_symbol     = i;
    *p_of_ebits = of - TABLE_OF_START[i];
    *p_of_elen  = TABLE_OF_EXTRA[i];

    for (i=N_LZ77_ML-1; ; i--)
        if (TABLE_ML_START[i] <= ml)
            break;
    
    *p_ml_ebits = ml - TABLE_ML_START[i];
    *p_ml_elen  = TABLE_ML_EXTRA[i];
    
    return i + 257;         // return ml symbol (257-285)
}


typedef struct {
    uint16_t ml [MAX_BLOCK_LEN];
    uint16_t of [MAX_BLOCK_LEN];
    uint16_t ml_cand [MAX_BLOCK_LEN] [N_HASH_ROW];
    uint16_t of_cand [MAX_BLOCK_LEN] [N_HASH_ROW];
    size_t cost [MAX_BLOCK_LEN+1];
    const uint8_t* hash1_tab [N_HASH] [N_HASH1_ROW];
    const uint8_t* hash2_tab [N_HASH] [N_HASH2_ROW];
    const uint8_t* hash3_tab [N_HASH] [N_HASH3_ROW];
} searchLZ77_workspace_t;


typedef struct {
    uint32_t symbol_cnt [N_SYMBOL] , symbol_huffman_len [N_SYMBOL] , symbol_huffman_bits [N_SYMBOL];
    uint32_t of_cnt    [N_LZ77_OF] , of_huffman_len    [N_LZ77_OF] , of_huffman_bits    [N_LZ77_OF];
} EntropyCtx_t;


static size_t costLit (EntropyCtx_t *ectx, uint8_t lit) {
    return ectx->symbol_huffman_len[lit];
}


static size_t costMatch (EntropyCtx_t *ectx, uint16_t ml, uint16_t of) {
    uint32_t symbol, ml_ebits=0, ml_elen=0, of_symbol=0, of_ebits=0, of_elen=0;
    symbol = getLZ77SymbolAndExtraBits(ml, of, &ml_ebits, &ml_elen, &of_symbol, &of_ebits, &of_elen);
    return ectx->symbol_huffman_len[symbol] +
           ml_elen +
           ectx->of_huffman_len[of_symbol] +
           of_elen;
}


static void searchLZ77 (uint8_t *p_src, size_t src_len, searchLZ77_workspace_t *wksp) {
    size_t i, skip=0;
    int k;   //sizeof(searchLZ77_workspace_t);
    
    for (i=0; i+5<src_len; i++) {
        const uint8_t *p = p_src + i;
        
        uint64_t byte01234 = 0x5555555555ULL ^ ((((uint64_t)p[0]) | ((uint64_t)p[1] << 8) | ((uint64_t)p[2] << 16) | ((uint64_t)p[3] << 24)) | ((uint64_t)p[4] << 32) | ((uint64_t)p[5] << 40));
        uint32_t hash1 = (byte01234 & 0x00FFFFFFULL) % N_HASH;
        uint32_t hash2 = (byte01234 & 0xFFFFFFFFULL) % N_HASH;
        uint32_t hash3 =  byte01234                  % N_HASH;
        
        wksp->ml[i] = wksp->of[i] = 0;
        for (k=0; k<N_HASH_ROW; k++) {
            wksp->ml_cand[i][k] = 0;
        }
        
        if (skip > 0) {
            skip --;
        } else {
            size_t len_max = src_len - i;
            if (len_max > MAX_LZ77_ML) {
                len_max = MAX_LZ77_ML;
            }
            
            for (k=0; k<N_HASH_ROW; k++) {
                const uint8_t *p_match = (k < N_HASH1_ROW)             ? wksp->hash1_tab[hash1][k] : 
                                         (k < N_HASH1_ROW+N_HASH2_ROW) ? wksp->hash2_tab[hash2][k-N_HASH1_ROW] :
                                                                         wksp->hash3_tab[hash3][k-N_HASH1_ROW-N_HASH2_ROW] ;
                if (p_src <= p_match && p_match < p) {
                    size_t of = p - p_match;
                    if (MIN_LZ77_OF <= of && of <= MAX_LZ77_OF) {
                        size_t ml;
                        for (ml=0; ml<len_max && p_match[ml]==p[ml]; ml++);
                        //if (lz77_len > MIN_LZ77_LEN || (lz77_len >= MIN_LZ77_LEN && (p_curr-p_match) < 256)) {
                        if (ml > MIN_LZ77_ML || (ml >= MIN_LZ77_ML && of < 256)) {
                            wksp->ml_cand[i][k] = ml;
                            wksp->of_cand[i][k] = of;
                            if (wksp->ml[i] < ml) {
                                wksp->ml[i] = ml;
                                wksp->of[i] = of;
                            }
                        }
                    }
                }
            }

            if (wksp->ml[i] >= SKIP_LZ77_ML) {
                skip = wksp->ml[i] - 1;
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
        for (k=0; k<N_HASH_ROW; k++) {
            wksp->ml_cand[i][k] = 0;
        }
    }
}


static void optimizeLZ77 (uint8_t *p_src, size_t src_len, searchLZ77_workspace_t *wksp, EntropyCtx_t *ectx) {
    size_t i;
    int k;
    wksp->cost[src_len] = 0;
    for (i=src_len; i>0;) {
        i --;
        wksp->ml[i] = wksp->of[i] = 0;
        wksp->cost[i] = wksp->cost[i+1] + costLit(ectx, p_src[i]);
        for (k=0; k<N_HASH_ROW; k++) {
            uint16_t ml = wksp->ml_cand[i][k];
            uint16_t of = wksp->of_cand[i][k];
            if (ml > 0) {
                size_t match_cost = wksp->cost[i+ml] + costMatch(ectx, ml, of);
                if (wksp->cost[i] > match_cost) {
                    wksp->cost[i] = match_cost;
                    wksp->ml[i] = ml;
                    wksp->of[i] = of;
                }
            }
        }
    }
}


static int deflateBlockDynamicHuffman (struct StreamWriter_t *p_bs, uint8_t *p_src, uint32_t src_len, uint32_t is_final_block, searchLZ77_workspace_t *wksp) {
    uint32_t i;

    EntropyCtx_t ectx;
    
    // LZ77 search
    searchLZ77(p_src, src_len, wksp);
    
    // clear count
    for (i=0; i<N_SYMBOL; i++) ectx.symbol_cnt[i] = 0;
    for (i=0; i<N_LZ77_OF; i++) ectx.of_cnt[i] = 0;

    // scan block data, get LZ77 symbols, count them to build huffman tree ------------------------------------------------------
    for (i=0; i<src_len; i++) {
        ectx.symbol_cnt[p_src[i]] ++;
        if (wksp->ml[i] > 0) {
            uint32_t symbol=0, ml_ebits=0, ml_elen=0, of_symbol=0, of_ebits=0, of_elen=0;
            symbol = getLZ77SymbolAndExtraBits(wksp->ml[i], wksp->of[i], &ml_ebits, &ml_elen, &of_symbol, &of_ebits, &of_elen);
            ectx.symbol_cnt[symbol] ++;
            ectx.of_cnt[of_symbol] ++;
        }
    }
    ectx.symbol_cnt[SYMBOL_END] ++;
    
    // build huffman tree first time ------------------------------------------------------
    buildHuffmanLen (N_LZ77_OF, ectx.of_cnt, ectx.of_huffman_len, OFFSET_TREE_MERGE_INC);
    buildHuffmanBits(N_LZ77_OF, ectx.of_huffman_len, ectx.of_huffman_bits);
    buildHuffmanLen (N_SYMBOL, ectx.symbol_cnt, ectx.symbol_huffman_len, SYMBOL_TREE_MERGE_INC);
    buildHuffmanBits(N_SYMBOL, ectx.symbol_huffman_len, ectx.symbol_huffman_bits);
    
    // second-time LZ77 search
    optimizeLZ77(p_src, src_len, wksp, &ectx);
    
    // clear count
    for (i=0; i<N_SYMBOL; i++) ectx.symbol_cnt[i] = 0;
    for (i=0; i<N_LZ77_OF; i++) ectx.of_cnt[i] = 0;
    
    // scan block data, get LZ77 symbols, count them to build huffman tree ------------------------------------------------------
    for (i=0; i<src_len; i++) {
        uint32_t symbol=0, ml_ebits=0, ml_elen=0, of_symbol=0, of_ebits=0, of_elen=0;
        if (wksp->ml[i] > 0) {
            symbol = getLZ77SymbolAndExtraBits(wksp->ml[i], wksp->of[i], &ml_ebits, &ml_elen, &of_symbol, &of_ebits, &of_elen);
            ectx.symbol_cnt[symbol] ++;
            ectx.of_cnt[of_symbol] ++;
            i += (wksp->ml[i] - 1);
        } else {
            symbol = p_src[i];
            ectx.symbol_cnt[symbol] ++;
        }
    }
    ectx.symbol_cnt[SYMBOL_END] ++;
    
    // build huffman tree second time ------------------------------------------------------
    buildHuffmanLen (N_LZ77_OF, ectx.of_cnt, ectx.of_huffman_len, OFFSET_TREE_MERGE_INC);
    buildHuffmanBits(N_LZ77_OF, ectx.of_huffman_len, ectx.of_huffman_bits);
    buildHuffmanLen (N_SYMBOL, ectx.symbol_cnt, ectx.symbol_huffman_len, SYMBOL_TREE_MERGE_INC);
    buildHuffmanBits(N_SYMBOL, ectx.symbol_huffman_len, ectx.symbol_huffman_bits);
    
    // write block header ------------------------------------------------------
    RET_WHEN_ERR(appendBits(p_bs, (!!is_final_block), 1));  // final block ?
    RET_WHEN_ERR(appendBits(p_bs, 2, 2));                   // dynamic huffman tree
    
    {   // write huf tree
        uint32_t hlit, hof;
        
        for (hlit=N_LZ77_ML; hlit>0; hlit--)
            if (ectx.symbol_huffman_len[N_LITERAL+1+hlit-1] != 0)
                break;
        
        for (hof=N_LZ77_OF-1; hof>0; hof--)
            if (ectx.of_huffman_len[hof] != 0)
                break;
        
        RET_WHEN_ERR(appendBits(p_bs, hlit, 5));   // hlit
        RET_WHEN_ERR(appendBits(p_bs, hof , 5));   // hof
        RET_WHEN_ERR(appendBits(p_bs, 19-4, 4));   // hclen
        
        for (i=0; i<3; i++)
            RET_WHEN_ERR(appendBits(p_bs, 0, 3));
        for (i=0; i<16; i++)
            RET_WHEN_ERR(appendBits(p_bs, 4, 3));
        
        for (i=0; i<N_LITERAL+1+hlit; i++)
            RET_WHEN_ERR(appendBits(p_bs, bitsReverse(ectx.symbol_huffman_len[i],4), 4));
        
        for (i=0; i<hof+1; i++)
            RET_WHEN_ERR(appendBits(p_bs, bitsReverse(ectx.of_huffman_len[i],4), 4));
    }
    
    // rescan block data, encode as LZ77 and huffman ------------------------------------------------------
    for (i=0; i<src_len; i++) {
        uint32_t symbol=0, ml_ebits=0, ml_elen=0, of_symbol=0, of_ebits=0, of_elen=0;
        if (wksp->ml[i] > 0) {
            symbol = getLZ77SymbolAndExtraBits(wksp->ml[i], wksp->of[i], &ml_ebits, &ml_elen, &of_symbol, &of_ebits, &of_elen);
            //assert(symbol_huffman_len[symbol] > 0);
            i += (wksp->ml[i] - 1);
            RET_WHEN_ERR(appendBits(p_bs, ectx.symbol_huffman_bits[symbol], ectx.symbol_huffman_len[symbol]));  // write LZ77_ml_symbol
            RET_WHEN_ERR(appendBits(p_bs, ml_ebits, ml_elen));                                                  // write extra bits of LZ77_len
            RET_WHEN_ERR(appendBits(p_bs, ectx.of_huffman_bits[of_symbol], ectx.of_huffman_len[of_symbol]));    // write symbol     of LZ77_offset
            RET_WHEN_ERR(appendBits(p_bs, of_ebits, of_elen));                                                  // write extra bits of LZ77_offset
        } else {
            symbol = p_src[i];
            RET_WHEN_ERR(appendBits(p_bs, ectx.symbol_huffman_bits[symbol], ectx.symbol_huffman_len[symbol]));  // write literal
        }
    }
    RET_WHEN_ERR(appendBits(p_bs, ectx.symbol_huffman_bits[SYMBOL_END], ectx.symbol_huffman_len[SYMBOL_END]));  // write SYMBOL_END
    
    return R_OK;
}


static int deflateNullBlock (struct StreamWriter_t *p_bs, uint32_t is_final_block) {
    RET_WHEN_ERR(appendBits(p_bs, (!!is_final_block), 1));  // final block ?
    RET_WHEN_ERR(appendBits(p_bs, 1, 2));                   // fixed huffman tree
    RET_WHEN_ERR(appendBits(p_bs, static_symbol_huffman_bits[SYMBOL_END], static_symbol_huffman_len[SYMBOL_END]));  // write SYMBOL_END
    return R_OK;
}


int deflateEncode (uint8_t *p_src, size_t src_len, uint8_t *p_dst, size_t *p_dst_len) {
    struct StreamWriter_t bs = newStreamWriter(p_dst, (*p_dst_len));

    RET_ERR_IF(R_SRC_OVERFLOW,     src_len  > 0xFFFF0000U);
    RET_ERR_IF(R_DST_OVERFLOW, (*p_dst_len) > 0xFFFF0000U);

    if (src_len == 0) {
        RET_WHEN_ERR(deflateNullBlock(&bs, 1));                                                        // special case : data length = 0, fill a empty block
    } else {
        uint32_t i;
        searchLZ77_workspace_t *wksp = (searchLZ77_workspace_t*)malloc(sizeof(searchLZ77_workspace_t));
        RET_ERR_IF(R_MEM_RANOUT, (wksp==NULL));

        for (i=0; i<src_len; i+=MAX_BLOCK_LEN) {                                                       // for all blocks
            uint32_t is_final_block = (i+MAX_BLOCK_LEN >= src_len);
            uint32_t block_len = is_final_block ? src_len-i : MAX_BLOCK_LEN;
            RET_WHEN_ERR(deflateBlockDynamicHuffman(&bs, p_src+i, block_len, is_final_block, wksp));   // try dynamic huffman
        }

        free(wksp);
    }

    RET_WHEN_ERR(alignBitsToBytes(&bs));

    *p_dst_len = (bs.p_buf - p_dst);

    return R_OK;
}



int gzipC (uint8_t *p_src, size_t src_len, uint8_t *p_dst, size_t *p_dst_len) {
    uint8_t  *p_dst_tmp   = p_dst;
    uint8_t **pp_dst      = &p_dst_tmp;
    uint8_t  *p_dst_limit = p_dst + *p_dst_len;
    size_t    deflate_len;
    
    RET_ERR_IF(R_SRC_OVERFLOW, p_src > (p_src + src_len));
    RET_ERR_IF(R_DST_OVERFLOW, p_dst > p_dst_limit);
    
    RET_WHEN_ERR(writeValue(pp_dst, p_dst_limit, 0x00088B1FU, 4));
    RET_WHEN_ERR(writeValue(pp_dst, p_dst_limit, 0x00000000U, 4));
    RET_WHEN_ERR(writeValue(pp_dst, p_dst_limit,     0x0304U, 2));

    deflate_len = p_dst_limit - (*pp_dst);
    RET_WHEN_ERR(deflateEncode(p_src, src_len, *pp_dst, &deflate_len));
    (*pp_dst) += deflate_len;
    
    RET_WHEN_ERR(writeValue(pp_dst, p_dst_limit, calcCrc32(p_src, src_len), 4));
    RET_WHEN_ERR(writeValue(pp_dst, p_dst_limit,                  src_len , 4));
    
    *p_dst_len = (*pp_dst) - p_dst;

    return R_OK;
}
