#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <unistd.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <time.h>
#include <stdint.h>
#include <sched.h>
#include <sys/time.h>

#define CACHE_LINE_SIZE 64
#define MAX_THREADS 128
#define MAX_OUTPUT_LEN 4096
#define THREAD_BUFFER_SIZE (MAX_OUTPUT_LEN * 4)
#define FORCE_INLINE __attribute__((always_inline)) inline
#define CACHE_ALIGNED __attribute__((aligned(CACHE_LINE_SIZE)))
#define LIKELY(x) __builtin_expect(!!(x), 1)
#define UNLIKELY(x) __builtin_expect(!!(x), 0)

typedef int BOOL;
#define FALSE 0
#define TRUE 1

CACHE_ALIGNED atomic_bool g_found = false;
CACHE_ALIGNED atomic_uint_fast64_t g_passwords_checked = 0;
CACHE_ALIGNED atomic_bool g_brute_force_running = false;
int g_total_passwords = 0;
char* g_found_password = NULL;
char* g_found_message = NULL;

static CACHE_ALIGNED char thread_buffers[MAX_THREADS][THREAD_BUFFER_SIZE];

typedef unsigned long ICE_SUBKEY[3];
typedef struct ice_key_struct {
    int ik_size;
    int ik_rounds;
    ICE_SUBKEY* ik_keysched;
} ICE_KEY;

static CACHE_ALIGNED unsigned long ice_sbox[4][1024];
static int ice_sboxes_initialised = 0;

static const int ice_smod[4][4] = {{333,313,505,369},{379,375,319,391},{361,445,451,397},{397,425,395,505}};
static const int ice_sxor[4][4] = {{0x83,0x85,0x9b,0xcd},{0xcc,0xa7,0xad,0x41},{0x4b,0x2e,0xd4,0x33},{0xea,0xcb,0x2e,0x04}};
static const unsigned long ice_pbox[32] = {0x1,0x80,0x400,0x2000,0x80000,0x200000,0x1000000,0x40000000,0x8,0x20,0x100,0x4000,0x10000,0x800000,0x4000000,0x20000000,0x4,0x10,0x200,0x8000,0x20000,0x400000,0x8000000,0x10000000,0x2,0x40,0x800,0x1000,0x40000,0x100000,0x2000000,0x80000000};
static const int ice_keyrot[16] = {0,1,2,3,2,1,3,0,1,3,2,0,3,1,0,2};

static FORCE_INLINE unsigned int gf_mult_fast(register unsigned int a, register unsigned int b, register unsigned int m) {
    register unsigned int r = 0;
    while (b) {
        if (b & 1) r ^= a;
        a <<= 1;
        b >>= 1;
        if (a >= 256) a ^= m;
    }
    return r;
}

static FORCE_INLINE unsigned long gf_exp7_fast(register unsigned int b, unsigned int m) {
    if (UNLIKELY(b == 0)) return 0;
    register unsigned int x = gf_mult_fast(b, b, m);
    x = gf_mult_fast(b, x, m);
    x = gf_mult_fast(x, x, m);
    return gf_mult_fast(b, x, m);
}

static FORCE_INLINE unsigned long ice_perm32_fast(register unsigned long x) {
    register unsigned long r = 0;
    register const unsigned long* p = ice_pbox;
    
    for (int i = 0; i < 32; i++) {
        if (x & 1) r |= *p;
        p++;
        x >>= 1;
    }
    return r;
}

static void ice_sboxes_init(void) {
    for (int i = 0; i < 1024; i++) {
        int c = (i >> 1) & 0xff;
        int r = (i & 1) | ((i & 0x200) >> 8);
        
        unsigned long x = gf_exp7_fast(c ^ ice_sxor[0][r], ice_smod[0][r]) << 24;
        ice_sbox[0][i] = ice_perm32_fast(x);
        
        x = gf_exp7_fast(c ^ ice_sxor[1][r], ice_smod[1][r]) << 16;
        ice_sbox[1][i] = ice_perm32_fast(x);
        
        x = gf_exp7_fast(c ^ ice_sxor[2][r], ice_smod[2][r]) << 8;
        ice_sbox[2][i] = ice_perm32_fast(x);
        
        x = gf_exp7_fast(c ^ ice_sxor[3][r], ice_smod[3][r]);
        ice_sbox[3][i] = ice_perm32_fast(x);
    }
}

static ICE_KEY* ice_key_create(int n) {
    if (UNLIKELY(!ice_sboxes_initialised)) {
        ice_sboxes_init();
        ice_sboxes_initialised = 1;
    }
    
    ICE_KEY* k = (ICE_KEY*)malloc(sizeof(ICE_KEY));
    if (UNLIKELY(!k)) return NULL;
    
    if (n < 1) {
        k->ik_size = 1;
        k->ik_rounds = 8;
    } else {
        k->ik_size = n;
        k->ik_rounds = n * 16;
    }
    
    k->ik_keysched = (ICE_SUBKEY*)malloc(k->ik_rounds * sizeof(ICE_SUBKEY));
    if (UNLIKELY(!k->ik_keysched)) {
        free(k);
        return NULL;
    }
    
    return k;
}

static void ice_key_destroy(ICE_KEY* k) {
    if (!k) return;
    if (k->ik_keysched) free(k->ik_keysched);
    free(k);
}

static FORCE_INLINE unsigned long ice_f_fast(register unsigned long p, const ICE_SUBKEY sk) {
    unsigned long tl = ((p >> 16) & 0x3ff) | (((p >> 14) | (p << 18)) & 0xffc00);
    unsigned long tr = (p & 0x3ff) | ((p << 2) & 0xffc00);
    
    unsigned long al = sk[2] & (tl ^ tr);
    unsigned long ar = al ^ tr;
    al ^= tl;
    al ^= sk[0];
    ar ^= sk[1];
    
    return ice_sbox[0][al >> 10] | ice_sbox[1][al & 0x3ff] | 
           ice_sbox[2][ar >> 10] | ice_sbox[3][ar & 0x3ff];
}

static FORCE_INLINE void ice_key_encrypt_fast(const ICE_KEY* k, const unsigned char* p, unsigned char* c) {
    register unsigned long l, r;
    
    l = ((unsigned long)p[0] << 24) | ((unsigned long)p[1] << 16) | 
        ((unsigned long)p[2] << 8) | p[3];
    r = ((unsigned long)p[4] << 24) | ((unsigned long)p[5] << 16) | 
        ((unsigned long)p[6] << 8) | p[7];
    
    for (int i = 0; i < k->ik_rounds; i += 2) {
        l ^= ice_f_fast(r, k->ik_keysched[i]);
        r ^= ice_f_fast(l, k->ik_keysched[i + 1]);
    }
    
    c[3] = r & 0xff; r >>= 8;
    c[2] = r & 0xff; r >>= 8;
    c[1] = r & 0xff; r >>= 8;
    c[0] = r & 0xff;
    
    c[7] = l & 0xff; l >>= 8;
    c[6] = l & 0xff; l >>= 8;
    c[5] = l & 0xff; l >>= 8;
    c[4] = l & 0xff;
}

static void ice_key_sched_build(ICE_KEY* k, unsigned short* b, int n, const int* r) {
    for (int i = 0; i < 8; i++) {
        register int kr = r[i];
        ICE_SUBKEY* isk = &k->ik_keysched[n + i];
        
        (*isk)[0] = (*isk)[1] = (*isk)[2] = 0;
        
        for (int j = 0; j < 15; j++) {
            unsigned long* cs = &(*isk)[j % 3];
            for (int l = 0; l < 4; l++) {
                unsigned short* cb = &b[(kr + l) & 3];
                register int bit = *cb & 1;
                *cs = (*cs << 1) | bit;
                *cb = (*cb >> 1) | ((bit ^ 1) << 15);
            }
        }
    }
}

static void ice_key_set_fast(ICE_KEY* k, const unsigned char* key) {
    if (k->ik_rounds == 8) {
        unsigned short b[4];
        for (int i = 0; i < 4; i++) {
            b[3 - i] = (key[i * 2] << 8) | key[i * 2 + 1];
        }
        ice_key_sched_build(k, b, 0, ice_keyrot);
        return;
    }
    
    for (int i = 0; i < k->ik_size; i++) {
        unsigned short b[4];
        for (int j = 0; j < 4; j++) {
            b[3 - j] = (key[i * 8 + j * 2] << 8) | key[i * 8 + j * 2 + 1];
        }
        ice_key_sched_build(k, b, i * 8, ice_keyrot);
        ice_key_sched_build(k, b, k->ik_rounds - 8 - i * 8, &ice_keyrot[8]);
    }
}

static const char* huffcodes[256] = {"010011101110011001000","010011101110011001001","010011101110011001010","010011101110011001011","010011101110011001100","010011101110011001101","010011101110011001110","010011101110011001111","101100010101","0100100","101101","010011101110011010000","0100111011100111","010011101110011010001","010011101110011010010","010011101110011010011","010011101110011010100","010011101110011010101","010011101110011010110","010011101110011010111","010011101110011011000","010011101110011011001","010011101110011011010","010011101110011011011","010011101110011011100","010011101110011011101","010011101110011011110","010011101110001","010011101110011011111","01001110111000000000","01001110111000000001","01001110111000000010","111","0100101000","101100100","10111111111","101111010010","1011000101000","0010100010101","00101011","101111110","00100011","010010101","101111010011","1010110","10111110","101000","101111001","0010000","01001011","101100101","001010101","001010011","1011110111","1011001100","0100101001","1010011001","0010100010","101111000","10111111110","01001110110","10100101010","10111101000","1010010100","0010100011","01001111","1011110110","101100011","101001101","00100010","001010010","1011000000","1011001101","0111000","10110000011","10110001011","001010100","101100111","101001011","101100001","010011100","1010011110001","101001110","10100100","10101110","1011110101","10100111101","1011000100","10110000010","0100111010","010011101111","101001111001","001010001011","101001010111","1011000101001","10111111100","00101000100","0101","001001","110110","01000","1100","101010","011101","10001","0011","1010011111","0100110","01111","101110","0001","0110","100001","10111111101","11010","0000","1001","110111","0111001","001011","10101111","100000","1010011000","1010011110000","101001010110","0100111011101","0010100010100","01001110111000000011","010011101110000001000","010011101110000001001","010011101110000001010","010011101110000001011","010011101110000001100","010011101110000001101","010011101110000001110","010011101110000001111","010011101110000010000","010011101110000010001","010011101110000010010","010011101110000010011","010011101110000010100","010011101110000010101","010011101110000010110","010011101110000010111","010011101110000011000","010011101110000011001","010011101110000011010","010011101110000011011","010011101110000011100","010011101110000011101","010011101110000011110","010011101110000011111","010011101110000100000","010011101110000100001","010011101110000100010","010011101110000100011","010011101110000100100","010011101110000100101","010011101110000100110","010011101110000100111","010011101110000101000","010011101110000101001","010011101110000101010","010011101110000101011","010011101110000101100","010011101110000101101","010011101110000101110","010011101110000101111","010011101110000110000","010011101110000110001","010011101110000110010","010011101110000110011","010011101110000110100","010011101110000110101","010011101110000110110","010011101110000110111","010011101110000111000","010011101110000111001","010011101110000111010","010011101110000111011","010011101110000111100","010011101110000111101","010011101110000111110","010011101110000111111","010011101110010000000","010011101110010000001","010011101110010000010","010011101110010000011","010011101110010000100","010011101110010000101","010011101110010000110","010011101110010000111","010011101110010001000","010011101110010001001","010011101110010001010","010011101110010001011","010011101110010001100","010011101110010001101","010011101110010001110","010011101110010001111","010011101110010010000","010011101110010010001","010011101110010010010","010011101110010010011","010011101110010010100","010011101110010010101","010011101110010010110","010011101110010010111","010011101110010011000","010011101110010011001","010011101110010011010","010011101110010011011","010011101110010011100","010011101110010011101","010011101110010011110","010011101110010011111","010011101110010100000","010011101110010100001","010011101110010100010","010011101110010100011","010011101110010100100","010011101110010100101","010011101110010100110","010011101110010100111","010011101110010101000","010011101110010101001","010011101110010101010","010011101110010101011","010011101110010101100","010011101110010101101","010011101110010101110","010011101110010101111","010011101110010110000","010011101110010110001","010011101110010110010","010011101110010110011","010011101110010110100","010011101110010110101","010011101110010110110","010011101110010110111","010011101110010111000","010011101110010111001","010011101110010111010","010011101110010111011","010011101110010111100","010011101110010111101","010011101110010111110","010011101110010111111","010011101110011000000","010011101110011000001","010011101110011000010","010011101110011000011","010011101110011000100","010011101110011000101","010011101110011000110","010011101110011000111"};

#define HUFFMAN_HASH_SIZE 2048
#define HUFFMAN_HASH_MASK (HUFFMAN_HASH_SIZE - 1)

typedef struct {
    uint32_t hash;
    uint8_t value;
    uint8_t len;
    uint8_t padding[2];
} HuffmanEntry;

static HuffmanEntry huffman_table[HUFFMAN_HASH_SIZE];

static FORCE_INLINE uint32_t fast_hash_binary_compat(const char* str, int len) {
    uint32_t hash = 0x811c9dc5;
    for (int i = 0; i < len; i++) {
        hash ^= str[i];
        hash *= 0x01000193;
    }
    return hash;
}

void build_optimized_huffman_table(void) {
    memset(huffman_table, 0, sizeof(huffman_table));
    
    for (int i = 0; i < 256; i++) {
        int len = strlen(huffcodes[i]);
        uint32_t hash = fast_hash_binary_compat(huffcodes[i], len);
        uint32_t index = hash & HUFFMAN_HASH_MASK;
        
        while (huffman_table[index].len != 0) {
            index = (index + 1) & HUFFMAN_HASH_MASK;
        }
        
        huffman_table[index].hash = hash;
        huffman_table[index].value = i;
        huffman_table[index].len = len;
    }
}

static FORCE_INLINE int huffcode_find_optimized(uint32_t hash, int len) {
    uint32_t index = hash & HUFFMAN_HASH_MASK;
    
    for (int probe = 0; probe < 16; probe++) {
        HuffmanEntry* entry = &huffman_table[index];
        if (UNLIKELY(entry->len == 0)) return -1;
        if (LIKELY(entry->hash == hash && entry->len == len)) {
            return entry->value;
        }
        index = (index + 1) & HUFFMAN_HASH_MASK;
    }
    
    return -1;
}

typedef struct {
    uint32_t current_hash;
    int uncompress_bit_count;
    int output_value;
    size_t output_len;
    int output_bit_count;
    BOOL failed;
    char* output_buffer;
} OptimizedUncompState;

static FORCE_INLINE void uncomp_state_reset_fast(OptimizedUncompState* ustate) {
    ustate->uncompress_bit_count = 0;
    ustate->current_hash = 0x811c9dc5;
    ustate->output_bit_count = 0;
    ustate->output_value = 0;
    ustate->output_len = 0;
    ustate->failed = FALSE;
}

static FORCE_INLINE void uncomp_state_init_fast(OptimizedUncompState* ustate, char* buffer) {
    ustate->output_buffer = buffer;
    uncomp_state_reset_fast(ustate);
}

static FORCE_INLINE BOOL uncomp_output_bit_fast(OptimizedUncompState* ustate, int bit) {
    ustate->output_value = (ustate->output_value << 1) | bit;
    if (UNLIKELY(++ustate->output_bit_count == 8)) {
        if (UNLIKELY(ustate->output_len >= MAX_OUTPUT_LEN - 1)) {
            ustate->failed = TRUE;
            return FALSE;
        }
        ustate->output_buffer[ustate->output_len++] = ustate->output_value;
        ustate->output_value = 0;
        ustate->output_bit_count = 0;
    }
    return TRUE;
}

static FORCE_INLINE void uncomp_process_bit_fast(OptimizedUncompState* ustate, int bit, BOOL is_compressed) {
    if (UNLIKELY(ustate->failed)) return;
    
    if (UNLIKELY(!is_compressed)) {
        uncomp_output_bit_fast(ustate, bit);
        return;
    }
    
    ustate->current_hash = (ustate->current_hash ^ (bit ? '1' : '0')) * 0x01000193;
    ustate->uncompress_bit_count++;
    
    int code = huffcode_find_optimized(ustate->current_hash, ustate->uncompress_bit_count);
    if (LIKELY(code >= 0)) {
        if (UNLIKELY(ustate->output_len >= MAX_OUTPUT_LEN - 1)) {
            ustate->failed = TRUE;
            return;
        }
        ustate->output_buffer[ustate->output_len++] = code;
        ustate->uncompress_bit_count = 0;
        ustate->current_hash = 0x811c9dc5;
    } else if (UNLIKELY(ustate->uncompress_bit_count >= 31)) {
        ustate->failed = TRUE;
    }
}

typedef struct { 
    const char* pass; 
    size_t len; 
} Password;

typedef int BitstreamEvent;

typedef struct {
    Password* wordlist_chunk; 
    int num_words;
    const BitstreamEvent* event_stream; 
    int num_events; 
    const char* keyword;
    int thread_id;
    size_t keyword_len;
} ThreadArgs;

void* optimized_worker_v2(void* args) {
    ThreadArgs* t_args = (ThreadArgs*)args;
    int thread_id = t_args->thread_id;
    
    ICE_KEY* ice_key = ice_key_create(128);
    unsigned char iv[8];
    OptimizedUncompState state_c, state_noc;
    
    char* buffer_c = &thread_buffers[thread_id][0];
    char* buffer_noc = &thread_buffers[thread_id][MAX_OUTPUT_LEN];
    
    uncomp_state_init_fast(&state_c, buffer_c);
    uncomp_state_init_fast(&state_noc, buffer_noc);
    
    size_t keyword_len = t_args->keyword_len;
    
    int local_progress = 0;
    const int PROGRESS_BATCH = 32;
    
    const BitstreamEvent* events = t_args->event_stream;
    const int num_events = t_args->num_events;
    const char* keyword = t_args->keyword;
    
    for (int i = 0; i < t_args->num_words; i++) {
        if (UNLIKELY(atomic_load_explicit(&g_found, memory_order_relaxed))) break;
        
        if (UNLIKELY(++local_progress >= PROGRESS_BATCH)) {
            atomic_fetch_add_explicit(&g_passwords_checked, local_progress, memory_order_relaxed);
            local_progress = 0;
        }
        
        const char* current_password = t_args->wordlist_chunk[i].pass;
        size_t len = t_args->wordlist_chunk[i].len;
        
        if (len > 0 && current_password[len - 1] == '\r') {
            len--;
        }
        
        uncomp_state_reset_fast(&state_c);
        uncomp_state_reset_fast(&state_noc);
        
        if (UNLIKELY(!current_password || len == 0)) {
            ice_key->ik_size = 0;
            ice_key->ik_rounds = 0;
            memset(iv, 0, 8);
        } else {
            int level = (len * 7 + 63) / 64;
            if (level == 0) level = 1;
            else if (level > 128) level = 128;
            
            ice_key->ik_size = level;
            ice_key->ik_rounds = level * 16;
            
            unsigned char buf[1024] = {0};
            int k = 0;
            
            for (size_t p_idx = 0; p_idx < len && k <= 8184; p_idx++) {
                unsigned char c = current_password[p_idx] & 0x7f;
                int idx = k / 8;
                int bit = k & 7;
                
                if (bit == 0) {
                    buf[idx] = c << 1;
                } else if (bit == 1) {
                    buf[idx] |= c;
                } else {
                    buf[idx] |= c >> (bit - 1);
                    if (idx + 1 < 1024) buf[idx + 1] = c << (9 - bit);
                }
                k += 7;
            }
            
            ice_key_set_fast(ice_key, buf);
            ice_key_encrypt_fast(ice_key, buf, iv);
        }
        
        for (int j = 0; j < num_events; j++) {
            if (UNLIKELY(j % 20000 == 0 && atomic_load_explicit(&g_found, memory_order_relaxed))) {
                goto cleanup;
            }
            
            int spc = events[j];
            
            int b0 = spc & 1;
            int b1 = (spc >> 1) & 1;
            int b2 = (spc >> 2) & 1;
            
            for (int bit_idx = 0; bit_idx < 3; bit_idx++) {
                int b = (bit_idx == 0) ? b0 : (bit_idx == 1) ? b1 : b2;
                int plain_bit;
                
                if (UNLIKELY(!ice_key->ik_size)) {
                    plain_bit = b;
                } else {
                    unsigned char e_buf[8];
                    ice_key_encrypt_fast(ice_key, iv, e_buf);
                    plain_bit = ((e_buf[0] & 128) != 0) ? !b : b;
                    
                    for (int k = 0; k < 7; k++) {
                        iv[k] = (iv[k] << 1) | ((iv[k+1] & 128) >> 7);
                    }
                    iv[7] = (iv[7] << 1) | b;
                }
                
                uncomp_process_bit_fast(&state_c, plain_bit, TRUE);
                uncomp_process_bit_fast(&state_noc, plain_bit, FALSE);
            }
        }
        
        if (UNLIKELY(atomic_load_explicit(&g_found, memory_order_relaxed))) break;
        
        state_c.output_buffer[state_c.output_len] = '\0';
        state_noc.output_buffer[state_noc.output_len] = '\0';
        
        if (LIKELY(!state_c.failed && state_c.output_len >= keyword_len)) {
            if (UNLIKELY(strstr(state_c.output_buffer, keyword))) {
                if (!atomic_exchange_explicit(&g_found, true, memory_order_acq_rel)) {
                    g_found_password = strndup(current_password ? current_password : "<no password>", len);
                    g_found_message = strdup(state_c.output_buffer);
                }
                break;
            }
        }
        
        if (LIKELY(state_noc.output_len >= keyword_len)) {
            if (UNLIKELY(strstr(state_noc.output_buffer, keyword))) {
                if (!atomic_exchange_explicit(&g_found, true, memory_order_acq_rel)) {
                    g_found_password = strndup(current_password ? current_password : "<no password>", len);
                    g_found_message = strdup(state_noc.output_buffer);
                }
                break;
            }
        }
    }
    
cleanup:
    if (local_progress > 0) {
        atomic_fetch_add_explicit(&g_passwords_checked, local_progress, memory_order_relaxed);
    }
    
    ice_key_destroy(ice_key);
    return NULL;
}

void* fast_progress_monitor(void* args) {
    struct timeval start_time, current_time;
    gettimeofday(&start_time, NULL);
    
    uint_fast64_t last_checked = 0;
    double last_speed = 0.0;
    int stable_count = 0;
    
    printf("\r[*] Progress: 0.00%% (0/%d) | Speed: 0 pass/s     ", g_total_passwords);
    fflush(stdout);
    
    while (atomic_load_explicit(&g_brute_force_running, memory_order_relaxed)) {
        usleep(50000);
        
        uint_fast64_t current_checked = atomic_load_explicit(&g_passwords_checked, memory_order_relaxed);
        gettimeofday(&current_time, NULL);
        
        double elapsed = (current_time.tv_sec - start_time.tv_sec) + 
                        (current_time.tv_usec - start_time.tv_usec) / 1000000.0;
        
        if (elapsed > 0.1) {
            double current_speed = (double)current_checked / elapsed;
            
            if (stable_count < 10) {
                last_speed = current_speed;
                stable_count++;
            } else {
                last_speed = (last_speed * 0.8) + (current_speed * 0.2);
            }
            
            double pct = 0.0;
            if (g_total_passwords > 0) {
                pct = (double)current_checked / g_total_passwords * 100.0;
                if (pct > 100.0) pct = 100.0;
            }
            
            printf("\r[*] Progress: %6.2f%% (%8llu/%d) | Speed: %8.0f pass/s   ", 
                   pct, (unsigned long long)current_checked, g_total_passwords, last_speed);
            fflush(stdout);
        }
        
        if (atomic_load_explicit(&g_found, memory_order_relaxed) || 
            current_checked >= (uint_fast64_t)g_total_passwords) {
            break;
        }
    }
    
    printf("\n");
    fflush(stdout);
    return NULL;
}

BitstreamEvent* preprocess_input_file(const char* input_data, int* out_num_events) {
    size_t data_len = strlen(input_data);
    int capacity = 8192;
    BitstreamEvent* events = (BitstreamEvent*)malloc(sizeof(BitstreamEvent) * capacity);
    int count = 0;
    BOOL start_tab_found = FALSE;
    
    const char* current_pos = input_data;
    char line_buf[8192];
    
    while (*current_pos) {
        const char* eol = strchr(current_pos, '\n');
        size_t len = eol ? (eol - current_pos) : strlen(current_pos);
        if (len >= sizeof(line_buf)) len = sizeof(line_buf) - 1;
        
        memcpy(line_buf, current_pos, len);
        line_buf[len] = '\0';
        current_pos += len + (eol != NULL);
        
        char* s, *last_ws = NULL;
        for (s = line_buf; *s != '\0'; s++) {
            if (*s != ' ' && *s != '\t') last_ws = NULL;
            else if (last_ws == NULL) last_ws = s;
        }
        
        if (!last_ws) continue;
        
        if (!start_tab_found && *last_ws == ' ') continue;
        if (!start_tab_found && *last_ws == '\t') {
            start_tab_found = TRUE;
            last_ws++;
            if (*last_ws == '\0') continue;
        }
        
        if (start_tab_found) {
            int spc = 0;
            for (s = last_ws; ; s++) {
                if (*s == ' ') {
                    spc++;
                } else if (*s == '\t') {
                    if (count == capacity) {
                        capacity *= 2;
                        events = (BitstreamEvent*)realloc(events, sizeof(BitstreamEvent) * capacity);
                    }
                    events[count++] = spc;
                    spc = 0;
                } else if (*s == '\0') {
                    if (spc > 0) {
                        if (count == capacity) {
                            capacity *= 2;
                            events = (BitstreamEvent*)realloc(events, sizeof(BitstreamEvent) * capacity);
                        }
                        events[count++] = spc;
                    }
                    break;
                }
            }
        }
    }
    
    *out_num_events = count;
    return events;
}

char* read_file_to_memory(const char* filename) {
    FILE* f = fopen(filename, "rb");
    if (!f) {
        perror(filename);
        return NULL;
    }
    
    fseek(f, 0, SEEK_END);
    long size = ftell(f);
    fseek(f, 0, SEEK_SET);
    
    char* buffer = malloc(size + 1);
    if (!buffer) {
        fclose(f);
        return NULL;
    }
    
    if (fread(buffer, 1, size, f) != (size_t)size) {
        free(buffer);
        fclose(f);
        return NULL;
    }
    
    buffer[size] = '\0';
    fclose(f);
    return buffer;
}

Password* process_wordlist_fast(char* wordlist_data, int* total_passwords) {
    int count = 0;
    for (char* p = wordlist_data; *p; p++) {
        if (*p == '\n') count++;
    }
    if (strlen(wordlist_data) > 0 && wordlist_data[strlen(wordlist_data) - 1] != '\n') {
        count++;
    }
    
    Password* wordlist = malloc(sizeof(Password) * count);
    int idx = 0;
    
    char* line = wordlist_data;
    char* next_line;
    
    while (line && *line && idx < count) {
        next_line = strchr(line, '\n');
        size_t len;
        
        if (next_line) {
            len = next_line - line;
            *next_line = '\0';
            next_line++;
        } else {
            len = strlen(line);
        }
        
        wordlist[idx].pass = line;
        wordlist[idx].len = len;
        idx++;
        
        line = next_line;
    }
    
    *total_passwords = idx;
    return wordlist;
}

int main(int argc, char* argv[]) {
    setvbuf(stdout, NULL, _IONBF, 0);
    
    printf(" ________      ___    ___      ________       ___    ___ ___  ___  ________  ________      \n|\\   __  \\    |\\  \\  /  /|    |\\   ____\\     |\\  \\  /  /|\\  \\|\\  \\|\\   __  \\|\\   ___  \\    \n\\ \\  \\|\\ /_   \\ \\  \\/  / /    \\ \\  \\___|_    \\ \\  \\/  / | \\  \\\\\\  \\ \\  \\|\\  \\ \\  \\\\ \\  \\   \n \\ \\   __  \\   \\ \\    / /      \\ \\_____  \\    \\ \\    / / \\ \\  \\\\\\  \\ \\   __  \\ \\  \\\\ \\  \\  \n  \\ \\  \\|\\  \\   \\/  /  /        \\|____|\\  \\    \\/  /  /   \\ \\  \\\\\\  \\ \\  \\ \\  \\ \\  \\\\ \\  \\ \n   \\ \\_______\\__/  / /            ____\\_\\  \\ __/  / /      \\ \\_______\\ \\__\\ \\__\\ \\__\\\\ \\__\\\n    \\|_______|\\___/ /            |\\_________\\\\___/ /        \\|_______|\\|__|\\|__|\\|__| \\|__|\n             \\|___|/             \\|_________\\|___|/                                        \n                                                                                          \n                                                                                          \n");

    
    if (argc != 4) {
        fprintf(stderr, "Usage: %s <infile> <wordlist> keyword:<text>\n", argv[0]);
        return 1;
    }
    
    const char* keyword = strchr(argv[3], ':');
    if (!keyword || strncmp(argv[3], "keyword:", 8) != 0) {
        fprintf(stderr, "Invalid keyword format. Use keyword:text\n");
        return 1;
    }
    keyword++;
    
    printf("[*] LOADING...\n");
    build_optimized_huffman_table();
    
    char* input_data = read_file_to_memory(argv[1]);
    if (!input_data) return 1;
    
    char* wordlist_data = read_file_to_memory(argv[2]);
    if (!wordlist_data) {
        free(input_data);
        return 1;
    }
    
    int num_events;
    BitstreamEvent* event_stream = preprocess_input_file(input_data, &num_events);
    free(input_data);
    
    Password* wordlist = process_wordlist_fast(wordlist_data, &g_total_passwords);
    
    Password empty_pass = {.pass = NULL, .len = 0};
    ThreadArgs empty_args = {
        .wordlist_chunk = &empty_pass,
        .num_words = 1,
        .event_stream = event_stream,
        .num_events = num_events,
        .keyword = keyword,
        .keyword_len = strlen(keyword),
        .thread_id = 0
    };
    
    optimized_worker_v2(&empty_args);
    if (atomic_load(&g_found)) goto found;
    
    long num_cores = sysconf(_SC_NPROCESSORS_ONLN);
    if (num_cores <= 0) num_cores = 1;
    if (num_cores > MAX_THREADS) num_cores = MAX_THREADS;
    
    long optimal_threads = (num_cores * 3) / 2;
    if (optimal_threads > MAX_THREADS) optimal_threads = MAX_THREADS;
    if (optimal_threads < num_cores) optimal_threads = num_cores;
    
    atomic_store_explicit(&g_brute_force_running, true, memory_order_release);
    
    pthread_t progress_thread;
    pthread_create(&progress_thread, NULL, fast_progress_monitor, NULL);
    
    pthread_t* threads = malloc(sizeof(pthread_t) * optimal_threads);
    ThreadArgs* args = malloc(sizeof(ThreadArgs) * optimal_threads);
    
    int words_per_thread = g_total_passwords / optimal_threads;
    int remaining_words = g_total_passwords % optimal_threads;
    
    int current_offset = 0;
    for (int i = 0; i < optimal_threads; i++) {
        int words_for_this_thread = words_per_thread + (i < remaining_words ? 1 : 0);
        
        args[i].wordlist_chunk = &wordlist[current_offset];
        args[i].num_words = words_for_this_thread;
        args[i].event_stream = event_stream;
        args[i].num_events = num_events;
        args[i].keyword = keyword;
        args[i].keyword_len = strlen(keyword);
        args[i].thread_id = i;
        
        pthread_create(&threads[i], NULL, optimized_worker_v2, &args[i]);
        
        current_offset += words_for_this_thread;
    }
    
    for (int i = 0; i < optimal_threads; i++) {
        pthread_join(threads[i], NULL);
    }
    
    atomic_store_explicit(&g_brute_force_running, false, memory_order_release);
    pthread_join(progress_thread, NULL);
    
found:
    if (g_found_password) {
        printf("\n[+] Password Found: %s\n", g_found_password);
        printf("Message:\n%s\n", g_found_message);
        free(g_found_password);
        free(g_found_message);
    } else {
        fprintf(stderr, "[-] Password not found.\n");
    }
    
    free(event_stream);
    free(wordlist_data);
    free(wordlist);
    free(threads);
    free(args);
    
    return 0;
}