

#include "internal/EverQuic_EverCrypt.h"



typedef Prims_list__uint8_t *bytes;

static Prims_int size_key = (krml_checked_int_t)32;

#define AES128 0
#define AES256 1

typedef uint8_t variant;

static Prims_int key_size(variant v)
{
  switch (v)
  {
    case AES128:
      {
        return (krml_checked_int_t)16;
      }
    case AES256:
      {
        return (krml_checked_int_t)32;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

typedef uint64_t als_ret;

extern bool EverCrypt_AutoConfig2_has_aesni();

extern bool EverCrypt_AutoConfig2_has_pclmulqdq();

extern bool EverCrypt_AutoConfig2_has_avx();

extern bool EverCrypt_AutoConfig2_has_sse();

static variant aes_alg_of_alg(Spec_Agile_Cipher_cipher_alg a)
{
  switch (a)
  {
    case Spec_Agile_Cipher_AES128:
      {
        return AES128;
      }
    case Spec_Agile_Cipher_AES256:
      {
        return AES256;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

Prims_int Spec_Agile_Cipher_key_length(Spec_Agile_Cipher_cipher_alg a)
{
  switch (a)
  {
    case Spec_Agile_Cipher_AES128:
      {
        return key_size(aes_alg_of_alg(a));
      }
    case Spec_Agile_Cipher_AES256:
      {
        return key_size(aes_alg_of_alg(a));
      }
    case Spec_Agile_Cipher_CHACHA20:
      {
        return size_key;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

Spec_Agile_Cipher_cipher_alg Spec_Agile_AEAD_cipher_alg_of_supported_alg(Spec_Agile_AEAD_alg a)
{
  switch (a)
  {
    case Spec_Agile_AEAD_AES128_GCM:
      {
        return Spec_Agile_Cipher_AES128;
      }
    case Spec_Agile_AEAD_AES256_GCM:
      {
        return Spec_Agile_Cipher_AES256;
      }
    case Spec_Agile_AEAD_CHACHA20_POLY1305:
      {
        return Spec_Agile_Cipher_CHACHA20;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

extern uint64_t aes128_key_expansion(uint8_t *x0, uint8_t *x1);

extern uint64_t aes256_key_expansion(uint8_t *x0, uint8_t *x1);

static inline void quarter_round(uint32_t *st, uint32_t a, uint32_t b, uint32_t c, uint32_t d)
{
  uint32_t sta = st[a];
  uint32_t stb0 = st[b];
  uint32_t std0 = st[d];
  uint32_t sta10 = sta + stb0;
  uint32_t std10 = std0 ^ sta10;
  uint32_t std2 = std10 << (uint32_t)16U | std10 >> (uint32_t)16U;
  st[a] = sta10;
  st[d] = std2;
  uint32_t sta0 = st[c];
  uint32_t stb1 = st[d];
  uint32_t std3 = st[b];
  uint32_t sta11 = sta0 + stb1;
  uint32_t std11 = std3 ^ sta11;
  uint32_t std20 = std11 << (uint32_t)12U | std11 >> (uint32_t)20U;
  st[c] = sta11;
  st[b] = std20;
  uint32_t sta2 = st[a];
  uint32_t stb2 = st[b];
  uint32_t std4 = st[d];
  uint32_t sta12 = sta2 + stb2;
  uint32_t std12 = std4 ^ sta12;
  uint32_t std21 = std12 << (uint32_t)8U | std12 >> (uint32_t)24U;
  st[a] = sta12;
  st[d] = std21;
  uint32_t sta3 = st[c];
  uint32_t stb = st[d];
  uint32_t std = st[b];
  uint32_t sta1 = sta3 + stb;
  uint32_t std1 = std ^ sta1;
  uint32_t std22 = std1 << (uint32_t)7U | std1 >> (uint32_t)25U;
  st[c] = sta1;
  st[b] = std22;
}

static inline void double_round(uint32_t *st)
{
  quarter_round(st, (uint32_t)0U, (uint32_t)4U, (uint32_t)8U, (uint32_t)12U);
  quarter_round(st, (uint32_t)1U, (uint32_t)5U, (uint32_t)9U, (uint32_t)13U);
  quarter_round(st, (uint32_t)2U, (uint32_t)6U, (uint32_t)10U, (uint32_t)14U);
  quarter_round(st, (uint32_t)3U, (uint32_t)7U, (uint32_t)11U, (uint32_t)15U);
  quarter_round(st, (uint32_t)0U, (uint32_t)5U, (uint32_t)10U, (uint32_t)15U);
  quarter_round(st, (uint32_t)1U, (uint32_t)6U, (uint32_t)11U, (uint32_t)12U);
  quarter_round(st, (uint32_t)2U, (uint32_t)7U, (uint32_t)8U, (uint32_t)13U);
  quarter_round(st, (uint32_t)3U, (uint32_t)4U, (uint32_t)9U, (uint32_t)14U);
}

static inline void rounds(uint32_t *st)
{
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
}

static inline void chacha20_core(uint32_t *k, uint32_t *ctx, uint32_t ctr)
{
  memcpy(k, ctx, (uint32_t)16U * sizeof (uint32_t));
  uint32_t ctr_u32 = ctr;
  k[12U] = k[12U] + ctr_u32;
  rounds(k);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint32_t *os = k;
    uint32_t x = k[i] + ctx[i];
    os[i] = x;
  }
  k[12U] = k[12U] + ctr_u32;
}

static const
uint32_t
chacha20_constants[4U] =
  { (uint32_t)0x61707865U, (uint32_t)0x3320646eU, (uint32_t)0x79622d32U, (uint32_t)0x6b206574U };

static void chacha20_init(uint32_t *ctx, uint8_t *k, uint8_t *n, uint32_t ctr)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint32_t *os = ctx;
    uint32_t x = chacha20_constants[i];
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint32_t *os = ctx + (uint32_t)4U;
    uint8_t *bj = k + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;
  }
  ctx[12U] = ctr;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)3U; i++)
  {
    uint32_t *os = ctx + (uint32_t)13U;
    uint8_t *bj = n + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;
  }
}

static void chacha20_encrypt_block(uint32_t *ctx, uint8_t *out, uint32_t incr, uint8_t *text)
{
  uint32_t k[16U] = { 0U };
  chacha20_core(k, ctx, incr);
  uint32_t bl[16U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint32_t *os = bl;
    uint8_t *bj = text + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint32_t *os = bl;
    uint32_t x = bl[i] ^ k[i];
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    store32_le(out + i * (uint32_t)4U, bl[i]);
}

extern uint64_t aes128_keyhash_init(uint8_t *x0, uint8_t *x1);

extern uint64_t aes256_keyhash_init(uint8_t *x0, uint8_t *x1);

#define Hacl_CHACHA20 0
#define Vale_AES128 1
#define Vale_AES256 2

typedef uint8_t impl;

static Spec_Agile_Cipher_cipher_alg cipher_alg_of_impl(impl i)
{
  switch (i)
  {
    case Hacl_CHACHA20:
      {
        return Spec_Agile_Cipher_CHACHA20;
      }
    case Vale_AES128:
      {
        return Spec_Agile_Cipher_AES128;
      }
    case Vale_AES256:
      {
        return Spec_Agile_Cipher_AES256;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

typedef struct EverCrypt_AEAD_state_s_s
{
  impl impl;
  uint8_t *ek;
}
EverCrypt_AEAD_state_s;

extern uint64_t
gctr128_bytes(
  uint8_t *x0,
  uint64_t x1,
  uint8_t *x2,
  uint8_t *x3,
  uint8_t *x4,
  uint8_t *x5,
  uint64_t x6
);

extern uint64_t
gctr256_bytes(
  uint8_t *x0,
  uint64_t x1,
  uint8_t *x2,
  uint8_t *x3,
  uint8_t *x4,
  uint8_t *x5,
  uint64_t x6
);

typedef struct NotEverCrypt_CTR_state_s_s
{
  impl i;
  uint8_t *iv;
  uint32_t iv_len;
  uint8_t *xkey;
  uint32_t ctr;
}
NotEverCrypt_CTR_state_s;

static impl vale_impl_of_alg(Spec_Agile_Cipher_cipher_alg a)
{
  switch (a)
  {
    case Spec_Agile_Cipher_AES128:
      {
        return Vale_AES128;
      }
    case Spec_Agile_Cipher_AES256:
      {
        return Vale_AES256;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

EverCrypt_Error_error_code
NotEverCrypt_CTR_create_in(
  Spec_Agile_Cipher_cipher_alg a,
  NotEverCrypt_CTR_state_s **dst,
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint32_t c
)
{
  switch (a)
  {
    case Spec_Agile_Cipher_AES128:
      {
        bool has_aesni = EverCrypt_AutoConfig2_has_aesni();
        bool has_pclmulqdq = EverCrypt_AutoConfig2_has_pclmulqdq();
        bool has_avx = EverCrypt_AutoConfig2_has_avx();
        bool has_sse = EverCrypt_AutoConfig2_has_sse();
        if (iv_len < (uint32_t)12U)
          return EverCrypt_Error_InvalidIVLength;
        else
        {
          #if EVERCRYPT_TARGETCONFIG_HACL_CAN_COMPILE_VALE
          if (has_aesni && has_pclmulqdq && has_avx && has_sse)
          {
            uint8_t *ek = KRML_HOST_CALLOC((uint32_t)304U, sizeof (uint8_t));
            uint8_t *keys_b = ek;
            uint8_t *hkeys_b = ek + (uint32_t)176U;
            uint64_t scrut = aes128_key_expansion(k, keys_b);
            uint64_t scrut0 = aes128_keyhash_init(keys_b, hkeys_b);
            uint8_t *iv_ = KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint8_t));
            memcpy(iv_, iv, iv_len * sizeof (uint8_t));
            KRML_CHECK_SIZE(sizeof (NotEverCrypt_CTR_state_s), (uint32_t)1U);
            NotEverCrypt_CTR_state_s *p = KRML_HOST_MALLOC(sizeof (NotEverCrypt_CTR_state_s));
            p[0U]
            =
              (
                (NotEverCrypt_CTR_state_s){
                  .i = vale_impl_of_alg(cipher_alg_of_impl(Vale_AES128)),
                  .iv = iv_,
                  .iv_len = iv_len,
                  .xkey = ek,
                  .ctr = c
                }
              );
            *dst = p;
            return EverCrypt_Error_Success;
          }
          #endif
          return EverCrypt_Error_UnsupportedAlgorithm;
        }
        break;
      }
    case Spec_Agile_Cipher_AES256:
      {
        bool has_aesni = EverCrypt_AutoConfig2_has_aesni();
        bool has_pclmulqdq = EverCrypt_AutoConfig2_has_pclmulqdq();
        bool has_avx = EverCrypt_AutoConfig2_has_avx();
        bool has_sse = EverCrypt_AutoConfig2_has_sse();
        if (iv_len < (uint32_t)12U)
          return EverCrypt_Error_InvalidIVLength;
        else
        {
          #if EVERCRYPT_TARGETCONFIG_HACL_CAN_COMPILE_VALE
          if (has_aesni && has_pclmulqdq && has_avx && has_sse)
          {
            uint8_t *ek = KRML_HOST_CALLOC((uint32_t)368U, sizeof (uint8_t));
            uint8_t *keys_b = ek;
            uint8_t *hkeys_b = ek + (uint32_t)240U;
            uint64_t scrut = aes256_key_expansion(k, keys_b);
            uint64_t scrut0 = aes256_keyhash_init(keys_b, hkeys_b);
            uint8_t *iv_ = KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint8_t));
            memcpy(iv_, iv, iv_len * sizeof (uint8_t));
            KRML_CHECK_SIZE(sizeof (NotEverCrypt_CTR_state_s), (uint32_t)1U);
            NotEverCrypt_CTR_state_s *p = KRML_HOST_MALLOC(sizeof (NotEverCrypt_CTR_state_s));
            p[0U]
            =
              (
                (NotEverCrypt_CTR_state_s){
                  .i = vale_impl_of_alg(cipher_alg_of_impl(Vale_AES256)),
                  .iv = iv_,
                  .iv_len = iv_len,
                  .xkey = ek,
                  .ctr = c
                }
              );
            *dst = p;
            return EverCrypt_Error_Success;
          }
          #endif
          return EverCrypt_Error_UnsupportedAlgorithm;
        }
        break;
      }
    case Spec_Agile_Cipher_CHACHA20:
      {
        uint8_t *ek = KRML_HOST_CALLOC((uint32_t)32U, sizeof (uint8_t));
        memcpy(ek, k, (uint32_t)32U * sizeof (uint8_t));
        KRML_CHECK_SIZE(sizeof (uint8_t), iv_len);
        uint8_t *iv_ = KRML_HOST_CALLOC(iv_len, sizeof (uint8_t));
        memcpy(iv_, iv, iv_len * sizeof (uint8_t));
        KRML_CHECK_SIZE(sizeof (NotEverCrypt_CTR_state_s), (uint32_t)1U);
        NotEverCrypt_CTR_state_s *p = KRML_HOST_MALLOC(sizeof (NotEverCrypt_CTR_state_s));
        p[0U]
        =
          (
            (NotEverCrypt_CTR_state_s){
              .i = Hacl_CHACHA20,
              .iv = iv_,
              .iv_len = (uint32_t)12U,
              .xkey = ek,
              .ctr = c
            }
          );
        *dst = p;
        return EverCrypt_Error_Success;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

void
NotEverCrypt_CTR_init(
  NotEverCrypt_CTR_state_s *p,
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint32_t c
)
{
  NotEverCrypt_CTR_state_s scrut0 = *p;
  uint8_t *ek = scrut0.xkey;
  uint8_t *iv_ = scrut0.iv;
  impl i = scrut0.i;
  memcpy(iv_, iv, iv_len * sizeof (uint8_t));
  switch (i)
  {
    case Vale_AES128:
      {
        #if EVERCRYPT_TARGETCONFIG_HACL_CAN_COMPILE_VALE
        uint8_t *keys_b = ek;
        uint8_t *hkeys_b = ek + (uint32_t)176U;
        uint64_t scrut = aes128_key_expansion(k, keys_b);
        uint64_t scrut0 = aes128_keyhash_init(keys_b, hkeys_b);
        #endif
        break;
      }
    case Vale_AES256:
      {
        #if EVERCRYPT_TARGETCONFIG_HACL_CAN_COMPILE_VALE
        uint8_t *keys_b = ek;
        uint8_t *hkeys_b = ek + (uint32_t)240U;
        uint64_t scrut = aes256_key_expansion(k, keys_b);
        uint64_t scrut0 = aes256_keyhash_init(keys_b, hkeys_b);
        #endif
        break;
      }
    case Hacl_CHACHA20:
      {
        memcpy(ek, k, (uint32_t)32U * sizeof (uint8_t));
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  *p = ((NotEverCrypt_CTR_state_s){ .i = i, .iv = iv_, .iv_len = iv_len, .xkey = ek, .ctr = c });
}

void NotEverCrypt_CTR_update_block(NotEverCrypt_CTR_state_s *p, uint8_t *dst, uint8_t *src)
{
  NotEverCrypt_CTR_state_s scrut = *p;
  impl i = scrut.i;
  uint8_t *iv = scrut.iv;
  uint8_t *ek = scrut.xkey;
  uint32_t c0 = scrut.ctr;
  switch (i)
  {
    case Vale_AES128:
      {
        #if EVERCRYPT_TARGETCONFIG_HACL_CAN_COMPILE_VALE
        NotEverCrypt_CTR_state_s scrut = *p;
        uint32_t c01 = scrut.ctr;
        uint8_t *ek1 = scrut.xkey;
        uint32_t iv_len1 = scrut.iv_len;
        uint8_t *iv1 = scrut.iv;
        uint8_t ctr_block[16U] = { 0U };
        memcpy(ctr_block, iv1, iv_len1 * sizeof (uint8_t));
        FStar_UInt128_uint128 uu____0 = load128_be(ctr_block);
        FStar_UInt128_uint128
        c = FStar_UInt128_add_mod(uu____0, FStar_UInt128_uint64_to_uint128((uint64_t)c01));
        store128_le(ctr_block, c);
        uint8_t *uu____1 = ek1;
        uint8_t inout_b[16U] = { 0U };
        uint32_t num_blocks = (uint32_t)(uint64_t)16U / (uint32_t)16U;
        uint32_t num_bytes_ = num_blocks * (uint32_t)16U;
        uint8_t *in_b_ = src;
        uint8_t *out_b_ = dst;
        memcpy(inout_b,
          src + num_bytes_,
          (uint32_t)(uint64_t)16U % (uint32_t)16U * sizeof (uint8_t));
        uint64_t
        scrut0 =
          gctr128_bytes(in_b_,
            (uint64_t)16U,
            out_b_,
            inout_b,
            uu____1,
            ctr_block,
            (uint64_t)num_blocks);
        memcpy(dst + num_bytes_,
          inout_b,
          (uint32_t)(uint64_t)16U % (uint32_t)16U * sizeof (uint8_t));
        uint32_t c1 = c01 + (uint32_t)1U;
        *p
        =
          (
            (NotEverCrypt_CTR_state_s){
              .i = Vale_AES128,
              .iv = iv1,
              .iv_len = iv_len1,
              .xkey = ek1,
              .ctr = c1
            }
          );
        #endif
        break;
      }
    case Vale_AES256:
      {
        #if EVERCRYPT_TARGETCONFIG_HACL_CAN_COMPILE_VALE
        NotEverCrypt_CTR_state_s scrut = *p;
        uint32_t c01 = scrut.ctr;
        uint8_t *ek1 = scrut.xkey;
        uint32_t iv_len1 = scrut.iv_len;
        uint8_t *iv1 = scrut.iv;
        uint8_t ctr_block[16U] = { 0U };
        memcpy(ctr_block, iv1, iv_len1 * sizeof (uint8_t));
        FStar_UInt128_uint128 uu____2 = load128_be(ctr_block);
        FStar_UInt128_uint128
        c = FStar_UInt128_add_mod(uu____2, FStar_UInt128_uint64_to_uint128((uint64_t)c01));
        store128_le(ctr_block, c);
        uint8_t *uu____3 = ek1;
        uint8_t inout_b[16U] = { 0U };
        uint32_t num_blocks = (uint32_t)(uint64_t)16U / (uint32_t)16U;
        uint32_t num_bytes_ = num_blocks * (uint32_t)16U;
        uint8_t *in_b_ = src;
        uint8_t *out_b_ = dst;
        memcpy(inout_b,
          src + num_bytes_,
          (uint32_t)(uint64_t)16U % (uint32_t)16U * sizeof (uint8_t));
        uint64_t
        scrut0 =
          gctr256_bytes(in_b_,
            (uint64_t)16U,
            out_b_,
            inout_b,
            uu____3,
            ctr_block,
            (uint64_t)num_blocks);
        memcpy(dst + num_bytes_,
          inout_b,
          (uint32_t)(uint64_t)16U % (uint32_t)16U * sizeof (uint8_t));
        uint32_t c1 = c01 + (uint32_t)1U;
        *p
        =
          (
            (NotEverCrypt_CTR_state_s){
              .i = Vale_AES256,
              .iv = iv1,
              .iv_len = iv_len1,
              .xkey = ek1,
              .ctr = c1
            }
          );
        #endif
        break;
      }
    case Hacl_CHACHA20:
      {
        uint32_t ctx[16U] = { 0U };
        chacha20_init(ctx, ek, iv, (uint32_t)0U);
        chacha20_encrypt_block(ctx, dst, c0, src);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

