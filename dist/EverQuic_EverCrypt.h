

#ifndef __EverQuic_EverCrypt_H
#define __EverQuic_EverCrypt_H
#include "kremlin/internal/target.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <stdint.h>
#include <stdbool.h>
#include <string.h>




#define Spec_Hash_Definitions_SHA2_224 0
#define Spec_Hash_Definitions_SHA2_256 1
#define Spec_Hash_Definitions_SHA2_384 2
#define Spec_Hash_Definitions_SHA2_512 3
#define Spec_Hash_Definitions_SHA1 4
#define Spec_Hash_Definitions_MD5 5
#define Spec_Hash_Definitions_Blake2S 6
#define Spec_Hash_Definitions_Blake2B 7

typedef uint8_t Spec_Hash_Definitions_hash_alg;

#define Spec_Agile_Cipher_AES128 0
#define Spec_Agile_Cipher_AES256 1
#define Spec_Agile_Cipher_CHACHA20 2

typedef uint8_t Spec_Agile_Cipher_cipher_alg;

Prims_int Spec_Agile_Cipher_key_length(Spec_Agile_Cipher_cipher_alg a);

#define Spec_Agile_AEAD_AES128_GCM 0
#define Spec_Agile_AEAD_AES256_GCM 1
#define Spec_Agile_AEAD_CHACHA20_POLY1305 2
#define Spec_Agile_AEAD_AES128_CCM 3
#define Spec_Agile_AEAD_AES256_CCM 4
#define Spec_Agile_AEAD_AES128_CCM8 5
#define Spec_Agile_AEAD_AES256_CCM8 6

typedef uint8_t Spec_Agile_AEAD_alg;

Spec_Agile_Cipher_cipher_alg
Spec_Agile_AEAD_cipher_alg_of_supported_alg(Spec_Agile_AEAD_alg a);

#define Spec_Cipher_Expansion_Hacl_CHACHA20 0
#define Spec_Cipher_Expansion_Vale_AES128 1
#define Spec_Cipher_Expansion_Vale_AES256 2

typedef uint8_t Spec_Cipher_Expansion_impl;

#define EverCrypt_Error_Success 0
#define EverCrypt_Error_UnsupportedAlgorithm 1
#define EverCrypt_Error_InvalidKey 2
#define EverCrypt_Error_AuthenticationFailure 3
#define EverCrypt_Error_InvalidIVLength 4
#define EverCrypt_Error_DecodeError 5

typedef uint8_t EverCrypt_Error_error_code;

typedef struct EverCrypt_CTR_state_s_s EverCrypt_CTR_state_s;

extern EverCrypt_Error_error_code
EverCrypt_CTR_create_in(
  Spec_Agile_Cipher_cipher_alg a,
  EverCrypt_CTR_state_s **r,
  uint8_t *dst,
  uint8_t *k,
  uint32_t iv,
  uint32_t iv_len
);

extern void
EverCrypt_CTR_init(
  EverCrypt_CTR_state_s *a,
  uint8_t *p,
  uint8_t *k,
  uint32_t iv,
  uint32_t iv_len
);

extern void EverCrypt_CTR_update_block(EverCrypt_CTR_state_s *a, uint8_t *p, uint8_t *dst);

extern void
EverCrypt_HKDF_expand(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);

extern void
EverCrypt_HKDF_extract(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);

typedef struct EverCrypt_AEAD_state_s_s EverCrypt_AEAD_state_s;

extern EverCrypt_Error_error_code
EverCrypt_AEAD_create_in(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s **r, uint8_t *dst);

extern EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt(
  EverCrypt_AEAD_state_s *a,
  uint8_t *s,
  uint32_t iv,
  uint8_t *iv_len,
  uint32_t ad,
  uint8_t *ad_len,
  uint32_t plain,
  uint8_t *plain_len,
  uint8_t *cipher
);

extern EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt(
  EverCrypt_AEAD_state_s *a,
  uint8_t *s,
  uint32_t iv,
  uint8_t *iv_len,
  uint32_t ad,
  uint8_t *ad_len,
  uint32_t cipher,
  uint8_t *cipher_len,
  uint8_t *tag
);


#define __EverQuic_EverCrypt_H_DEFINED
#endif
