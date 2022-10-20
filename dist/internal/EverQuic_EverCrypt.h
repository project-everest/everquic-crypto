

#ifndef __internal_EverQuic_EverCrypt_H
#define __internal_EverQuic_EverCrypt_H



#include "../EverQuic_EverCrypt.h"
#include "krml/internal/target.h"
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#define Spec_Agile_Cipher_AES128 0
#define Spec_Agile_Cipher_AES256 1
#define Spec_Agile_Cipher_CHACHA20 2

typedef uint8_t Spec_Agile_Cipher_cipher_alg;

Prims_int Spec_Agile_Cipher_key_length(Spec_Agile_Cipher_cipher_alg a);

Spec_Agile_Cipher_cipher_alg
Spec_Agile_AEAD_cipher_alg_of_supported_alg(Spec_Agile_AEAD_alg a);

typedef struct EverCrypt_AEAD_state_s_s EverCrypt_AEAD_state_s;

extern EverCrypt_Error_error_code
EverCrypt_AEAD_create_in(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s **dst, uint8_t *k);

extern EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt(
  EverCrypt_AEAD_state_s *s,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
);

extern EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt(
  EverCrypt_AEAD_state_s *s,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
);

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

typedef struct NotEverCrypt_CTR_state_s_s NotEverCrypt_CTR_state_s;

EverCrypt_Error_error_code
NotEverCrypt_CTR_create_in(
  Spec_Agile_Cipher_cipher_alg a,
  NotEverCrypt_CTR_state_s **dst,
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint32_t c
);

void
NotEverCrypt_CTR_init(
  NotEverCrypt_CTR_state_s *p,
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint32_t c
);

void NotEverCrypt_CTR_update_block(NotEverCrypt_CTR_state_s *p, uint8_t *dst, uint8_t *src);


#define __internal_EverQuic_EverCrypt_H_DEFINED
#endif
