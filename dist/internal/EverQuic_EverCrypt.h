

#ifndef __internal_EverQuic_EverCrypt_H
#define __internal_EverQuic_EverCrypt_H

#include "internal/LowStar.h"
#include "internal/EverQuic_Krmllib.h"
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

krml_checked_int_t Spec_Agile_Cipher_key_length(Spec_Agile_Cipher_cipher_alg a);

Spec_Agile_Cipher_cipher_alg
Spec_Agile_AEAD_cipher_alg_of_supported_alg(Spec_Agile_AEAD_alg a);

typedef struct EverCrypt_AEAD_state_s_s EverCrypt_AEAD_state_s;

/**
Create the required AEAD state for the algorithm.

Note: The caller must free the AEAD state by calling `EverCrypt_AEAD_free`.

@param a The argument `a` must be either of:
  * `Spec_Agile_AEAD_AES128_GCM` (KEY_LEN=16),
  * `Spec_Agile_AEAD_AES256_GCM` (KEY_LEN=32), or
  * `Spec_Agile_AEAD_CHACHA20_POLY1305` (KEY_LEN=32).
@param dst Pointer to a pointer where the address of the allocated AEAD state will be written to.
@param k Pointer to `KEY_LEN` bytes of memory where the key is read from. The size depends on the used algorithm, see above.

@return The function returns `EverCrypt_Error_Success` on success or
  `EverCrypt_Error_UnsupportedAlgorithm` in case of a bad algorithm identifier.
  (See `EverCrypt_Error.h`.)
*/
extern EverCrypt_Error_error_code
EverCrypt_AEAD_create_in(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s **dst, uint8_t *k);

/**
Encrypt and authenticate a message (`plain`) with associated data (`ad`).

@param s Pointer to the The AEAD state created by `EverCrypt_AEAD_create_in`. It already contains the encryption key.
@param iv Pointer to `iv_len` bytes of memory where the nonce is read from.
@param iv_len Length of the nonce. Note: ChaCha20Poly1305 requires a 12 byte nonce.
@param ad Pointer to `ad_len` bytes of memory where the associated data is read from.
@param ad_len Length of the associated data.
@param plain Pointer to `plain_len` bytes of memory where the to-be-encrypted plaintext is read from.
@param plain_len Length of the to-be-encrypted plaintext.
@param cipher Pointer to `plain_len` bytes of memory where the ciphertext is written to.
@param tag Pointer to `TAG_LEN` bytes of memory where the tag is written to.
  The length of the `tag` must be of a suitable length for the chosen algorithm:
  * `Spec_Agile_AEAD_AES128_GCM` (TAG_LEN=16)
  * `Spec_Agile_AEAD_AES256_GCM` (TAG_LEN=16)
  * `Spec_Agile_AEAD_CHACHA20_POLY1305` (TAG_LEN=16)

@return `EverCrypt_AEAD_encrypt` may return either `EverCrypt_Error_Success` or `EverCrypt_Error_InvalidKey` (`EverCrypt_error.h`). The latter is returned if and only if the `s` parameter is `NULL`.
*/
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

/**
Verify the authenticity of `ad` || `cipher` and decrypt `cipher` into `dst`.

@param s Pointer to the The AEAD state created by `EverCrypt_AEAD_create_in`. It already contains the encryption key.
@param iv Pointer to `iv_len` bytes of memory where the nonce is read from.
@param iv_len Length of the nonce. Note: ChaCha20Poly1305 requires a 12 byte nonce.
@param ad Pointer to `ad_len` bytes of memory where the associated data is read from.
@param ad_len Length of the associated data.
@param cipher Pointer to `cipher_len` bytes of memory where the ciphertext is read from.
@param cipher_len Length of the ciphertext.
@param tag Pointer to `TAG_LEN` bytes of memory where the tag is read from.
  The length of the `tag` must be of a suitable length for the chosen algorithm:
  * `Spec_Agile_AEAD_AES128_GCM` (TAG_LEN=16)
  * `Spec_Agile_AEAD_AES256_GCM` (TAG_LEN=16)
  * `Spec_Agile_AEAD_CHACHA20_POLY1305` (TAG_LEN=16)
@param dst Pointer to `cipher_len` bytes of memory where the decrypted plaintext will be written to.

@return `EverCrypt_AEAD_decrypt` returns ...

  * `EverCrypt_Error_Success`

  ... on success and either of ...

  * `EverCrypt_Error_InvalidKey` (returned if and only if the `s` parameter is `NULL`),
  * `EverCrypt_Error_InvalidIVLength` (see note about requirements on IV size above), or
  * `EverCrypt_Error_AuthenticationFailure` (in case the ciphertext could not be authenticated, e.g., due to modifications)

  ... on failure (`EverCrypt_error.h`).

  Upon success, the plaintext will be written into `dst`.
*/
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

/**
Expand pseudorandom key to desired length.

@param a Hash function to use. Usually, the same as used in `EverCrypt_HKDF_extract`.
@param okm Pointer to `len` bytes of memory where output keying material is written to.
@param prk Pointer to at least `HashLen` bytes of memory where pseudorandom key is read from. Usually, this points to the output from the extract step.
@param prklen Length of pseudorandom key.
@param info Pointer to `infolen` bytes of memory where context and application specific information is read from.
@param infolen Length of context and application specific information. Can be 0.
@param len Length of output keying material.
*/
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

/**
Extract a fixed-length pseudorandom key from input keying material.

@param a Hash function to use. The allowed values are:
  * `Spec_Hash_Definitions_Blake2B` (`HashLen` = 64), 
  * `Spec_Hash_Definitions_Blake2S` (`HashLen` = 32), 
  * `Spec_Hash_Definitions_SHA2_256` (`HashLen` = 32), 
  * `Spec_Hash_Definitions_SHA2_384` (`HashLen` = 48), 
  * `Spec_Hash_Definitions_SHA2_512` (`HashLen` = 64), and
  * `Spec_Hash_Definitions_SHA1` (`HashLen` = 20).
@param prk Pointer to `HashLen` bytes of memory where pseudorandom key is written to.
  `HashLen` depends on the used algorithm `a`. See above.
@param salt Pointer to `saltlen` bytes of memory where salt value is read from.
@param saltlen Length of salt value.
@param ikm Pointer to `ikmlen` bytes of memory where input keying material is read from.
@param ikmlen Length of input keying material.
*/
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
