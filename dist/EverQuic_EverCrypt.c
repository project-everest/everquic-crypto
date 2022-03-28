

#include "internal/EverQuic_EverCrypt.h"



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

typedef struct EverCrypt_CTR_state_s_s
{
  Spec_Cipher_Expansion_impl i;
  uint8_t *iv;
  uint32_t iv_len;
  uint8_t *xkey;
  uint32_t ctr;
}
EverCrypt_CTR_state_s;

typedef struct EverCrypt_AEAD_state_s_s
{
  Spec_Cipher_Expansion_impl impl;
  uint8_t *ek;
}
EverCrypt_AEAD_state_s;

