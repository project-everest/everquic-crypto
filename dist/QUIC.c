

#include "QUIC.h"

Prims_int QUIC_cipher_keysize(Spec_Agile_AEAD_alg a)
{
  return Spec_Agile_Cipher_key_length(Spec_Agile_AEAD_cipher_alg_of_supported_alg(a));
}

static EverQuic_index iid(EverQuic_index i)
{
  return i;
}

typedef EverQuic_state_s *raise;

static EverQuic_state_s *istate(EverQuic_index i, EverQuic_state_s *s)
{
  EverQuic_index x0 = iid(i);
  return s;
}

EverCrypt_Error_error_code
QUIC_encrypt(
  EverQuic_index i,
  EverQuic_state_s *s,
  uint8_t *dst,
  uint64_t *dst_pn,
  EverQuic_header h,
  uint8_t *plain,
  uint32_t plain_len
)
{
  EverQuic_state_s *s1 = istate(i, s);
  return EverQuic_encrypt(s1, dst, dst_pn, h, plain, plain_len);
}

EverCrypt_Error_error_code
QUIC_decrypt(
  EverQuic_state_s *uu___1,
  EverQuic_result *uu___2,
  uint8_t *uu___3,
  uint32_t uu___4,
  uint8_t uu___5
)
{
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n", __FILE__, __LINE__, "");
  KRML_HOST_EXIT(255U);
}

