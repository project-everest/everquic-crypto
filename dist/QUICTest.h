

#ifndef __QUICTest_H
#define __QUICTest_H

#include "EverQuic_EverCrypt.h"
#include "EverQuic.h"
#include "krml/internal/target.h"
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include <stdint.h>
#include <stdbool.h>
#include <string.h>

extern EverQuic_index QUICTest_idx;

bool QUICTest_is_success_body(EverCrypt_Error_error_code e);

bool QUICTest_check_is_true_body(bool e);

extern bool QUICTest_is_equal(uint8_t *b1, uint8_t *b2, uint32_t len);

exit_code QUICTest_test(void);


#define __QUICTest_H_DEFINED
#endif
