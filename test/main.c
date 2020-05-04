#include <stdio.h>
#include <stdlib.h>

#include "EverQuic.h"
#include "QUICTest.h"

bool QUICTest_is_equal (uint8_t * b1, uint8_t * b2, uint32_t len) {
  return (memcmp(b1, b2, len) == 0);
}

int main () {
  QUICTest_test ();
  return EXIT_SUCCESS;
}
