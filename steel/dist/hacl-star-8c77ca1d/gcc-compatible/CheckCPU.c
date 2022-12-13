#include "EverCrypt_AutoConfig2.h"

int main() {
  EverCrypt_AutoConfig2_init();
  bool has_avx2 = EverCrypt_AutoConfig2_has_avx2();
  bool has_aesni = EverCrypt_AutoConfig2_has_aesni();
  printf(">>>>>>>>>>>>>>>>>Has AVX2=%d, Has AES-NI=%d<<<<<<<<<<<<<<<<<<\n", has_avx2, has_aesni);
}



    
/* cc  -fPIC -I. -I /home/nswamy/everest/karamel/include -I /home/nswamy/everest/karamel/krmllib/dist/minimal -Wall -Wextra -Werror -std=c11 -Wno-unused-variable -Wno-unknown-warning-option -Wno-unused-but-set-variable -Wno-unused-function -Wno-unused-parameter -Wno-infinite-recursion -g -fwrapv -D_BSD_SOURCE -D_DEFAULT_SOURCE -fPIC -Wno-unused -Wno-parentheses -Wno-deprecated-declarations -Wno-#warnings -Wno-error=cpp -Wno-cpp -g -std=gnu11 -O3 -c  CheckCPU.exe CheckCPU.c */
