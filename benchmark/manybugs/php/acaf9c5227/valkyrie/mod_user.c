/*
   +----------------------------------------------------------------------+
   | PHP Version 5                                                        |
   +----------------------------------------------------------------------+
   | Copyright (c) 1997-2012 The PHP Group                                |
   +----------------------------------------------------------------------+
   | This source file is subject to version 3.01 of the PHP license,      |
   | that is bundled with this package in the file LICENSE, and is        |
   | available through the world-wide-web at the following url:           |
   | http://www.php.net/license/3_01.txt                                  |
   | If you did not receive a copy of the PHP license and are unable to   |
   | obtain it through the world-wide-web, please send a note to          |
   | license@php.net so we can mail you a copy immediately.               |
   +----------------------------------------------------------------------+
   | Author: Sascha Schumann <sascha@schumann.cx>                         |
   +----------------------------------------------------------------------+
 */

/* $Id$ */

#include "mod_user.h"
#include "php.h"
#include "php_session.h"

ps_module ps_mod_user = {PS_MOD(user)};

#define SESS_ZVAL_LONG(val, a)                                                 \
  {                                                                            \
    MAKE_STD_ZVAL(a);                                                          \
    ZVAL_LONG(a, val);                                                         \
  }

#define SESS_ZVAL_STRING(vl, a)                                                \
  {                                                                            \
    char *__vl = vl;                                                           \
    SESS_ZVAL_STRINGN(__vl, strlen(__vl), a);                                  \
  }

#define SESS_ZVAL_STRINGN(vl, ln, a)                                           \
  {                                                                            \
    MAKE_STD_ZVAL(a);                                                          \
    ZVAL_STRINGL(a, vl, ln, 1);                                                \
  }

static zval *ps_call_handler(zval *func, int argc, zval **argv TSRMLS_DC) {
  int i;
  zval *retval = NULL;

  MAKE_STD_ZVAL(retval);
 /* jump:54 */  if (call_user_function(EG(function_table), NULL, func, retval, argc,
                         argv TSRMLS_CC) == FAILURE) {
    zval_ptr_dtor(&retval);
    retval = NULL;
  }

 /* jump:58 */  for (i = 0; i < argc; i++) {
    zval_ptr_dtor(&argv[i]);
  }

  return retval;
}

#define STDVARS                                                                \
  zval *retval;                                                                \
  int ret = FAILURE

#define PSF(a) PS(mod_user_names).name.ps_##a

#define FINISH                                                                 \
  if (retval) {                                                                \
    convert_to_long(retval);                                                   \
    ret = Z_LVAL_P(retval);                                                    \
    zval_ptr_dtor(&retval);                                                    \
  }                                                                            \
  return ret

PS_OPEN_FUNC(user) {
  zval *args[2];
  STDVARS;

  SESS_ZVAL_STRING((char *)save_path, args[0]);
  SESS_ZVAL_STRING((char *)session_name, args[1]);

  retval = ps_call_handler(PSF(open), 2, args TSRMLS_CC);
  PS(mod_user_implemented) = 1;

  FINISH;
}

PS_CLOSE_FUNC(user) {
  STDVARS;

 /* jump:96 */  if (!PS(mod_user_implemented)) {
    /* already closed */
    return SUCCESS;
  }

  retval = ps_call_handler(PSF(close), 0, NULL TSRMLS_CC);
  PS(mod_user_implemented) = 0;

  FINISH;
}

PS_READ_FUNC(user) {
  zval *args[1];
  STDVARS;

  SESS_ZVAL_STRING((char *)key, args[0]);

  retval = ps_call_handler(PSF(read), 1, args TSRMLS_CC);

 /* jump:119 */  if (retval) {
 /* jump:117 */    if (Z_TYPE_P(retval) == IS_STRING) {
      *val = estrndup(Z_STRVAL_P(retval), Z_STRLEN_P(retval));
      *vallen = Z_STRLEN_P(retval);
      ret = SUCCESS;
    }
    zval_ptr_dtor(&retval);
  }

  return ret;
}

PS_WRITE_FUNC(user) {
  zval *args[2];
  STDVARS;

  SESS_ZVAL_STRING((char *)key, args[0]);
  SESS_ZVAL_STRINGN((char *)val, vallen, args[1]);

  retval = ps_call_handler(PSF(write), 2, args TSRMLS_CC);

  FINISH;
}

PS_DESTROY_FUNC(user) {
  zval *args[1];
  STDVARS;

  SESS_ZVAL_STRING((char *)key, args[0]);

  retval = ps_call_handler(PSF(destroy), 1, args TSRMLS_CC);

  FINISH;
}

PS_GC_FUNC(user) {
  zval *args[1];
  STDVARS;

  SESS_ZVAL_LONG(maxlifetime, args[0]);

  retval = ps_call_handler(PSF(gc), 1, args TSRMLS_CC);

  FINISH;
}

/*
 * Local variables:
 * tab-width: 4
 * c-basic-offset: 4
 * End:
 * vim600: sw=4 ts=4 fdm=marker
 * vim<600: sw=4 ts=4
 */
