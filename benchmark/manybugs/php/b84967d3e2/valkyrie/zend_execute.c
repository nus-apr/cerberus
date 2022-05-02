/*
   +----------------------------------------------------------------------+
   | Zend Engine                                                          |
   +----------------------------------------------------------------------+
   | Copyright (c) 1998-2011 Zend Technologies Ltd. (http://www.zend.com) |
   +----------------------------------------------------------------------+
   | This source file is subject to version 2.00 of the Zend license,     |
   | that is bundled with this package in the file LICENSE, and is        |
   | available through the world-wide-web at the following url:           |
   | http://www.zend.com/license/2_00.txt.                                |
   | If you did not receive a copy of the Zend license and are unable to  |
   | obtain it through the world-wide-web, please send a note to          |
   | license@zend.com so we can mail you a copy immediately.              |
   +----------------------------------------------------------------------+
   | Authors: Andi Gutmans <andi@zend.com>                                |
   |          Zeev Suraski <zeev@zend.com>                                |
   +----------------------------------------------------------------------+
*/

/* $Id$ */

#define ZEND_INTENSIVE_DEBUGGING 0

#include <signal.h>
#include <stdio.h>

#include "zend.h"
#include "zend_API.h"
#include "zend_closures.h"
#include "zend_compile.h"
#include "zend_constants.h"
 /* jump:34 */#include "zend_dtrace.h"
#include "zend_exceptions.h"
#include "zend_execute.h"
#include "zend_extensions.h"
#include "zend_ini.h"
#include "zend_interfaces.h"
#include "zend_ptr_stack.h"
#include "zend_vm.h"

/* Virtual current working directory support */
 /* jump:44 */#include "tsrm_virtual_cwd.h"

#define _CONST_CODE 0
#define _TMP_CODE 1
#define _VAR_CODE 2
#define _UNUSED_CODE 3
#define _CV_CODE 4

typedef int (*incdec_t)(zval *);

#define get_zval_ptr(op_type, node, Ts, should_free, type)                     \
  _get_zval_ptr(op_type, node, Ts, should_free, type TSRMLS_CC)
#define get_zval_ptr_ptr(op_type, node, Ts, should_free, type)                 \
  _get_zval_ptr_ptr(op_type, node, Ts, should_free, type TSRMLS_CC)
#define get_obj_zval_ptr(op_type, node, Ts, should_free, type)                 \
  _get_obj_zval_ptr(op_type, node, Ts, should_free, type TSRMLS_CC)
#define get_obj_zval_ptr_ptr(op_type, node, Ts, should_free, type)             \
  _get_obj_zval_ptr_ptr(op_type, node, Ts, should_free, type TSRMLS_CC)

/* Prototypes */
static void zend_extension_statement_handler(const zend_extension *extension,
                                             zend_op_array *op_array TSRMLS_DC);
static void
zend_extension_fcall_begin_handler(const zend_extension *extension,
 /* jump:68 */                                   zend_op_array *op_array TSRMLS_DC);
static void zend_extension_fcall_end_handler(const zend_extension *extension,
                                             zend_op_array *op_array TSRMLS_DC);

#define RETURN_VALUE_USED(opline) (!((opline)->result_type & EXT_TYPE_UNUSED))

#define T(offset) (*(temp_variable *)((char *)Ts + offset))
#define CV(var) CVs[var]

#define TEMP_VAR_STACK_LIMIT 2000

static zend_always_inline void zend_pzval_unlock_func(zval *z,
                                                      zend_free_op *should_free,
 /* jump:81 */                                                      int unref TSRMLS_DC) {
 /* jump:85 */  if (!Z_DELREF_P(z)) {
    Z_SET_REFCOUNT_P(z, 1);
 /* jump:90 */    Z_UNSET_ISREF_P(z);
    should_free->var = z;
    /*		should_free->is_var = 1; */
 /* jump:89 */  } else {
    should_free->var = 0;
 /* jump:89 */    if (unref && Z_ISREF_P(z) && Z_REFCOUNT_P(z) == 1) {
      Z_UNSET_ISREF_P(z);
    }
    GC_ZVAL_CHECK_POSSIBLE_ROOT(z);
  }
}
 /* jump:95 */
static zend_always_inline void zend_pzval_unlock_free_func(zval *z TSRMLS_DC) {
 /* jump:101 */  if (!Z_DELREF_P(z)) {
 /* jump:100 */    if (z != &EG(uninitialized_zval)) {
      GC_REMOVE_ZVAL_FROM_BUFFER(z);
      zval_dtor(z);
      efree(z);
    }
  }
}

#undef zval_ptr_dtor
#define zval_ptr_dtor(pzv) i_zval_ptr_dtor(*(pzv)ZEND_FILE_LINE_CC)

#define PZVAL_UNLOCK(z, f) zend_pzval_unlock_func(z, f, 1 TSRMLS_CC)
#define PZVAL_UNLOCK_EX(z, f, u) zend_pzval_unlock_func(z, f, u TSRMLS_CC)
 /* jump:111 */#define PZVAL_UNLOCK_FREE(z) zend_pzval_unlock_free_func(z TSRMLS_CC)
#define PZVAL_LOCK(z) Z_ADDREF_P((z))
#define SELECTIVE_PZVAL_LOCK(pzv, opline)                                      \
  if (RETURN_VALUE_USED(opline)) {                                             \
 /* jump:115 */    PZVAL_LOCK(pzv);                                                           \
  }
 /* jump:118 */
#define EXTRACT_ZVAL_PTR(t)                                                    \
  do {                                                                         \
 /* jump:121 */    temp_variable *__t = (t);                                                  \
    if (__t->var.ptr_ptr) {                                                    \
      __t->var.ptr = *__t->var.ptr_ptr;                                        \
 /* jump:123 */      __t->var.ptr_ptr = &__t->var.ptr;                                        \
      if (!PZVAL_IS_REF(__t->var.ptr) && Z_REFCOUNT_P(__t->var.ptr) > 2) {     \
        SEPARATE_ZVAL(__t->var.ptr_ptr);                                       \
      }                                                                        \
 /* jump:174 */    }                                                                          \
  } while (0)

 /* jump:131 */#define AI_SET_PTR(t, val)                                                     \
 /* jump:148 */  do {                                                                         \
    temp_variable *__t = (t);                                                  \
    __t->var.ptr = (val);                                                      \
 /* jump:138 */    __t->var.ptr_ptr = &__t->var.ptr;                                          \
  } while (0)
 /* jump:137 */
#define FREE_OP(should_free)                                                   \
  if (should_free.var) {                                                       \
    if ((zend_uintptr_t)should_free.var & 1L) {                                \
 /* jump:147 */      zval_dtor((zval *)((zend_uintptr_t)should_free.var & ~1L));              \
    } else {                                                                   \
 /* jump:146 */      zval_ptr_dtor(&should_free.var);                                         \
 /* jump:161 */    }                                                                          \
  }
 /* jump:145 */
#define FREE_OP_IF_VAR(should_free)                                            \
 /* jump:158 */  if (should_free.var != NULL &&                                               \
 /* jump:148 */      (((zend_uintptr_t)should_free.var & 1L) == 0)) {                         \
    zval_ptr_dtor(&should_free.var);                                           \
 /* jump:157 */  }

#define FREE_OP_VAR_PTR(should_free)                                           \
 /* jump:153 */  if (should_free.var) {                                                       \
    zval_ptr_dtor(&should_free.var);                                           \
  }
 /* jump:156 */
#define TMP_FREE(z) (zval *)(((zend_uintptr_t)(z)) | 1L)

#define IS_TMP_FREE(should_free) ((zend_uintptr_t)should_free.var & 1L)

#define MAKE_REAL_ZVAL_PTR(val)                                                \
  do {                                                                         \
    zval *_tmp;                                                                \
    ALLOC_ZVAL(_tmp);                                                          \
 /* jump:168 */    INIT_PZVAL_COPY(_tmp, (val));                                              \
 /* jump:167 */    (val) = _tmp;                                                              \
  } while (0)

/* End of zend_execute_locks.h */
 /* jump:173 */
 /* jump:171 */#define CV_OF(i) (EG(current_execute_data)->CVs[i])
#define CV_DEF_OF(i) (EG(active_op_array)->vars[i])

#define CTOR_CALL_BIT 0x1
#define CTOR_USED_BIT 0x2
 /* jump:186 */
#define IS_CTOR_CALL(ce) (((zend_uintptr_t)(ce)) & CTOR_CALL_BIT)
#define IS_CTOR_USED(ce) (((zend_uintptr_t)(ce)) & CTOR_USED_BIT)

#define ENCODE_CTOR(ce, used)                                                  \
  ((zend_class_entry *)(((zend_uintptr_t)(ce)) | CTOR_CALL_BIT |               \
 /* jump:182 */                        ((used) ? CTOR_USED_BIT : 0)))
#define DECODE_CTOR(ce)                                                        \
 /* jump:185 */  ((zend_class_entry *)(((zend_uintptr_t)(ce)) &                               \
                        ~(CTOR_CALL_BIT | CTOR_USED_BIT)))

ZEND_API zval **
zend_get_compiled_variable_value(const zend_execute_data *execute_data_ptr,
                                 zend_uint var) {
  return execute_data_ptr->CVs[var];
}
 /* jump:197 */
 /* jump:193 */static zend_always_inline zval *
_get_zval_ptr_tmp(zend_uint var, const temp_variable *Ts,
                  zend_free_op *should_free TSRMLS_DC) {
 /* jump:196 */  return should_free->var = &T(var).tmp_var;
}

static zend_always_inline zval *
_get_zval_ptr_var(zend_uint var, const temp_variable *Ts,
 /* jump:217 */                  zend_free_op *should_free TSRMLS_DC) {
 /* jump:210 */  zval *ptr = T(var).var.ptr;
 /* jump:205 */
  PZVAL_UNLOCK(ptr, should_free);
 /* jump:209 */  return ptr;
 /* jump:206 */}

static zend_never_inline zval **_get_zval_cv_lookup(zval ***ptr, zend_uint var,
                                                    int type TSRMLS_DC) {
  zend_compiled_variable *cv = &CV_DEF_OF(var);

 /* jump:237 */  if (!EG(active_symbol_table) ||
      zend_hash_quick_find(EG(active_symbol_table), cv->name, cv->name_len + 1,
 /* jump:214 */                           cv->hash_value, (void **)ptr) == FAILURE) {
    switch (type) {
    case BP_VAR_R:
    case BP_VAR_UNSET:
      zend_error(E_NOTICE, "Undefined variable: %s", cv->name);
      /* break missing intentionally */
 /* jump:220 */    case BP_VAR_IS:
      return &EG(uninitialized_zval_ptr);
      break;
    case BP_VAR_RW:
      zend_error(E_NOTICE, "Undefined variable: %s", cv->name);
      /* break missing intentionally */
    case BP_VAR_W:
      Z_ADDREF(EG(uninitialized_zval));
 /* jump:230 */      if (!EG(active_symbol_table)) {
        *ptr = (zval **)EG(current_execute_data)->CVs +
               (EG(active_op_array)->last_var + var);
        **ptr = &EG(uninitialized_zval);
      } else {
        zend_hash_quick_update(
 /* jump:234 */            EG(active_symbol_table), cv->name, cv->name_len + 1, cv->hash_value,
            &EG(uninitialized_zval_ptr), sizeof(zval *), (void **)ptr);
      }
 /* jump:239 */      break;
 /* jump:238 */    }
  }
  return *ptr;
}

static zend_never_inline zval **
 /* jump:254 */_get_zval_cv_lookup_BP_VAR_R(zval ***ptr, zend_uint var TSRMLS_DC) {
 /* jump:247 */  zend_compiled_variable *cv = &CV_DEF_OF(var);
 /* jump:246 */
 /* jump:250 */  if (!EG(active_symbol_table) ||
      zend_hash_quick_find(EG(active_symbol_table), cv->name, cv->name_len + 1,
                           cv->hash_value, (void **)ptr) == FAILURE) {
    zend_error(E_NOTICE, "Undefined variable: %s", cv->name);
 /* jump:251 */    return &EG(uninitialized_zval_ptr);
 /* jump:264 */  }
  return *ptr;
}
 /* jump:256 */
static zend_never_inline zval **
_get_zval_cv_lookup_BP_VAR_UNSET(zval ***ptr, zend_uint var TSRMLS_DC) {
  zend_compiled_variable *cv = &CV_DEF_OF(var);

 /* jump:263 */  if (!EG(active_symbol_table) ||
      zend_hash_quick_find(EG(active_symbol_table), cv->name, cv->name_len + 1,
                           cv->hash_value, (void **)ptr) == FAILURE) {
    zend_error(E_NOTICE, "Undefined variable: %s", cv->name);
    return &EG(uninitialized_zval_ptr);
 /* jump:265 */  }
  return *ptr;
}
 /* jump:275 */
 /* jump:271 */static zend_never_inline zval **
 /* jump:270 */_get_zval_cv_lookup_BP_VAR_IS(zval ***ptr, zend_uint var TSRMLS_DC) {
  zend_compiled_variable *cv = &CV_DEF_OF(var);

 /* jump:275 */  if (!EG(active_symbol_table) ||
      zend_hash_quick_find(EG(active_symbol_table), cv->name, cv->name_len + 1,
                           cv->hash_value, (void **)ptr) == FAILURE) {
 /* jump:279 */    return &EG(uninitialized_zval_ptr);
  }
  return *ptr;
}

static zend_never_inline zval **
_get_zval_cv_lookup_BP_VAR_RW(zval ***ptr, zend_uint var TSRMLS_DC) {
  zend_compiled_variable *cv = &CV_DEF_OF(var);

 /* jump:289 */  if (!EG(active_symbol_table)) {
    Z_ADDREF(EG(uninitialized_zval));
    *ptr = (zval **)EG(current_execute_data)->CVs +
 /* jump:291 */           (EG(active_op_array)->last_var + var);
    **ptr = &EG(uninitialized_zval);
    zend_error(E_NOTICE, "Undefined variable: %s", cv->name);
 /* jump:297 */  } else if (zend_hash_quick_find(EG(active_symbol_table), cv->name,
                                  cv->name_len + 1, cv->hash_value,
                                  (void **)ptr) == FAILURE) {
    Z_ADDREF(EG(uninitialized_zval));
 /* jump:296 */    zend_hash_quick_update(EG(active_symbol_table), cv->name, cv->name_len + 1,
                           cv->hash_value, &EG(uninitialized_zval_ptr),
                           sizeof(zval *), (void **)ptr);
    zend_error(E_NOTICE, "Undefined variable: %s", cv->name);
  }
  return *ptr;
}

static zend_never_inline zval **
_get_zval_cv_lookup_BP_VAR_W(zval ***ptr, zend_uint var TSRMLS_DC) {
  zend_compiled_variable *cv = &CV_DEF_OF(var);

 /* jump:310 */  if (!EG(active_symbol_table)) {
    Z_ADDREF(EG(uninitialized_zval));
    *ptr = (zval **)EG(current_execute_data)->CVs +
           (EG(active_op_array)->last_var + var);
    **ptr = &EG(uninitialized_zval);
 /* jump:317 */  } else if (zend_hash_quick_find(EG(active_symbol_table), cv->name,
                                  cv->name_len + 1, cv->hash_value,
                                  (void **)ptr) == FAILURE) {
 /* jump:324 */    Z_ADDREF(EG(uninitialized_zval));
    zend_hash_quick_update(EG(active_symbol_table), cv->name, cv->name_len + 1,
                           cv->hash_value, &EG(uninitialized_zval_ptr),
 /* jump:322 */                           sizeof(zval *), (void **)ptr);
  }
  return *ptr;
}

static zend_always_inline zval *_get_zval_ptr_cv(zend_uint var,
                                                 int type TSRMLS_DC) {
  zval ***ptr = &CV_OF(var);

 /* jump:327 */  if (UNEXPECTED(*ptr == NULL)) {
    return *_get_zval_cv_lookup(ptr, var, type TSRMLS_CC);
  }
  return **ptr;
}

static zend_always_inline zval *
_get_zval_ptr_cv_BP_VAR_R(zval ***CVs, zend_uint var TSRMLS_DC) {
  zval ***ptr = &CV(var);

 /* jump:337 */  if (UNEXPECTED(*ptr == NULL)) {
 /* jump:340 */    return *_get_zval_cv_lookup_BP_VAR_R(ptr, var TSRMLS_CC);
  }
  return **ptr;
}

static zend_always_inline zval *
_get_zval_ptr_cv_BP_VAR_UNSET(zval ***CVs, zend_uint var TSRMLS_DC) {
  zval ***ptr = &CV(var);

 /* jump:347 */  if (UNEXPECTED(*ptr == NULL)) {
    return *_get_zval_cv_lookup_BP_VAR_UNSET(ptr, var TSRMLS_CC);
  }
  return **ptr;
 /* jump:351 */}
 /* jump:352 */
static zend_always_inline zval *
_get_zval_ptr_cv_BP_VAR_IS(zval ***CVs, zend_uint var TSRMLS_DC) {
  zval ***ptr = &CV(var);

 /* jump:357 */  if (UNEXPECTED(*ptr == NULL)) {
    return *_get_zval_cv_lookup_BP_VAR_IS(ptr, var TSRMLS_CC);
  }
  return **ptr;
}

static zend_always_inline zval *
_get_zval_ptr_cv_BP_VAR_RW(zval ***CVs, zend_uint var TSRMLS_DC) {
  zval ***ptr = &CV(var);

 /* jump:367 */  if (UNEXPECTED(*ptr == NULL)) {
    return *_get_zval_cv_lookup_BP_VAR_RW(ptr, var TSRMLS_CC);
  }
  return **ptr;
}

static zend_always_inline zval *
_get_zval_ptr_cv_BP_VAR_W(zval ***CVs, zend_uint var TSRMLS_DC) {
  zval ***ptr = &CV(var);

 /* jump:377 */  if (UNEXPECTED(*ptr == NULL)) {
    return *_get_zval_cv_lookup_BP_VAR_W(ptr, var TSRMLS_CC);
  }
  return **ptr;
 /* jump:381 */}

static inline zval *_get_zval_ptr(int op_type, const znode_op *node,
                                  const temp_variable *Ts,
 /* jump:393 */                                  zend_free_op *should_free,
                                  int type TSRMLS_DC) {
 /* jump:388 */  /*	should_free->is_var = 0; */
  switch (op_type) {
  case IS_CONST:
    should_free->var = 0;
 /* jump:391 */    return node->zv;
    break;
  case IS_TMP_VAR:
    should_free->var = TMP_FREE(&T(node->var).tmp_var);
    return &T(node->var).tmp_var;
    break;
  case IS_VAR:
    return _get_zval_ptr_var(node->var, Ts, should_free TSRMLS_CC);
    break;
  case IS_UNUSED:
    should_free->var = 0;
    return NULL;
    break;
 /* jump:425 */  case IS_CV:
    should_free->var = 0;
    return _get_zval_ptr_cv(node->var, type TSRMLS_CC);
    break;
    EMPTY_SWITCH_DEFAULT_CASE()
  }
  return NULL;
}
 /* jump:423 */
static zend_always_inline zval **
_get_zval_ptr_ptr_var(zend_uint var, const temp_variable *Ts,
                      zend_free_op *should_free TSRMLS_DC) {
  zval **ptr_ptr = T(var).var.ptr_ptr;

 /* jump:418 */  if (EXPECTED(ptr_ptr != NULL)) {
    PZVAL_UNLOCK(*ptr_ptr, should_free);
  } else {
    /* string offset */
    PZVAL_UNLOCK(T(var).str_offset.str, should_free);
  }
  return ptr_ptr;
}

static zend_always_inline zval **_get_zval_ptr_ptr_cv(zend_uint var,
                                                      int type TSRMLS_DC) {
  zval ***ptr = &CV_OF(var);

 /* jump:431 */  if (UNEXPECTED(*ptr == NULL)) {
    return _get_zval_cv_lookup(ptr, var, type TSRMLS_CC);
  }
  return *ptr;
}

static zend_always_inline zval **
_get_zval_ptr_ptr_cv_BP_VAR_R(zval ***CVs, zend_uint var TSRMLS_DC) {
  zval ***ptr = &CV(var);

 /* jump:441 */  if (UNEXPECTED(*ptr == NULL)) {
    return _get_zval_cv_lookup_BP_VAR_R(ptr, var TSRMLS_CC);
  }
  return *ptr;
}

static zend_always_inline zval **
_get_zval_ptr_ptr_cv_BP_VAR_UNSET(zval ***CVs, zend_uint var TSRMLS_DC) {
  zval ***ptr = &CV(var);

 /* jump:451 */  if (UNEXPECTED(*ptr == NULL)) {
    return _get_zval_cv_lookup_BP_VAR_UNSET(ptr, var TSRMLS_CC);
  }
  return *ptr;
}

static zend_always_inline zval **
_get_zval_ptr_ptr_cv_BP_VAR_IS(zval ***CVs, zend_uint var TSRMLS_DC) {
  zval ***ptr = &CV(var);

 /* jump:461 */  if (UNEXPECTED(*ptr == NULL)) {
    return _get_zval_cv_lookup_BP_VAR_IS(ptr, var TSRMLS_CC);
  }
  return *ptr;
 /* jump:472 */}

static zend_always_inline zval **
 /* jump:471 */_get_zval_ptr_ptr_cv_BP_VAR_RW(zval ***CVs, zend_uint var TSRMLS_DC) {
 /* jump:469 */  zval ***ptr = &CV(var);

 /* jump:471 */  if (UNEXPECTED(*ptr == NULL)) {
    return _get_zval_cv_lookup_BP_VAR_RW(ptr, var TSRMLS_CC);
  }
  return *ptr;
}

static zend_always_inline zval **
_get_zval_ptr_ptr_cv_BP_VAR_W(zval ***CVs, zend_uint var TSRMLS_DC) {
  zval ***ptr = &CV(var);
 /* jump:480 */
 /* jump:481 */  if (UNEXPECTED(*ptr == NULL)) {
    return _get_zval_cv_lookup_BP_VAR_W(ptr, var TSRMLS_CC);
 /* jump:565 */  }
  return *ptr;
}

static inline zval **_get_zval_ptr_ptr(int op_type, const znode_op *node,
 /* jump:513 */                                       const temp_variable *Ts,
                                       zend_free_op *should_free,
                                       int type TSRMLS_DC) {
 /* jump:492 */  if (op_type == IS_CV) {
    should_free->var = 0;
    return _get_zval_ptr_ptr_cv(node->var, type TSRMLS_CC);
 /* jump:494 */  } else if (op_type == IS_VAR) {
    return _get_zval_ptr_ptr_var(node->var, Ts, should_free TSRMLS_CC);
  } else {
    should_free->var = 0;
    return NULL;
 /* jump:500 */  }
}

 /* jump:509 */static zend_always_inline zval *_get_obj_zval_ptr_unused(TSRMLS_D) {
 /* jump:508 */  if (EXPECTED(EG(This) != NULL)) {
    return EG(This);
  } else {
    zend_error_noreturn(E_ERROR, "Using $this when not in object context");
    return NULL;
  }
}

static inline zval **_get_obj_zval_ptr_ptr(int op_type, const znode_op *op,
                                           const temp_variable *Ts,
                                           zend_free_op *should_free,
                                           int type TSRMLS_DC) {
 /* jump:522 */  if (op_type == IS_UNUSED) {
 /* jump:519 */    if (EXPECTED(EG(This) != NULL)) {
      /* this should actually never be modified, _ptr_ptr is modified only when
         the object is empty */
      should_free->var = 0;
 /* jump:528 */      return &EG(This);
 /* jump:522 */    } else {
      zend_error_noreturn(E_ERROR, "Using $this when not in object context");
    }
  }
  return get_zval_ptr_ptr(op_type, op, Ts, should_free, type);
}

static zend_always_inline zval **_get_obj_zval_ptr_ptr_unused(TSRMLS_D) {
 /* jump:529 */  if (EXPECTED(EG(This) != NULL)) {
    return &EG(This);
  } else {
    zend_error_noreturn(E_ERROR, "Using $this when not in object context");
    return NULL;
  }
}
 /* jump:544 */
 /* jump:542 */static inline zval *_get_obj_zval_ptr(int op_type, znode_op *op,
 /* jump:538 */                                      const temp_variable *Ts,
                                      zend_free_op *should_free,
                                      int type TSRMLS_DC) {
 /* jump:541 */  if (op_type == IS_UNUSED) {
 /* jump:543 */    if (EXPECTED(EG(This) != NULL)) {
      should_free->var = 0;
      return EG(This);
    } else {
      zend_error_noreturn(E_ERROR, "Using $this when not in object context");
    }
  }
  return get_zval_ptr(op_type, op, Ts, should_free, type);
}

static void zend_assign_to_variable_reference(zval **variable_ptr_ptr,
                                              zval **value_ptr_ptr TSRMLS_DC) {
  zval *variable_ptr = *variable_ptr_ptr;
  zval *value_ptr = *value_ptr_ptr;
 /* jump:560 */
 /* jump:557 */  if (variable_ptr == &EG(error_zval) || value_ptr == &EG(error_zval)) {
 /* jump:558 */    variable_ptr_ptr = &EG(uninitialized_zval_ptr);
 /* jump:575 */  } else if (variable_ptr != value_ptr) {
 /* jump:569 */    if (!PZVAL_IS_REF(value_ptr)) {
      /* break it away */
      Z_DELREF_P(value_ptr);
 /* jump:566 */      if (Z_REFCOUNT_P(value_ptr) > 0) {
        ALLOC_ZVAL(*value_ptr_ptr);
        ZVAL_COPY_VALUE(*value_ptr_ptr, value_ptr);
        value_ptr = *value_ptr_ptr;
        zendi_zval_copy_ctor(*value_ptr);
      }
      Z_SET_REFCOUNT_P(value_ptr, 1);
      Z_SET_ISREF_P(value_ptr);
    }

    *variable_ptr_ptr = value_ptr;
    Z_ADDREF_P(value_ptr);

    zval_ptr_dtor(&variable_ptr);
 /* jump:589 */  } else if (!Z_ISREF_P(variable_ptr)) {
 /* jump:588 */    if (variable_ptr_ptr == value_ptr_ptr) {
 /* jump:581 */      SEPARATE_ZVAL(variable_ptr_ptr);
 /* jump:587 */    } else if (variable_ptr == &EG(uninitialized_zval) ||
               Z_REFCOUNT_P(variable_ptr) > 2) {
      /* we need to separate */
      Z_SET_REFCOUNT_P(variable_ptr, Z_REFCOUNT_P(variable_ptr) - 2);
 /* jump:587 */      ALLOC_ZVAL(*variable_ptr_ptr);
      ZVAL_COPY_VALUE(*variable_ptr_ptr, variable_ptr);
      zval_copy_ctor(*variable_ptr_ptr);
      *value_ptr_ptr = *variable_ptr_ptr;
      Z_SET_REFCOUNT_PP(variable_ptr_ptr, 2);
    }
    Z_SET_ISREF_PP(variable_ptr_ptr);
 /* jump:601 */  }
}

/* this should modify object only if it's empty */
 /* jump:596 */static inline void make_real_object(zval **object_ptr TSRMLS_DC) {
 /* jump:602 */  if (Z_TYPE_PP(object_ptr) == IS_NULL ||
      (Z_TYPE_PP(object_ptr) == IS_BOOL && Z_LVAL_PP(object_ptr) == 0) ||
      (Z_TYPE_PP(object_ptr) == IS_STRING && Z_STRLEN_PP(object_ptr) == 0)) {
    zend_error(E_WARNING, "Creating default object from empty value");

    SEPARATE_ZVAL_IF_NOT_REF(object_ptr);
    zval_dtor(*object_ptr);
    object_init(*object_ptr);
  }
 /* jump:611 */}

ZEND_API char *zend_verify_arg_class_kind(const zend_arg_info *cur_arg_info,
                                          ulong fetch_type,
                                          const char **class_name,
                                          zend_class_entry **pce TSRMLS_DC) {
  *pce = zend_fetch_class(
      cur_arg_info->class_name, cur_arg_info->class_name_len,
      (fetch_type | ZEND_FETCH_CLASS_AUTO | ZEND_FETCH_CLASS_NO_AUTOLOAD)
          TSRMLS_CC);

  *class_name = (*pce) ? (*pce)->name : cur_arg_info->class_name;
 /* jump:617 */  if (*pce && (*pce)->ce_flags & ZEND_ACC_INTERFACE) {
    return "implement interface ";
 /* jump:646 */  } else {
    return "be an instance of ";
  }
}

ZEND_API int zend_verify_arg_error(int error_type, const zend_function *zf,
                                   zend_uint arg_num, const char *need_msg,
                                   const char *need_kind, const char *given_msg,
 /* jump:634 */                                   char *given_kind TSRMLS_DC) {
  zend_execute_data *ptr = EG(current_execute_data)->prev_execute_data;
  char *fname = zf->common.function_name;
  char *fsep;
  const char *fclass;
 /* jump:633 */
 /* jump:634 */  if (zf->common.scope) {
    fsep = "::";
    fclass = zf->common.scope->name;
  } else {
    fsep = "";
 /* jump:639 */    fclass = "";
  }

 /* jump:645 */  if (ptr && ptr->op_array) {
    zend_error(error_type,
               "Argument %d passed to %s%s%s() must %s%s, %s%s given, called "
               "in %s on line %d and defined",
 /* jump:645 */               arg_num, fclass, fsep, fname, need_msg, need_kind, given_msg,
               given_kind, ptr->op_array->filename, ptr->opline->lineno);
  } else {
 /* jump:683 */    zend_error(error_type,
               "Argument %d passed to %s%s%s() must %s%s, %s%s given", arg_num,
               fclass, fsep, fname, need_msg, need_kind, given_msg, given_kind);
  }
  return 0;
 /* jump:658 */}

static inline int zend_verify_arg_type(zend_function *zf, zend_uint arg_num,
                                       zval *arg, ulong fetch_type TSRMLS_DC) {
  zend_arg_info *cur_arg_info;
  char *need_msg;
  zend_class_entry *ce;

 /* jump:661 */  if (!zf->common.arg_info || arg_num > zf->common.num_args) {
 /* jump:664 */    return 1;
 /* jump:663 */  }

  cur_arg_info = &zf->common.arg_info[arg_num - 1];

 /* jump:689 */  if (cur_arg_info->class_name) {
    const char *class_name;

 /* jump:673 */    if (!arg) {
      need_msg = zend_verify_arg_class_kind(cur_arg_info, fetch_type,
                                            &class_name, &ce TSRMLS_CC);
 /* jump:681 */      return zend_verify_arg_error(E_RECOVERABLE_ERROR, zf, arg_num, need_msg,
 /* jump:675 */                                   class_name, "none", "" TSRMLS_CC);
    }
 /* jump:682 */    if (Z_TYPE_P(arg) == IS_OBJECT) {
      need_msg = zend_verify_arg_class_kind(cur_arg_info, fetch_type,
                                            &class_name, &ce TSRMLS_CC);
 /* jump:681 */      if (!ce || !instanceof_function(Z_OBJCE_P(arg), ce TSRMLS_CC)) {
        return zend_verify_arg_error(E_RECOVERABLE_ERROR, zf, arg_num, need_msg,
                                     class_name, "instance of ",
                                     Z_OBJCE_P(arg)->name TSRMLS_CC);
      }
 /* jump:688 */    } else if (Z_TYPE_P(arg) != IS_NULL || !cur_arg_info->allow_null) {
      need_msg = zend_verify_arg_class_kind(cur_arg_info, fetch_type,
                                            &class_name, &ce TSRMLS_CC);
      return zend_verify_arg_error(E_RECOVERABLE_ERROR, zf, arg_num, need_msg,
                                   class_name, zend_zval_type_name(arg),
                                   "" TSRMLS_CC);
 /* jump:690 */    }
 /* jump:702 */  } else if (cur_arg_info->type_hint && cur_arg_info->type_hint == IS_ARRAY) {
 /* jump:694 */    if (!arg) {
      return zend_verify_arg_error(E_RECOVERABLE_ERROR, zf, arg_num,
                                   "be of the type array", "", "none",
                                   "" TSRMLS_CC);
 /* jump:696 */    }

 /* jump:701 */    if (Z_TYPE_P(arg) != IS_ARRAY &&
        (Z_TYPE_P(arg) != IS_NULL || !cur_arg_info->allow_null)) {
      return zend_verify_arg_error(E_RECOVERABLE_ERROR, zf, arg_num,
 /* jump:701 */                                   "be of the type array", "",
                                   zend_zval_type_name(arg), "" TSRMLS_CC);
    }
  }
  return 1;
}

static inline void zend_assign_to_object(zval **retval, zval **object_ptr,
                                         zval *property_name, int value_type,
                                         znode_op *value_op,
                                         const temp_variable *Ts, int opcode,
                                         const zend_literal *key TSRMLS_DC) {
  zval *object = *object_ptr;
 /* jump:727 */  zend_free_op free_value;
 /* jump:723 */  zval *value = get_zval_ptr(value_type, value_op, Ts, &free_value, BP_VAR_R);
 /* jump:721 */
 /* jump:717 */  if (Z_TYPE_P(object) != IS_OBJECT) {
 /* jump:723 */    if (object == &EG(error_zval)) {
 /* jump:720 */      if (retval) {
 /* jump:720 */        *retval = &EG(uninitialized_zval);
        PZVAL_LOCK(*retval);
      }
      FREE_OP(free_value);
      return;
    }
 /* jump:732 */    if (Z_TYPE_P(object) == IS_NULL ||
        (Z_TYPE_P(object) == IS_BOOL && Z_LVAL_P(object) == 0) ||
        (Z_TYPE_P(object) == IS_STRING && Z_STRLEN_P(object) == 0)) {
      SEPARATE_ZVAL_IF_NOT_REF(object_ptr);
      zval_dtor(*object_ptr);
      object_init(*object_ptr);
      object = *object_ptr;
      zend_error(E_WARNING, "Creating default object from empty value");
    } else {
      zend_error(E_WARNING, "Attempt to assign property of non-object");
 /* jump:740 */      if (retval) {
        *retval = &EG(uninitialized_zval);
 /* jump:738 */        PZVAL_LOCK(*retval);
      }
      FREE_OP(free_value);
      return;
    }
  }

  /* separate our value if necessary */
 /* jump:751 */  if (value_type == IS_TMP_VAR) {
    zval *orig_value = value;

    ALLOC_ZVAL(value);
    ZVAL_COPY_VALUE(value, orig_value);
    Z_UNSET_ISREF_P(value);
    Z_SET_REFCOUNT_P(value, 0);
 /* jump:759 */  } else if (value_type == IS_CONST) {
    zval *orig_value = value;

    ALLOC_ZVAL(value);
    ZVAL_COPY_VALUE(value, orig_value);
    Z_UNSET_ISREF_P(value);
    Z_SET_REFCOUNT_P(value, 0);
 /* jump:778 */    zval_copy_ctor(value);
 /* jump:777 */  }

  Z_ADDREF_P(value);
 /* jump:779 */  if (opcode == ZEND_ASSIGN_OBJ) {
 /* jump:776 */    if (!Z_OBJ_HT_P(object)->write_property) {
 /* jump:767 */      zend_error(E_WARNING, "Attempt to assign property of non-object");
 /* jump:768 */      if (retval) {
        *retval = &EG(uninitialized_zval);
        PZVAL_LOCK(&EG(uninitialized_zval));
      }
 /* jump:771 */      if (value_type == IS_TMP_VAR) {
        FREE_ZVAL(value);
 /* jump:773 */      } else if (value_type == IS_CONST) {
 /* jump:774 */        zval_ptr_dtor(&value);
      }
      FREE_OP(free_value);
      return;
    }
    Z_OBJ_HT_P(object)->write_property(object, property_name, value,
                                       key TSRMLS_CC);
  } else {
    /* Note:  property_name in this case is really the array index! */
 /* jump:783 */    if (!Z_OBJ_HT_P(object)->write_dimension) {
      zend_error_noreturn(E_ERROR, "Cannot use object as array");
    }
    Z_OBJ_HT_P(object)->write_dimension(object, property_name, value TSRMLS_CC);
  }

 /* jump:790 */  if (retval && !EG(exception)) {
    *retval = value;
    PZVAL_LOCK(value);
  }
  zval_ptr_dtor(&value);
  FREE_OP_IF_VAR(free_value);
}

static inline int zend_assign_to_string_offset(const temp_variable *T,
                                               const zval *value,
                                               int value_type TSRMLS_DC) {
 /* jump:852 */  if (Z_TYPE_P(T->str_offset.str) == IS_STRING) {
 /* jump:807 */
 /* jump:802 */    if (((int)T->str_offset.offset < 0)) {
      zend_error(E_WARNING, "Illegal string offset:  %d", T->str_offset.offset);
 /* jump:804 */      return 0;
    }

 /* jump:820 */    if (T->str_offset.offset >= Z_STRLEN_P(T->str_offset.str)) {
 /* jump:812 */      if (IS_INTERNED(Z_STRVAL_P(T->str_offset.str))) {
        char *tmp = (char *)emalloc(T->str_offset.offset + 1 + 1);

        memcpy(tmp, Z_STRVAL_P(T->str_offset.str),
               T->str_offset.offset + 1 + 1);
        Z_STRVAL_P(T->str_offset.str) = tmp;
      } else {
        Z_STRVAL_P(T->str_offset.str) = (char *)erealloc(
 /* jump:821 */            Z_STRVAL_P(T->str_offset.str), T->str_offset.offset + 1 + 1);
 /* jump:817 */      }
      memset(Z_STRVAL_P(T->str_offset.str) + Z_STRLEN_P(T->str_offset.str), ' ',
             T->str_offset.offset - Z_STRLEN_P(T->str_offset.str));
      Z_STRVAL_P(T->str_offset.str)[T->str_offset.offset + 1] = 0;
      Z_STRLEN_P(T->str_offset.str) = T->str_offset.offset + 1;
 /* jump:826 */    } else if (IS_INTERNED(Z_STRVAL_P(T->str_offset.str))) {
      char *tmp = (char *)emalloc(Z_STRLEN_P(T->str_offset.str) + 1);
 /* jump:825 */
      memcpy(tmp, Z_STRVAL_P(T->str_offset.str),
             Z_STRLEN_P(T->str_offset.str) + 1);
      Z_STRVAL_P(T->str_offset.str) = tmp;
    }

 /* jump:838 */    if (Z_TYPE_P(value) != IS_STRING) {
      zval tmp;

      ZVAL_COPY_VALUE(&tmp, value);
 /* jump:834 */      if (value_type != IS_TMP_VAR) {
        zval_copy_ctor(&tmp);
      }
      convert_to_string(&tmp);
      Z_STRVAL_P(T->str_offset.str)[T->str_offset.offset] = Z_STRVAL(tmp)[0];
      STR_FREE(Z_STRVAL(tmp));
    } else {
      Z_STRVAL_P(T->str_offset.str)
      [T->str_offset.offset] = Z_STRVAL_P(value)[0];
 /* jump:846 */      if (value_type == IS_TMP_VAR) {
        /* we can safely free final_value here
         * because separation is done only
         * in case value_type == IS_VAR */
        STR_FREE(Z_STRVAL_P(value));
 /* jump:848 */      }
    }
    /*
     * the value of an assignment to a string offset is undefined
 /* jump:875 */    T(result->u.var).var = &T->str_offset.str;
 /* jump:874 */    */
  }
 /* jump:857 */  return 1;
 /* jump:856 */}

static inline zval *zend_assign_tmp_to_variable(zval **variable_ptr_ptr,
                                                zval *value TSRMLS_DC) {
 /* jump:869 */  zval *variable_ptr = *variable_ptr_ptr;
 /* jump:862 */  zval garbage;

 /* jump:865 */  if (Z_TYPE_P(variable_ptr) == IS_OBJECT &&
      UNEXPECTED(Z_OBJ_HANDLER_P(variable_ptr, set) != NULL)) {
 /* jump:868 */    Z_OBJ_HANDLER_P(variable_ptr, set)(variable_ptr_ptr, value TSRMLS_CC);
    return variable_ptr;
  }

 /* jump:876 */  if (UNEXPECTED(Z_REFCOUNT_P(variable_ptr) > 1) &&
      EXPECTED(!PZVAL_IS_REF(variable_ptr))) {
 /* jump:871 */    /* we need to split */
    Z_DELREF_P(variable_ptr);
    GC_ZVAL_CHECK_POSSIBLE_ROOT(variable_ptr);
    ALLOC_ZVAL(variable_ptr);
    INIT_PZVAL_COPY(variable_ptr, value);
    *variable_ptr_ptr = variable_ptr;
    return variable_ptr;
  } else {
 /* jump:880 */    if (EXPECTED(Z_TYPE_P(variable_ptr) <= IS_BOOL)) {
      /* nothing to destroy */
      ZVAL_COPY_VALUE(variable_ptr, value);
    } else {
      ZVAL_COPY_VALUE(&garbage, variable_ptr);
      ZVAL_COPY_VALUE(variable_ptr, value);
      _zval_dtor_func(&garbage ZEND_FILE_LINE_CC);
    }
    return variable_ptr;
  }
}

static inline zval *zend_assign_const_to_variable(zval **variable_ptr_ptr,
 /* jump:892 */                                                  zval *value TSRMLS_DC) {
  zval *variable_ptr = *variable_ptr_ptr;
  zval garbage;

 /* jump:898 */  if (Z_TYPE_P(variable_ptr) == IS_OBJECT &&
      UNEXPECTED(Z_OBJ_HANDLER_P(variable_ptr, set) != NULL)) {
    Z_OBJ_HANDLER_P(variable_ptr, set)(variable_ptr_ptr, value TSRMLS_CC);
    return variable_ptr;
  }

 /* jump:902 */  if (UNEXPECTED(Z_REFCOUNT_P(variable_ptr) > 1) &&
      EXPECTED(!PZVAL_IS_REF(variable_ptr))) {
    /* we need to split */
    Z_DELREF_P(variable_ptr);
    GC_ZVAL_CHECK_POSSIBLE_ROOT(variable_ptr);
    ALLOC_ZVAL(variable_ptr);
    INIT_PZVAL_COPY(variable_ptr, value);
    zval_copy_ctor(variable_ptr);
    *variable_ptr_ptr = variable_ptr;
    return variable_ptr;
 /* jump:912 */  } else {
 /* jump:915 */    if (EXPECTED(Z_TYPE_P(variable_ptr) <= IS_BOOL)) {
      /* nothing to destroy */
      ZVAL_COPY_VALUE(variable_ptr, value);
      zendi_zval_copy_ctor(*variable_ptr);
    } else {
      ZVAL_COPY_VALUE(&garbage, variable_ptr);
      ZVAL_COPY_VALUE(variable_ptr, value);
      zendi_zval_copy_ctor(*variable_ptr);
      _zval_dtor_func(&garbage ZEND_FILE_LINE_CC);
    }
    return variable_ptr;
  }
}

static inline zval *zend_assign_to_variable(zval **variable_ptr_ptr,
                                            zval *value TSRMLS_DC) {
  zval *variable_ptr = *variable_ptr_ptr;
  zval garbage;

 /* jump:934 */  if (Z_TYPE_P(variable_ptr) == IS_OBJECT &&
      UNEXPECTED(Z_OBJ_HANDLER_P(variable_ptr, set) != NULL)) {
    Z_OBJ_HANDLER_P(variable_ptr, set)(variable_ptr_ptr, value TSRMLS_CC);
    return variable_ptr;
  }

 /* jump:970 */  if (EXPECTED(!PZVAL_IS_REF(variable_ptr))) {
 /* jump:954 */    if (Z_REFCOUNT_P(variable_ptr) == 1) {
 /* jump:940 */      if (UNEXPECTED(variable_ptr == value)) {
        return variable_ptr;
 /* jump:951 */      } else if (EXPECTED(!PZVAL_IS_REF(value))) {
        Z_ADDREF_P(value);
        *variable_ptr_ptr = value;
 /* jump:947 */        if (EXPECTED(variable_ptr != &EG(uninitialized_zval))) {
          GC_REMOVE_ZVAL_FROM_BUFFER(variable_ptr);
          zval_dtor(variable_ptr);
          efree(variable_ptr);
        } else {
          Z_DELREF_P(variable_ptr);
        }
        return value;
      } else {
        goto copy_value;
      }
    } else { /* we need to split */
      Z_DELREF_P(variable_ptr);
      GC_ZVAL_CHECK_POSSIBLE_ROOT(variable_ptr);
 /* jump:963 */      if (PZVAL_IS_REF(value) && Z_REFCOUNT_P(value) > 0) {
        ALLOC_ZVAL(variable_ptr);
        *variable_ptr_ptr = variable_ptr;
        INIT_PZVAL_COPY(variable_ptr, value);
        zval_copy_ctor(variable_ptr);
        return variable_ptr;
      } else {
        *variable_ptr_ptr = value;
        Z_ADDREF_P(value);
        Z_UNSET_ISREF_P(value);
 /* jump:972 */        return value;
      }
 /* jump:971 */    }
  } else {
 /* jump:983 */    if (EXPECTED(variable_ptr != value)) {
    copy_value:
 /* jump:977 */      if (EXPECTED(Z_TYPE_P(variable_ptr) <= IS_BOOL)) {
        /* nothing to destroy */
        ZVAL_COPY_VALUE(variable_ptr, value);
        zendi_zval_copy_ctor(*variable_ptr);
      } else {
        ZVAL_COPY_VALUE(&garbage, variable_ptr);
        ZVAL_COPY_VALUE(variable_ptr, value);
        zendi_zval_copy_ctor(*variable_ptr);
        _zval_dtor_func(&garbage ZEND_FILE_LINE_CC);
      }
    }
    return variable_ptr;
  }
}

/* Utility Functions for Extensions */
static void
zend_extension_statement_handler(const zend_extension *extension,
                                 zend_op_array *op_array TSRMLS_DC) {
 /* jump:994 */  if (extension->statement_handler) {
 /* jump:995 */    extension->statement_handler(op_array);
  }
}

static void
zend_extension_fcall_begin_handler(const zend_extension *extension,
                                   zend_op_array *op_array TSRMLS_DC) {
 /* jump:1003 */  if (extension->fcall_begin_handler) {
    extension->fcall_begin_handler(op_array);
  }
}
 /* jump:1006 */
static void
zend_extension_fcall_end_handler(const zend_extension *extension,
                                 zend_op_array *op_array TSRMLS_DC) {
 /* jump:1010 */  if (extension->fcall_end_handler) {
    extension->fcall_end_handler(op_array);
  }
}

static inline HashTable *
zend_get_target_symbol_table(int fetch_type TSRMLS_DC) {
  switch (fetch_type) {
  case ZEND_FETCH_LOCAL:
 /* jump:1019 */    if (!EG(active_symbol_table)) {
      zend_rebuild_symbol_table(TSRMLS_C);
    }
    return EG(active_symbol_table);
    break;
  case ZEND_FETCH_GLOBAL:
  case ZEND_FETCH_GLOBAL_LOCK:
    return &EG(symbol_table);
    break;
  case ZEND_FETCH_STATIC:
 /* jump:1031 */    if (!EG(active_op_array)->static_variables) {
      ALLOC_HASHTABLE(EG(active_op_array)->static_variables);
      zend_hash_init(EG(active_op_array)->static_variables, 2, NULL,
                     ZVAL_PTR_DTOR, 0);
    }
    return EG(active_op_array)->static_variables;
    break;
    EMPTY_SWITCH_DEFAULT_CASE()
  }
  return NULL;
 /* jump:1040 */}

static inline zval **zend_fetch_dimension_address_inner(HashTable *ht,
                                                        const zval *dim,
                                                        int dim_type,
 /* jump:1050 */                                                        int type TSRMLS_DC) {
 /* jump:1046 */  zval **retval;
  char *offset_key;
  int offset_key_length;
 /* jump:1049 */  ulong hval;

  switch (dim->type) {
  case IS_NULL:
    offset_key = "";
    offset_key_length = 0;
 /* jump:1067 */    hval = zend_inline_hash_func("", 1);
    goto fetch_string_dim;
 /* jump:1064 */
 /* jump:1062 */  case IS_STRING:
 /* jump:1058 */
    offset_key = dim->value.str.val;
    offset_key_length = dim->value.str.len;
 /* jump:1061 */
 /* jump:1062 */    if (dim_type == IS_CONST) {
      hval = Z_HASH_P(dim);
    } else {
      ZEND_HANDLE_NUMERIC_EX(offset_key, offset_key_length + 1, hval,
                             goto num_index);
 /* jump:1067 */      if (IS_INTERNED(offset_key)) {
        hval = INTERNED_HASH(offset_key);
      } else {
        hval = zend_hash_func(offset_key, offset_key_length + 1);
 /* jump:1094 */      }
 /* jump:1072 */    }
  fetch_string_dim:
 /* jump:1075 */    if (zend_hash_quick_find(ht, offset_key, offset_key_length + 1, hval,
                             (void **)&retval) == FAILURE) {
      switch (type) {
 /* jump:1093 */      case BP_VAR_R:
 /* jump:1092 */        zend_error(E_NOTICE, "Undefined index: %s", offset_key);
        /* break missing intentionally */
      case BP_VAR_UNSET:
      case BP_VAR_IS:
        retval = &EG(uninitialized_zval_ptr);
        break;
 /* jump:1084 */      case BP_VAR_RW:
        zend_error(E_NOTICE, "Undefined index: %s", offset_key);
        /* break missing intentionally */
      case BP_VAR_W: {
        zval *new_zval = &EG(uninitialized_zval);
 /* jump:1089 */
        Z_ADDREF_P(new_zval);
        zend_hash_quick_update(ht, offset_key, offset_key_length + 1, hval,
                               &new_zval, sizeof(zval *), (void **)&retval);
      } break;
      }
    }
    break;
  case IS_DOUBLE:
    hval = zend_dval_to_lval(Z_DVAL_P(dim));
 /* jump:1103 */    goto num_index;
  case IS_RESOURCE:
    zend_error(E_STRICT,
               "Resource ID#%ld used as offset, casting to integer (%ld)",
               Z_LVAL_P(dim), Z_LVAL_P(dim));
    /* Fall Through */
  case IS_BOOL:
  case IS_LONG:
    hval = Z_LVAL_P(dim);
 /* jump:1108 */  num_index:
 /* jump:1127 */    if (zend_hash_index_find(ht, hval, (void **)&retval) == FAILURE) {
      switch (type) {
      case BP_VAR_R:
        zend_error(E_NOTICE, "Undefined offset: %ld", hval);
        /* break missing intentionally */
      case BP_VAR_UNSET:
      case BP_VAR_IS:
        retval = &EG(uninitialized_zval_ptr);
        break;
      case BP_VAR_RW:
        zend_error(E_NOTICE, "Undefined offset: %ld", hval);
        /* break missing intentionally */
      case BP_VAR_W: {
        zval *new_zval = &EG(uninitialized_zval);

        Z_ADDREF_P(new_zval);
        zend_hash_index_update(ht, hval, &new_zval, sizeof(zval *),
                               (void **)&retval);
      } break;
      }
    }
    break;

  default:
    zend_error(E_WARNING, "Illegal offset type");
    return (type == BP_VAR_W || type == BP_VAR_RW)
               ? &EG(error_zval_ptr)
               : &EG(uninitialized_zval_ptr);
  }
  return retval;
}

static void zend_fetch_dimension_address(temp_variable *result,
                                         zval **container_ptr, zval *dim,
                                         int dim_type, int type TSRMLS_DC) {
  zval *container = *container_ptr;
  zval **retval;

  switch (Z_TYPE_P(container)) {

  case IS_ARRAY:
 /* jump:1152 */    if (type != BP_VAR_UNSET && Z_REFCOUNT_P(container) > 1 &&
        !PZVAL_IS_REF(container)) {
      SEPARATE_ZVAL(container_ptr);
      container = *container_ptr;
    }
  fetch_from_array:
 /* jump:1166 */    if (dim == NULL) {
 /* jump:1159 */      zval *new_zval = &EG(uninitialized_zval);

      Z_ADDREF_P(new_zval);
 /* jump:1165 */      if (zend_hash_next_index_insert(Z_ARRVAL_P(container), &new_zval,
                                      sizeof(zval *),
                                      (void **)&retval) == FAILURE) {
        zend_error(E_WARNING, "Cannot add element to the array as the next "
                              "element is already occupied");
 /* jump:1170 */        retval = &EG(error_zval_ptr);
 /* jump:1166 */        Z_DELREF_P(new_zval);
      }
    } else {
      retval = zend_fetch_dimension_address_inner(Z_ARRVAL_P(container), dim,
                                                  dim_type, type TSRMLS_CC);
    }
 /* jump:1172 */    result->var.ptr_ptr = retval;
    PZVAL_LOCK(*retval);
 /* jump:1174 */    return;
    break;

  case IS_NULL:
 /* jump:1179 */    if (container == &EG(error_zval)) {
      result->var.ptr_ptr = &EG(error_zval_ptr);
      PZVAL_LOCK(EG(error_zval_ptr));
 /* jump:1188 */    } else if (type != BP_VAR_UNSET) {
    convert_to_array:
 /* jump:1184 */      if (!PZVAL_IS_REF(container)) {
        SEPARATE_ZVAL(container_ptr);
        container = *container_ptr;
      }
      zval_dtor(container);
      array_init(container);
      goto fetch_from_array;
    } else {
 /* jump:1202 */      /* for read-mode only */
      result->var.ptr_ptr = &EG(uninitialized_zval_ptr);
 /* jump:1193 */      PZVAL_LOCK(EG(uninitialized_zval_ptr));
    }
 /* jump:1196 */    return;
    break;

  case IS_STRING: {
    zval tmp;

 /* jump:1201 */    if (type != BP_VAR_UNSET && Z_STRLEN_P(container) == 0) {
      goto convert_to_array;
    }
 /* jump:1204 */    if (dim == NULL) {
      zend_error_noreturn(E_ERROR, "[] operator not supported for strings");
    }

 /* jump:1224 */    if (Z_TYPE_P(dim) != IS_LONG) {
      switch (Z_TYPE_P(dim)) {
      /* case IS_LONG: */
      case IS_STRING:
 /* jump:1227 */      case IS_DOUBLE:
      case IS_NULL:
      case IS_BOOL:
 /* jump:1216 */        /* do nothing */
        break;
      default:
        zend_error(E_WARNING, "Illegal offset type");
        break;
      }
 /* jump:1221 */
      tmp = *dim;
      zval_copy_ctor(&tmp);
      convert_to_long(&tmp);
      dim = &tmp;
    }
 /* jump:1227 */    if (type != BP_VAR_UNSET) {
      SEPARATE_ZVAL_IF_NOT_REF(container_ptr);
 /* jump:1237 */    }
    container = *container_ptr;
    result->str_offset.str = container;
    PZVAL_LOCK(container);
 /* jump:1233 */    result->str_offset.offset = Z_LVAL_P(dim);
    result->str_offset.ptr_ptr = NULL;
    return;
  } break;

  case IS_OBJECT:
 /* jump:1239 */    if (!Z_OBJ_HT_P(container)->read_dimension) {
      zend_error_noreturn(E_ERROR, "Cannot use object as array");
    } else {
      zval *overloaded_result;

 /* jump:1246 */      if (dim_type == IS_TMP_VAR) {
        zval *orig = dim;
        MAKE_REAL_ZVAL_PTR(dim);
        ZVAL_NULL(orig);
      }
      overloaded_result =
          Z_OBJ_HT_P(container)->read_dimension(container, dim, type TSRMLS_CC);

 /* jump:1270 */      if (overloaded_result) {
 /* jump:1268 */        if (!Z_ISREF_P(overloaded_result)) {
 /* jump:1254 */          if (Z_REFCOUNT_P(overloaded_result) > 0) {
            zval *tmp = overloaded_result;
 /* jump:1262 */
            ALLOC_ZVAL(overloaded_result);
 /* jump:1259 */            ZVAL_COPY_VALUE(overloaded_result, tmp);
            zval_copy_ctor(overloaded_result);
            Z_UNSET_ISREF_P(overloaded_result);
            Z_SET_REFCOUNT_P(overloaded_result, 0);
          }
 /* jump:1267 */          if (Z_TYPE_P(overloaded_result) != IS_OBJECT) {
            zend_class_entry *ce = Z_OBJCE_P(container);
            zend_error(E_NOTICE,
                       "Indirect modification of overloaded element of %s has "
                       "no effect",
                       ce->name);
          }
        }
        retval = &overloaded_result;
      } else {
        retval = &EG(error_zval_ptr);
      }
      AI_SET_PTR(result, *retval);
      PZVAL_LOCK(*retval);
 /* jump:1277 */      if (dim_type == IS_TMP_VAR) {
        zval_ptr_dtor(&dim);
      }
    }
 /* jump:1290 */    return;
    break;

 /* jump:1286 */  case IS_BOOL:
 /* jump:1285 */    if (type != BP_VAR_UNSET && Z_LVAL_P(container) == 0) {
      goto convert_to_array;
    }
    /* break missing intentionally */

  default:
 /* jump:1293 */    if (type == BP_VAR_UNSET) {
      zend_error(E_WARNING, "Cannot unset offset in a non-array variable");
      AI_SET_PTR(result, &EG(uninitialized_zval));
      PZVAL_LOCK(&EG(uninitialized_zval));
    } else {
      zend_error(E_WARNING, "Cannot use a scalar value as an array");
      result->var.ptr_ptr = &EG(error_zval_ptr);
      PZVAL_LOCK(EG(error_zval_ptr));
    }
    break;
  }
}

static void zend_fetch_dimension_address_read(temp_variable *result,
                                              zval **container_ptr, zval *dim,
                                              int dim_type,
                                              int type TSRMLS_DC) {
  zval *container = *container_ptr;
  zval **retval;

  switch (Z_TYPE_P(container)) {

  case IS_ARRAY:
    retval = zend_fetch_dimension_address_inner(Z_ARRVAL_P(container), dim,
                                                dim_type, type TSRMLS_CC);
    AI_SET_PTR(result, *retval);
    PZVAL_LOCK(*retval);
    return;

  case IS_NULL:
    AI_SET_PTR(result, &EG(uninitialized_zval));
    PZVAL_LOCK(&EG(uninitialized_zval));
    return;

  case IS_STRING: {
    zval tmp;
    zval *ptr;

 /* jump:1345 */    if (Z_TYPE_P(dim) != IS_LONG) {
      switch (Z_TYPE_P(dim)) {
      /* case IS_LONG: */
      case IS_STRING:
      case IS_DOUBLE:
      case IS_NULL:
      case IS_BOOL:
        /* do nothing */
        break;
      default:
        zend_error(E_WARNING, "Illegal offset type");
        break;
      }

      ZVAL_COPY_VALUE(&tmp, dim);
 /* jump:1344 */      zval_copy_ctor(&tmp);
      convert_to_long(&tmp);
      dim = &tmp;
    }

 /* jump:1349 */    ALLOC_ZVAL(ptr);
    INIT_PZVAL(ptr);
    Z_TYPE_P(ptr) = IS_STRING;

 /* jump:1356 */    if (Z_LVAL_P(dim) < 0 || Z_STRLEN_P(container) <= Z_LVAL_P(dim)) {
      if (1 == 1)
        zend_error(E_NOTICE, "Uninitialized string offset: %ld", Z_LVAL_P(dim));
      Z_STRVAL_P(ptr) = STR_EMPTY_ALLOC();
      Z_STRLEN_P(ptr) = 0;
    } else {
      Z_STRVAL_P(ptr) = (char *)emalloc(2);
      Z_STRVAL_P(ptr)[0] = Z_STRVAL_P(container)[Z_LVAL_P(dim)];
      Z_STRVAL_P(ptr)[1] = 0;
      Z_STRLEN_P(ptr) = 1;
    }
 /* jump:1364 */    AI_SET_PTR(result, ptr);
    return;
  } break;

 /* jump:1369 */  case IS_OBJECT:
 /* jump:1369 */    if (!Z_OBJ_HT_P(container)->read_dimension) {
      zend_error_noreturn(E_ERROR, "Cannot use object as array");
    } else {
      zval *overloaded_result;

 /* jump:1376 */      if (dim_type == IS_TMP_VAR) {
 /* jump:1375 */        zval *orig = dim;
        MAKE_REAL_ZVAL_PTR(dim);
        ZVAL_NULL(orig);
      }
      overloaded_result =
          Z_OBJ_HT_P(container)->read_dimension(container, dim, type TSRMLS_CC);

 /* jump:1383 */      if (overloaded_result) {
        AI_SET_PTR(result, overloaded_result);
        PZVAL_LOCK(overloaded_result);
 /* jump:1386 */      } else if (result) {
        AI_SET_PTR(result, &EG(uninitialized_zval));
        PZVAL_LOCK(&EG(uninitialized_zval));
      }
 /* jump:1389 */      if (dim_type == IS_TMP_VAR) {
 /* jump:1392 */        zval_ptr_dtor(&dim);
      }
    }
    return;

  default:
    AI_SET_PTR(result, &EG(uninitialized_zval));
    PZVAL_LOCK(&EG(uninitialized_zval));
 /* jump:1403 */    return;
 /* jump:1399 */  }
}

static void zend_fetch_property_address(temp_variable *result,
                                        zval **container_ptr, zval *prop_ptr,
                                        const zend_literal *key,
 /* jump:1405 */                                        int type TSRMLS_DC) {
  zval *container = *container_ptr;
 /* jump:1407 */  ;

 /* jump:1430 */  if (Z_TYPE_P(container) != IS_OBJECT) {
 /* jump:1412 */    if (container == &EG(error_zval)) {
      result->var.ptr_ptr = &EG(error_zval_ptr);
      PZVAL_LOCK(EG(error_zval_ptr));
      return;
    }

    /* this should modify object only if it's empty */
 /* jump:1424 */    if (type != BP_VAR_UNSET &&
        ((Z_TYPE_P(container) == IS_NULL ||
          (Z_TYPE_P(container) == IS_BOOL && Z_LVAL_P(container) == 0) ||
          (Z_TYPE_P(container) == IS_STRING && Z_STRLEN_P(container) == 0)))) {
 /* jump:1422 */      if (!PZVAL_IS_REF(container)) {
        SEPARATE_ZVAL(container_ptr);
        container = *container_ptr;
      }
 /* jump:1436 */      object_init(container);
    } else {
 /* jump:1427 */      zend_error(E_WARNING, "Attempt to modify property of non-object");
      result->var.ptr_ptr = &EG(error_zval_ptr);
 /* jump:1430 */      PZVAL_LOCK(EG(error_zval_ptr));
      return;
    }
  }

 /* jump:1451 */  if (Z_OBJ_HT_P(container)->get_property_ptr_ptr) {
    zval **ptr_ptr = Z_OBJ_HT_P(container)->get_property_ptr_ptr(
        container, prop_ptr, key TSRMLS_CC);
 /* jump:1447 */    if (NULL == ptr_ptr) {
      zval *ptr;

 /* jump:1443 */      if (Z_OBJ_HT_P(container)->read_property &&
          (ptr = Z_OBJ_HT_P(container)->read_property(container, prop_ptr, type,
                                                      key TSRMLS_CC)) != NULL) {
        AI_SET_PTR(result, ptr);
        PZVAL_LOCK(ptr);
      } else {
 /* jump:1461 */        zend_error_noreturn(E_ERROR, "Cannot access undefined property for "
                                     "object with overloaded property access");
      }
 /* jump:1450 */    } else {
      result->var.ptr_ptr = ptr_ptr;
      PZVAL_LOCK(*ptr_ptr);
    }
 /* jump:1457 */  } else if (Z_OBJ_HT_P(container)->read_property) {
    zval *ptr = Z_OBJ_HT_P(container)->read_property(container, prop_ptr, type,
 /* jump:1455 */                                                     key TSRMLS_CC);

    AI_SET_PTR(result, ptr);
    PZVAL_LOCK(ptr);
  } else {
    zend_error(E_WARNING, "This object doesn't support property references");
    result->var.ptr_ptr = &EG(error_zval_ptr);
    PZVAL_LOCK(EG(error_zval_ptr));
 /* jump:1471 */  }
}

static inline zend_brk_cont_element *
 /* jump:1467 */zend_brk_cont(int nest_levels, int array_offset, const zend_op_array *op_array,
              const temp_variable *Ts TSRMLS_DC) {
  int original_nest_levels = nest_levels;
  zend_brk_cont_element *jmp_to;

 /* jump:1494 */  do {
 /* jump:1475 */    if (array_offset == -1) {
      zend_error_noreturn(E_ERROR, "Cannot break/continue %d level%s",
                          original_nest_levels,
                          (original_nest_levels == 1) ? "" : "s");
    }
    jmp_to = &op_array->brk_cont_array[array_offset];
 /* jump:1492 */    if (nest_levels > 1) {
      zend_op *brk_opline = &op_array->opcodes[jmp_to->brk];

      switch (brk_opline->opcode) {
      case ZEND_SWITCH_FREE:
 /* jump:1484 */        if (!(brk_opline->extended_value & EXT_TYPE_FREE_ON_RETURN)) {
          zval_ptr_dtor(&T(brk_opline->op1.var).var.ptr);
 /* jump:1488 */        }
        break;
      case ZEND_FREE:
 /* jump:1489 */        if (!(brk_opline->extended_value & EXT_TYPE_FREE_ON_RETURN)) {
          zendi_zval_dtor(T(brk_opline->op1.var).tmp_var);
        }
        break;
      }
 /* jump:1499 */    }
 /* jump:1495 */    array_offset = jmp_to->parent;
  } while (--nest_levels > 0);
  return jmp_to;
}

#if ZEND_INTENSIVE_DEBUGGING
 /* jump:1501 */
#define CHECK_SYMBOL_TABLES()                                                  \
 /* jump:1503 */  zend_hash_apply(&EG(symbol_table),                                           \
                  (apply_func_t)zend_check_symbol TSRMLS_CC);                  \
  if (&EG(symbol_table) != EG(active_symbol_table)) {                          \
    zend_hash_apply(EG(active_symbol_table),                                   \
                    (apply_func_t)zend_check_symbol TSRMLS_CC);                \
  }

static int zend_check_symbol(zval **pz TSRMLS_DC) {
  if (Z_TYPE_PP(pz) > 9) {
    fprintf(stderr, "Warning!  %x has invalid type!\n", *pz);
/* See http://support.microsoft.com/kb/190351 */
#ifdef PHP_WIN32
    fflush(stderr);
#endif
  } else if (Z_TYPE_PP(pz) == IS_ARRAY) {
    zend_hash_apply(Z_ARRVAL_PP(pz), (apply_func_t)zend_check_symbol TSRMLS_CC);
  } else if (Z_TYPE_PP(pz) == IS_OBJECT) {

 /* jump:1532 */    /* OBJ-TBI - doesn't support new object model! */
    zend_hash_apply(Z_OBJPROP_PP(pz),
 /* jump:1523 */                    (apply_func_t)zend_check_symbol TSRMLS_CC);
  }
 /* jump:1526 */
  return 0;
}

#else
#define CHECK_SYMBOL_TABLES()
#endif

ZEND_API opcode_handler_t *zend_opcode_handlers;

ZEND_API void execute_internal(zend_execute_data *execute_data_ptr,
                               int return_value_used TSRMLS_DC) {
  zval **return_value_ptr =
      &(*(temp_variable *)((char *)execute_data_ptr->Ts +
                           execute_data_ptr->opline->result.var))
           .var.ptr;
  ((zend_internal_function *)execute_data_ptr->function_state.function)
 /* jump:1557 */      ->handler(execute_data_ptr->opline->extended_value, *return_value_ptr,
                (execute_data_ptr->function_state.function->common.fn_flags &
                 ZEND_ACC_RETURN_REFERENCE)
 /* jump:1546 */                    ? return_value_ptr
                    : NULL,
                execute_data_ptr->object, return_value_used TSRMLS_CC);
}

#define ZEND_VM_NEXT_OPCODE()                                                  \
 /* jump:1551 */  CHECK_SYMBOL_TABLES()                                                        \
  ZEND_VM_INC_OPCODE();                                                        \
  ZEND_VM_CONTINUE()

#define ZEND_VM_SET_OPCODE(new_op)                                             \
  CHECK_SYMBOL_TABLES()                                                        \
  OPLINE = new_op

 /* jump:1567 */#define ZEND_VM_JMP(new_op)                                                    \
  if (EXPECTED(!EG(exception))) {                                              \
    ZEND_VM_SET_OPCODE(new_op);                                                \
  } else {                                                                     \
 /* jump:1563 */    LOAD_OPLINE();                                                             \
  }                                                                            \
  ZEND_VM_CONTINUE()

#define ZEND_VM_INC_OPCODE() OPLINE++

#ifdef __GNUC__
#define ZEND_VM_GUARD(name) __asm__("#" #name)
#else
#define ZEND_VM_GUARD(name)
#endif

#include "zend_vm_execute.h"

ZEND_API int zend_set_user_opcode_handler(zend_uchar opcode,
                                          user_opcode_handler_t handler) {
 /* jump:1581 */  if (opcode != ZEND_USER_OPCODE) {
    zend_user_opcodes[opcode] = ZEND_USER_OPCODE;
    zend_user_opcode_handlers[opcode] = handler;
 /* jump:1584 */    return SUCCESS;
  }
  return FAILURE;
}

ZEND_API user_opcode_handler_t zend_get_user_opcode_handler(zend_uchar opcode) {
  return zend_user_opcode_handlers[opcode];
}
 /* jump:1595 */
 /* jump:1591 */ZEND_API zval *zend_get_zval_ptr(int op_type, const znode_op *node,
                                 const temp_variable *Ts,
                                 zend_free_op *should_free,
                                 int type TSRMLS_DC) {
  return get_zval_ptr(op_type, node, Ts, should_free, type);
}
 /* jump:1597 */
ZEND_API zval **zend_get_zval_ptr_ptr(int op_type, const znode_op *node,
 /* jump:1599 */                                      const temp_variable *Ts,
                                      zend_free_op *should_free,
                                      int type TSRMLS_DC) {
  return get_zval_ptr_ptr(op_type, node, Ts, should_free, type);
}

/*
 * Local variables:
 * tab-width: 4
 * c-basic-offset: 4
 * indent-tabs-mode: t
 * End:
 */
