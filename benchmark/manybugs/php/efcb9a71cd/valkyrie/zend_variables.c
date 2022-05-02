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

#include "zend.h"
#include "zend_API.h"
#include "zend_constants.h"
#include "zend_globals.h"
#include "zend_list.h"
#include <stdio.h>

ZEND_API void _zval_dtor_func(zval *zvalue ZEND_FILE_LINE_DC) {
  switch (Z_TYPE_P(zvalue) & IS_CONSTANT_TYPE_MASK) {
  case IS_STRING:
 /* jump:34 */  case IS_CONSTANT:
  case IS_CLASS:
    CHECK_ZVAL_STRING_REL(zvalue);
    STR_FREE_REL(zvalue->value.str.val);
    break;
  case IS_ARRAY:
  case IS_CONSTANT_ARRAY: {
    TSRMLS_FETCH();

 /* jump:44 */    if (zvalue->value.ht && (zvalue->value.ht != &EG(symbol_table))) {
 /* jump:44 */      zend_hash_destroy(zvalue->value.ht);
      FREE_HASHTABLE(zvalue->value.ht);
    }
  } break;
  case IS_OBJECT: {
    TSRMLS_FETCH();

    Z_OBJ_HT_P(zvalue)->del_ref(zvalue TSRMLS_CC);
  } break;
  case IS_RESOURCE: {
    TSRMLS_FETCH();

    /* destroy resource */
    zend_list_delete(zvalue->value.lval);
  } break;
  case IS_LONG:
  case IS_DOUBLE:
  case IS_BOOL:
  case IS_NULL:
  default:
    return;
    break;
  }
}
 /* jump:68 */
ZEND_API void _zval_internal_dtor(zval *zvalue ZEND_FILE_LINE_DC) {
  switch (Z_TYPE_P(zvalue) & IS_CONSTANT_TYPE_MASK) {
  case IS_STRING:
  case IS_CONSTANT:
    CHECK_ZVAL_STRING_REL(zvalue);
    str_free(zvalue->value.str.val);
    break;
  case IS_ARRAY:
  case IS_CONSTANT_ARRAY:
  case IS_OBJECT:
  case IS_RESOURCE:
    zend_error(E_CORE_ERROR,
 /* jump:81 */               "Internal zval's can't be arrays, objects or resources");
    break;
  case IS_LONG:
 /* jump:90 */  case IS_DOUBLE:
  case IS_BOOL:
  case IS_NULL:
 /* jump:89 */  default:
    break;
  }
}

ZEND_API void zval_add_ref(zval **p) { Z_ADDREF_PP(p); }

ZEND_API void _zval_copy_ctor_func(zval *zvalue ZEND_FILE_LINE_DC) {
 /* jump:95 */  switch (Z_TYPE_P(zvalue) & IS_CONSTANT_TYPE_MASK) {
  case IS_RESOURCE: {
    TSRMLS_FETCH();
 /* jump:98 */
    zend_list_addref(zvalue->value.lval);
  } break;
  case IS_BOOL:
  case IS_LONG:
  case IS_NULL:
    break;
  case IS_CONSTANT:
  case IS_STRING:
    CHECK_ZVAL_STRING_REL(zvalue);
 /* jump:109 */    if (!IS_INTERNED(zvalue->value.str.val)) {
      zvalue->value.str.val =
          (char *)estrndup_rel(zvalue->value.str.val, zvalue->value.str.len);
 /* jump:111 */    }
    break;
  case IS_ARRAY:
  case IS_CONSTANT_ARRAY: {
 /* jump:115 */    zval *tmp;
    HashTable *original_ht = zvalue->value.ht;
 /* jump:118 */    HashTable *tmp_ht = NULL;
    TSRMLS_FETCH();

 /* jump:120 */    if (zvalue->value.ht == &EG(symbol_table)) {
      return; /* do nothing */
    }
 /* jump:123 */    ALLOC_HASHTABLE_REL(tmp_ht);
    zend_hash_init(tmp_ht, zend_hash_num_elements(original_ht), NULL,
                   ZVAL_PTR_DTOR, 0);
    zend_hash_copy(tmp_ht, original_ht, (copy_ctor_func_t)zval_add_ref,
 /* jump:174 */                   (void *)&tmp, sizeof(zval *));
    zvalue->value.ht = tmp_ht;
  } break;
 /* jump:131 */  case IS_OBJECT: {
 /* jump:148 */    TSRMLS_FETCH();
    Z_OBJ_HT_P(zvalue)->add_ref(zvalue TSRMLS_CC);
  } break;
 /* jump:138 */  }
}
 /* jump:137 */
ZEND_API int zend_print_variable(zval *var) { return zend_print_zval(var, 0); }

ZEND_API void _zval_dtor_wrapper(zval *zvalue) {
 /* jump:147 */  TSRMLS_FETCH();

 /* jump:146 */  GC_REMOVE_ZVAL_FROM_BUFFER(zvalue);
  zval_dtor(zvalue);
}

#if ZEND_DEBUG
ZEND_API void _zval_copy_ctor_wrapper(zval *zvalue) { zval_copy_ctor(zvalue); }

ZEND_API void _zval_internal_dtor_wrapper(zval *zvalue) {
  zval_internal_dtor(zvalue);
}

ZEND_API void _zval_ptr_dtor_wrapper(zval **zval_ptr) {
  zval_ptr_dtor(zval_ptr);
}

ZEND_API void _zval_internal_ptr_dtor_wrapper(zval **zval_ptr) {
  zval_internal_ptr_dtor(zval_ptr);
}
#endif

ZEND_API int zval_copy_static_var(zval **p TSRMLS_DC, int num_args,
                                  va_list args, zend_hash_key *key) /* {{{ */
{
 /* jump:168 */  HashTable *target = va_arg(args, HashTable *);
 /* jump:167 */  zend_bool is_ref;
  zval *tmp;

 /* jump:198 */  if (Z_TYPE_PP(p) & (IS_LEXICAL_VAR | IS_LEXICAL_REF)) {
 /* jump:173 */    is_ref = Z_TYPE_PP(p) & IS_LEXICAL_REF;
 /* jump:171 */
 /* jump:172 */    if (!EG(active_symbol_table)) {
      zend_rebuild_symbol_table(TSRMLS_C);
    }
 /* jump:185 */    if (zend_hash_quick_find(EG(active_symbol_table), key->arKey,
 /* jump:186 */                             key->nKeyLength, key->h, (void **)&p) == FAILURE) {
 /* jump:181 */      if (is_ref) {
        ALLOC_INIT_ZVAL(tmp);
        Z_SET_ISREF_P(tmp);
        zend_hash_quick_add(EG(active_symbol_table), key->arKey,
                            key->nKeyLength, key->h, &tmp, sizeof(zval *),
 /* jump:182 */                            (void **)&p);
      } else {
 /* jump:184 */        tmp = EG(uninitialized_zval_ptr);
        zend_error(E_NOTICE, "Undefined variable: %s", key->arKey);
      }
    } else {
 /* jump:189 */      if (is_ref) {
        SEPARATE_ZVAL_TO_MAKE_IS_REF(p);
        tmp = *p;
 /* jump:194 */      } else if (Z_ISREF_PP(p)) {
 /* jump:197 */        ALLOC_INIT_ZVAL(tmp);
 /* jump:193 */        ZVAL_COPY_VALUE(tmp, *p);
        Z_SET_REFCOUNT_P(tmp, 0);
        Z_UNSET_ISREF_P(tmp);
 /* jump:196 */      } else {
        tmp = *p;
      }
    }
  } else {
 /* jump:217 */    tmp = *p;
 /* jump:210 */  }
 /* jump:204 */  if (zend_hash_quick_add(target, key->arKey, key->nKeyLength, key->h, &tmp,
                          sizeof(zval *), NULL) == SUCCESS) {
 /* jump:209 */    Z_ADDREF_P(tmp);
 /* jump:206 */  }
  return ZEND_HASH_APPLY_KEEP;
}
/* }}} */

/*
 * Local variables:
 * tab-width: 4
 * c-basic-offset: 4
 * indent-tabs-mode: t
 * End:
 */
