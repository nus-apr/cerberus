#!/usr/bin/perl -w
use strict;
my @cunit_tests = (
    "pretest/compile_with_cunit.bas",
    "compound/while.bas",
    "compound/for_UDT_counter2.bas",
    "compound/continue_mult.bas",
    "compound/exit_mult.bas",
    "compound/select.bas",
    "compound/scope_imp_str.bas",
    "compound/for_UDT_counter.bas",
    "compound/scope.bas",
    "compound/for_pointer_counter.bas",
    "compound/select_const.bas",
    "compound/scope_array.bas",
    "compound/for_UDT_counter3.bas",
    "compound/scope_temp.bas",
    "console/ascii.bas",
    "console/common.bas",
    "const/op_concat.bas",
    "const/nonconst_to_const.bas",
    "const/offsetof.bas",
    "const/const_to_const.bas",
    "const/typedef.bas",
    "const/ptrassign.bas",
    "const/byval_ok.bas",
    "const/ovl.bas",
    "const/extern.bas",
    "crt/stdout.bas",
    "datetime/calc.bas",
    "datetime/testdate.bas",
    "datetime/testtime.bas",
    "dim/auto_var2.bas",
    "dim/udt_initialization2.bas",
    "dim/redim_param.bas",
    "dim/string_init.bas",
    "dim/redim.bas",
    "dim/array_init.bas",
    "dim/static.bas",
    "dim/array_ellipsis_init.bas",
    "dim/udt_initialization3.bas",
    "dim/auto_var.bas",
    "dim/array_static_init.bas",
    "dim/typeof.bas",
    "dim/auto_var3.bas",
    "dim/decl_var_cast.bas",
    "dim/udt_initialization.bas",
    "dim/udt_init_pad.bas",
    "dim/udt_init.bas",
    "expressions/double-to-unsigned.bas",
    "expressions/shortcutops.bas",
    "expressions/iif2.bas",
    "expressions/iif.bas",
    "expressions/mult-assign.bas",
    "expressions/op-self-func.bas",
    "file/text_in2.bas",
    "file/large_dbl.bas",
    "file/lof.bas",
    "file/pipe.bas",
    "file/large_int.bas",
    "file/encod.bas",
    "file/input.bas",
    "file/text_in.bas",
    "functions/bydesc_array2.bas",
    "functions/return_notreg2.bas",
    "functions/str_paramcopy.bas",
    "functions/va_tmpstring.bas",
    "functions/var_args.bas",
    "functions/udt_result_call2.bas",
    "functions/str_recursion.bas",
    "functions/array_recursion_str.bas",
    "functions/zwstring_params.bas",
    "functions/naked_functions.bas",
    "functions/udt_result_access.bas",
    "functions/udt_result_access5.bas",
    "functions/bydesc_arrayfield.bas",
    "functions/udt_result_access4.bas",
    "functions/fixstr_arg.bas",
    "functions/str_z_and_dyn.bas",
    "functions/str_paramrecursion.bas",
    "functions/callconv_mode.bas",
    "functions/bydesc_array_str.bas",
    "functions/return_notreg.bas",
    "functions/rtl_cb.bas",
    "functions/array_recursion.bas",
    "functions/bydesc_array.bas",
    "functions/va_strings.bas",
    "functions/udt_result_call.bas",
    "functions/callconv_default.bas",
    "functions/udt_result2.bas",
    "functions/va_int_and_ptrs.bas",
    "functions/void_param.bas",
    "functions/udt_result_access2.bas",
    "functions/udt_result_access3.bas",
    "functions/udt_result.bas",
    "functions/bydesc_arrayfield_str.bas",
    "interactive/input.bas",
    "macros/hello.bas",
    "macros/macro_trim.bas",
    "macros/macro_nested2.bas",
    "macros/seq_size.bas",
    "macros/bit___.bas",
    "macros/conditional.bas",
    "macros/recursive.bas",
    "macros/macro_nested1.bas",
    "macros/variadic.bas",
    "macros/min.bas",
    "namespace/reimp2.bas",
    "namespace/redim2.bas",
    "namespace/using.bas",
    "namespace/using_nested2.bas",
    "namespace/dups.bas",
    "namespace/dim_array.bas",
    "namespace/using_nested.bas",
    "namespace/redim.bas",
    "namespace/using2.bas",
    "namespace/reimp1.bas",
    "namespace/global.bas",
    "namespace/interf_imp.bas",
    "namespace/using_rec.bas",
    "namespace/extimp.bas",
    "namespace/enum.bas",
    "namespace/global2.bas",
    "namespace/reimp3.bas",
    "namespace/sum.bas",
    "namespace/multi_nested.bas",
    "namespace/dups_qkwd.bas",
    "namespace/using_reimp2.bas",
    "namespace/import_method.bas",
    "namespace/using_reimp.bas",
    "namespace/dups2.bas",
    "numbers/hexliteral.bas",
    "numbers/tostring.bas",
    "numbers/cast_ll2f.bas",
    "numbers/casting.bas",
    "numbers/cast_unsigned.bas",
    "numbers/cast_signed.bas",
    "numbers/const_op.bas",
    "numbers/numbers.bas",
    "numbers/longints.bas",
    "numbers/cast_f2ll.bas",
    "numbers/coercion.bas",
    "numbers/literals.bas",
    "optimizations/side_effects.bas",
    "optimizations/logic1.bas",
    "optimizations/inline_logexpsqr.bas",
    "optimizations/logic2.bas",
    "optimizations/inline_fixfrac.bas",
    "optimizations/vector.bas",
    "optimizations/casting.bas",
    "optimizations/operand_reorder.bas",
    "optimizations/inline_trans.bas",
    "optimizations/literaldup.bas",
    "optimizations/mul_assoc.bas",
    "optimizations/inline_sgn.bas",
    "optimizations/mul_dist.bas",
    "optimizations/const_idx.bas",
    "optimizations/toshift.bas",
    "optimizations/self_compare.bas",
    "overload/implicit_ctor2.bas",
    "overload/bop_coercion2.bas",
    "overload/op_concat.bas",
    "overload/op_deref.bas",
    "overload/op_ctor_coercion_ref.bas",
    "overload/uop_coersion.bas",
    "overload/op_ctor_coercion.bas",
    "overload/op_addrof.bas",
    "overload/type_vararg.basc",
    "overload/op_new_delete.bas",
    "overload/op_to_ptr.bas",
    "overload/integer_width.bas",
    "overload/sub_call.bas",
    "overload/addressof.bas",
    "overload/arg_cast.bas",
    "overload/arg_cast2.bas",
    "overload/implicit_ctor.bas",
    "overload/anontype.bas",
    "overload/op_ctor_coercion_udt.bas",
    "overload/hex_oct_bin.bas",
    "overload/op_cast_coercion.bas",
    "overload/strings.bas",
    "overload/funptr.bas",
    "overload/sub_call2.bas",
    "overload/defaults.bas",
    "overload/overruled_ctor.bas",
    "overload/bop_coercion.bas",
    "overload/op_deref2.bas",
    "overload/bydesc.bas",
    "overload/strings_ptr.bas",
    "overload/simple.bas",
    "overload/access_mode.bas",
    "pointers/funptr_mangling.bas",
    "pointers/addrofnull.bas",
    "pointers/casting2.bas",
    "pointers/new_init.bas",
    "pointers/field_deref.bas",
    "pointers/multi_deref.bas",
    "pointers/funptr-funcderef.bas",
    "pointers/array_ptr_fn.bas",
    "pointers/indexing1.bas",
    "pointers/indexing2.bas",
    "pointers/typedef_fwd.bas",
    "pointers/funptr_fwdbyref.bas",
    "pointers/prop_new_del.bas",
    "pointers/field_array_desc.bas",
    "pointers/funptr_array1.bas",
    "pointers/casting3.bas",
    "pointers/casting1.bas",
    "pointers/field_deref_func.bas",
    "pointers/arith.bas",
    "pointers/addr_deref.bas",
    "pp/numeric_ops.bas",
    "pp/inc_once2.bas",
    "pp/inc_once3.bas",
    "pp/inc_once2_self.bas",
    "pp/typeof.bas",
    "pp/inc_once5.bas",
    "pp/inc_once1.bas",
    "pp/inc_once4.bas",
    "quirk/data.bas",
    "quirk/data_fwd2.bas",
    "quirk/data_fwd.bas",
    "quirk/casting.bas",
    "quirk/open_methods.bas",
    "quirk/sizeof-typeof-expr.bas",
    "quirk/typeof.bas",
    "scopes/macros.bas",
    "scopes/types.bas",
    "scopes/delaydtor.bas",
    "scopes/branch_cross.bas",
    "scopes/enums.bas",
    "scopes/fornext.bas",
    "scopes/consts.bas",
    "string/ltrim.bas",
    "string/inline_zstring_cast.bas",
    "string/len.bas",
    "string/chr_0.bas",
    "string/instr_0.bas",
    "string/initialization.bas",
    "string/escape.bas",
    "string/instrrev_x.bas",
    "string/initialization2.bas",
    "string/instrrev_0.bas",
    "string/strptr.bas",
    "string/val.bas",
    "string/format.bas",
    "string/redim.bas",
    "string/mid_stmt_dref_dest.bas",
    "string/trim.bas",
    "string/str_idx.bas",
    "string/compare.bas",
    "string/cvi_mki.bas",
    "string/oct.bas",
    "string/comp_null.bas",
    "string/instr_x.bas",
    "string/print_using.bas",
    "string/rtrim.bas",
    "string/mkcv.bas",
    "string/mid_set.bas",
    "string/array_len.bas",
    "string/str_pad.bas",
    "structs/with_and_len.bas",
    "structs/ctor_byval.bas",
    "structs/bitfield-misc.bas",
    "structs/obj_property_dup.bas",
    "structs/obj_meth_static2.bas",
    "structs/obj_global.bas",
    "structs/obj_property.bas",
    "structs/obj_shared_array_ini.bas",
    "structs/ctor_union_copy.bas",
    "structs/array_only_dtor.bas",
    "structs/obj_property_idx.bas",
    "structs/obj_cast_ovl.bas",
    "structs/anon_nested.bas",
    "structs/obj_ptr2.bas",
    "structs/bitfield-opovlcast.bas",
    "structs/padding.bas",
    "structs/ctor_bitfield.bas",
    "structs/const_method.bas",
    "structs/obj_global_with_temp.bas",
    "structs/ctor_coercion.bas",
    "structs/bitfield_select.bas",
    "structs/bitfield_union.bas",
    "structs/ops.bas",
    "structs/bitfield_access.bas",
    "structs/anon_align.bas",
    "structs/clear.bas",
    "structs/obj_cast_ovl2.bas",
    "structs/assign_anon.bas",
    "structs/obj_meth_ovld_sub.bas",
    "structs/imp_var_dup.bas",
    "structs/obj_static.bas",
    "structs/obj_static_dyn.bas",
    "structs/op_assign_explicit_fwd.bas",
    "structs/obj_vis_static.bas",
    "structs/bitfield_conv.bas",
    "structs/obj_init_toself.bas",
    "structs/enum_decl.bas",
    "structs/bool_expr_cast.bas",
    "structs/obj_field_ini_str.bas",
    "structs/obj_temp.bas",
    "structs/obj_static_array_ini.bas",
    "structs/obj_property2.bas",
    "structs/obj_field_ini_array_nested.bas",
    "structs/obj_property_idx2.bas",
    "structs/ctor_byref.bas",
    "structs/with_prop.bas",
    "structs/obj_field_ini.bas",
    "structs/obj_static_array.bas",
    "structs/str_redim.bas",
    "structs/obj_redim_presv.bas",
    "structs/obj_field_ini_array.bas",
    "structs/op_access_mode.bas",
    "structs/obj_ptr.bas",
    "structs/obj_ptr_vec.bas",
    "structs/init_union.bas",
    "structs/obj_global_with_temp3.bas",
    "structs/obj_temp2.bas",
    "structs/obj_ptr_ini.bas",
    "structs/obj_global_with_temp2.bas",
    "structs/ctor_default.bas",
    "structs/obj_ptr3.bas",
    "structs/new_in_type_body.bas",
    "structs/obj_byval_return.bas",
    "structs/const_access.bas",
    "structs/ctor_assign_parenths.bas",
    "structs/intrinsic_anon.bas",
    "structs/obj_ptrto_static.bas",
    "structs/bitfield_init.bas",
    "structs/obj_inner_enum.bas",
    "structs/ctor_union.bas",
    "structs/assignment.bas",
    "structs/ctor_bydesc.bas",
    "structs/obj_property_stmt.bas",
    "structs/obj_redim.bas",
    "structs/func_backpatching.bas",
    "structs/bitfield_logic.bas",
    "structs/obj_meth_static.bas",
    "structs/obj_global_dyn.bas",
    "structs/obj_meth_ovld.bas",
    "structs/obj_default_param.bas",
    "swap/udt.bas",
    "threads/racecondition.bas",
    "typedef/pointers.bas",
    "typedef/backpatch.bas",
    "typedef/syntax.bas",
    "wstring/ltrim.bas",
    "wstring/len.bas",
    "wstring/lineinput.bas",
    "wstring/unc.bas",
    "wstring/woct.bas",
    "wstring/data.bas",
    "wstring/instr_0.bas",
    "wstring/utf8.bas",
    "wstring/instrrev_x.bas",
    "wstring/instrrev_0.bas",
    "wstring/select.bas",
    "wstring/trim.bas",
    "wstring/concat_conv.bas",
    "wstring/wchr.bas",
    "wstring/symb.bas",
    "wstring/utf_conv.bas",
    "wstring/uniseq.bas",
    "wstring/instr_x.bas",
    "wstring/asc.bas",
    "wstring/rtrim.bas",
    "pretest/compile_with_cunit.bas"
);

my @fb_tests = (
    "SRCLIST_COMPILE_ONLY_OK += ./pretest/compile_only_ok.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./comments/multiline.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./const/typedef-const-forward-ptr-2-1.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./const/typedef-forward-ptr-constptr-2.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./const/fromconst.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./const/backpatch-type-constptr-2.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./const/typedef-forward-constptr-1-2.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./const/typedef-forward-constptr-2-2.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./const/typedef-const-forward-ptr-1-2.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./const/type_alias.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./const/typedef-forward-constptr-constptr-3.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./const/make-typedef-const-2.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./functions/mangle.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./macros/macro_empty.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./macros/conditional2.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./macros/intrinsic.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./overload/tostring.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./overload/allow_byval_ptr.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./overload/op_to_self.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./quirk/gfx_methAsMod.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./quirk/gfx_propertiesasbuffers.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./structs/const_method2.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./structs/obj_access_const2.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./structs/obj_access_const4.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./structs/implicit_dtor.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./typedef/backpatch-deleted.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./typedef/redefine.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./pretest/compile_only_fail.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/backpatch-const-type-constptr-2.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/var_const.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/rtl-line.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/typedef-forward-constptr-constptr-1.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/typedef-const-forward-1.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/typedef-const-forward-ptr-1-1.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/typedef-forward-constptr-1-1.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/backpatch-const-type-constptr-1.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/make-typedef-const-1.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/member.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/typedef-const-forward-ptr-2-2.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/funcres.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/any_const.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/typedef-forward-constptr-constptr-2.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/constptr_to_ptr.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/ovl_ambiguous.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/rtl-getmouse.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/rtl-get.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/typedef-const-forward-2.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/backpatch-type-constptr-1.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/typedef-forward-constptr-2-1.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/backpatch-const-type.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/rtl-getjoystick.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/typedef-forward-ptr-constptr-1.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/rtl-mid.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/typedef2.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/typedef-const-forward-3.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/const_to_nonconst.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/rtl-swap.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./const/rtl-getf.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./functions/array_param.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./macros/invalid_symbolname.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./namespace/dups_fail2.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./namespace/dups_fail.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./quirk/casting_typo.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./quirk/function_array.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./structs/protected_member.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./structs/obj_access_const3.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./structs/obj_access_const.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./structs/const_method3.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./structs/private_member2.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./structs/private_member.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./structs/const_member2.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./structs/const_method4.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./structs/const_method5.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./structs/const_member.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./structs/protected_member2.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./threads/bad_call.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./typedef/backpatch-ptr-limit-2.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./typedef/alias-ptr-limit.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./typedef/backpatch-ptr-limit-3.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./typedef/incomplete.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./typedef/void.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./typedef/backpatch-ptr-limit-1.bas",
    "SRCLIST_COMPILE_AND_RUN_OK += ./pretest/compile_and_run_ok.bas",
    "SRCLIST_COMPILE_AND_RUN_OK += ./overload/void_resolution.bas",
    "SRCLIST_COMPILE_AND_RUN_OK += ./quirk/quirk_arraystatement.bas",
    "SRCLIST_COMPILE_AND_RUN_OK += ./scopes/dtor_eol_eof1.bas",
    "SRCLIST_COMPILE_AND_RUN_OK += ./scopes/dtor_eol_eof2.bas",
    "SRCLIST_COMPILE_AND_RUN_FAIL += ./pretest/compile_and_run_fail.bas",
    "SRCLIST_MULTI_MODULE_OK += ./pretest/multi_module_ok.bmk",
    "SRCLIST_MULTI_MODULE_OK += ./dim/mod_common/submod.bmk",
    "SRCLIST_MULTI_MODULE_OK += ./dim/submod/submod.bmk",
    "SRCLIST_MULTI_MODULE_OK += ./dim/mod_extern/submod.bmk",
    "SRCLIST_MULTI_MODULE_OK += ./namespace/submod/submod.bmk",
    "SRCLIST_MULTI_MODULE_FAIL += ./pretest/multi_module_fail.bmk"

);

my @qb_tests = (
    "SRCLIST_COMPILE_ONLY_OK += ./qb/literal_types.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./qb/file_open_com.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./qb/suffixes.bas",
    "SRCLIST_COMPILE_ONLY_OK += ./qb/file_open_lpt.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./qb/file_open_lpt_fail.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./qb/file_open_scrn_fail.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./qb/file_open_com_fail.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./qb/file_open_cons_fail.bas",
    "SRCLIST_COMPILE_ONLY_FAIL += ./qb/scope_block.bas",
    "SRCLIST_COMPILE_AND_RUN_OK += ./qb/data.bas",
    "SRCLIST_COMPILE_AND_RUN_OK += ./qb/align_qb.bas",
    "SRCLIST_COMPILE_AND_RUN_OK += ./qb/suffixes2.bas",
    "SRCLIST_COMPILE_AND_RUN_OK += ./qb/file_open_scrn.bas",
    "SRCLIST_COMPILE_AND_RUN_OK += ./qb/file_open.bas",
    "SRCLIST_COMPILE_AND_RUN_OK += ./qb/call.bas",
    "SRCLIST_COMPILE_AND_RUN_OK += ./qb/str.bas",
    "SRCLIST_COMPILE_AND_RUN_OK += ./qb/qbtypes.bas",
    "SRCLIST_COMPILE_AND_RUN_OK += ./qb/file_open_cons.bas",
    "SRCLIST_COMPILE_AND_RUN_OK += ./qb/literal_sizes.bas",
    "SRCLIST_COMPILE_AND_RUN_OK += ./qb/mkcv.bas"
);

my @deprecated_tests = (
    "SRCLIST_COMPILE_AND_RUN_OK += ./deprecated/implicit_explicit.bas",
    "SRCLIST_COMPILE_AND_RUN_OK += ./deprecated/shadow_inherit.bas",
    "SRCLIST_COMPILE_AND_RUN_OK += ./deprecated/string_suffix.bas",
    "SRCLIST_COMPILE_AND_RUN_OK += ./deprecated/innerdup.bas"
);

if (length($ARGV[0]) == 0)
{
    die "Must specify a test number";
}
my $cunit_len = scalar @cunit_tests;
my $fb_len = scalar @fb_tests;
my $qb_len = scalar @qb_tests;
my $deprecated_len = scalar @deprecated_tests;



my $length = $cunit_len + $fb_len + $qb_len + $deprecated_len;
if ($ARGV[0] =~ m/length/) { print $length; exit 0 }


my $num = $ARGV[0] - 1;

my $name = "";
my $type = "";
if ($num < ($cunit_len))
{
    $name = $cunit_tests[$num];
    $type = "cunit";
}
elsif ($num < ($cunit_len + $fb_len))
{
    $name = $fb_tests[$num - $cunit_len];
    $type = "fb";
}
elsif ($num < ($cunit_len + $fb_len + $qb_len))
{
    $name = $qb_tests[$num - $cunit_len - $fb_len];
    $type = "qb";
}
else
{
    $name = $deprecated_tests[$num - $cunit_len - $fb_len - $qb_len];
    $type = "deprecated";
}
#time for i in $(seq 1 `perl ~/genprog-many-bugs/alltests length`) ; do perl ~/genprog-many-bugs/alltests $i ; done
#print "test name is $name, and type is $type\n";
#exit 0;

if ($num < 0 || $num > $length)
{
    die "Invalid test number: $num";
}


sub reset_incs {
    system("rm -f log-tests-fb.inc log-tests-qb.inc log-tests-deprecated.inc");
    my $res = system("touch log-tests-fb.inc log-tests-qb.inc log-tests-deprecated.inc cunit-tests.inc") >> 8;
    if ($res != 0)
    {
        die "Unable to touch output files: $!";
    }
}

sub make_test {
    my $test_type = $_[0];
    reset_incs ();

    #print "$name\n";
    #print "make --no-print-directory -f log-tests.mk mostlyclean FB_LANG=$test_type\n";
    #print "make --no-print-directory -f log-tests.mk FB_LANG=$test_type\n";
    my @cleanup = `make --no-print-directory -f log-tests.mk mostlyclean FB_LANG=$test_type`;
    print STDERR "type is $test_type\n";
    #my @cleanup = `make --no-print-directory clean`;
    #my $res = system("echo $name > log-tests-$test_type.inc") >> 8;
    my $res = system("echo $name > log-tests-$test_type.inc") >> 8;
    my @output = `FBC=\`pwd\`/../../fbc-root/bin/fbc make --no-print-directory log-tests FBC=\`pwd\`/../../fbc-root/bin/fbc FB_LANG=$test_type`;
    print @output;
    chomp @output;

    $name =~ s/[^.]*[.]\/(.*)/$1/;
    foreach my $line(@output)
    {
        if ($line =~ m/RESULT=FAILED/)
        {
            print "FAIL: $name\n";
            exit 1;
        }
        elsif ($line =~ m/None Found/)
        {
            print "PASS: $name\n";
            exit 0;
        }
    }

    print "ERROR: unable to interpret test output!\n";
    system("echo $name >> PARSE_FAILURES");
    exit 1;
}


if ($type =~ "cunit")
{
    my $res1 = system("echo SRCLIST += $name > cunit-tests.inc") >> 8;
    my @result = `FBC=\`pwd\`/../../fbc-root/bin/fbc make --no-print-directory cunit-tests FBC=\`pwd\`/../../fbc-root/bin/fbc`;
    my $float_result = 0;
    foreach my $line (@result)
    {
        #print $line;
        if ($line =~ m/[ \t]+tests/)
        {
            chomp $line;
            $line =~ s/.*tests[ ]+([0-9])+[ ]+[0-9]+[ ]+([0-9])+.*/$2\/$1/;
            #print "$line\n";
            $float_result = eval($line);
            if (! (defined $float_result))
            {
                $float_result = 0;
            }
            last;
        }
    }
    if ($float_result == 1)
    {
        print "PASS: $name\n";
        exit 0
    }
    else
    {
        print "FAIL: $name\n";
        exit 1;
    }
}
else
{
    make_test $type;
}


