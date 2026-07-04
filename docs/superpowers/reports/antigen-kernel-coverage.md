# Kernel Coverage

| Module | Covered | Total | % |
|---|---:|---:|---:|
| Cure.Core.Certificate | 153 | 192 | 79.7 |
| Cure.Core.Conv | 50 | 66 | 75.8 |
| Cure.Core.Eval | 62 | 65 | 95.4 |
| Cure.Core.Inductive | 40 | 79 | 50.6 |
| Cure.Core.Kernel | 237 | 340 | 69.7 |
| Cure.Core.Normalise | 86 | 103 | 83.5 |
| Cure.Core.Quote | 34 | 37 | 91.9 |
| Cure.Core.Serialize | 80 | 108 | 74.1 |

## Cold lines

## Cure.Core.Certificate cold lines

  - add_rel/2: 323
  - arg_relation/2: 295, 306, 309
  - arity_of/1: 443
  - callees_env/2: 409
  - calls?/2: 591, 593, 595, 596, 597, 609, 610, 613
  - function_edges/3: 450, 458
  - mutual_group_total?/4: 436
  - pathmul/2: 317
  - reaches?/4: 536
  - row_len/1: 494
  - rows/2: 284
  - scrut_index/1: 252
  - shift_term/2: 573, 574, 575
  - walk/4: 161, 162
  - walk_node/4: 187, 190, 193, 195, 196, 207, 208, 209, 212, 215, 216, 217

## Cure.Core.Conv cold lines

  - conv?/4: 49
  - conv_neutral?/4: 135, 136, 139, 150
  - conv_struct?/4: 70, 83, 102
  - eta_eq?/4: 108, 109
  - same_value_no_delta?/3: 187, 188, 190, 191, 194, 199

## Cure.Core.Eval cold lines

  - eval/2: 26
  - vfst/1: 153
  - vsnd/1: 156

## Cure.Core.Inductive cold lines

  - arg_telescope/2: 225, 226, 227
  - ctor_quantities/2: 234, 235, 236, 237
  - ctor_result_indices/2: 216, 217, 218
  - ctor_result_params/2: 266, 267, 268, 269
  - family?/2: 199
  - gather_data_heads/2: 361, 363, 364
  - index_telescope/2: 244, 245, 246
  - occurs?/2: 373, 375, 376, 377, 378, 379, 380, 381, 384, 388, 389, 391
  - param_telescope/2: 254
  - register_builtin/3: 127, 129, 132
  - strictly_positive?/4: 318, 335

## Cure.Core.Kernel cold lines

  - bind_index/4: 861, 864, 865, 866, 867, 869, 874
  - branch_unify/4: 771, 773, 774, 775
  - check/3: 289, 296, 312
  - check_case_branches/7: 706, 711
  - check_ctor/3: 412, 413, 415, 416, 417, 418, 419, 420
  - check_ctor_args/2: 510, 511, 513, 516
  - check_def/2: 358
  - check_family/2: 395, 397, 398
  - check_field_levels/2: 523
  - check_motive_wf/4: 606
  - check_result_indices/3: 991, 992, 993, 994
  - check_telescope/2: 499, 502, 503, 504
  - check_uniform_params/5: 432, 433, 436, 439, 440, 442
  - ensure_eq/1: 474
  - ensure_pi/1: 466
  - head_key/1: 904, 905, 906
  - infer/2: 44, 67, 95, 125, 166, 181, 237
  - infer_prim/3: 1070
  - infer_sort/2: 459
  - infer_type_value_sort/2: 618, 620, 621, 622, 631, 689
  - normalize/2: 34
  - normalize/3: 38
  - numeric_type?/1: 1074
  - reduce_index_pairs/3: 805
  - remap_index_error/2: 557
  - replace_branch_vars/2: 945, 948, 951, 954, 957, 959, 960, 970, 971, 976, 979, 982
  - resolve_index_var/3: 884, 885, 886
  - rigid_index?/1: 893, 894, 895, 896, 897, 898, 899, 900, 901
  - shift_subst/2: 987
  - unify_one/4: 824, 826
  - unify_spine/4: 838, 840, 843

## Cure.Core.Normalise cold lines

  - fuel_key/0: 85
  - nf/2: 37
  - normalize_opts/1: 108, 112, 116, 122
  - reduce_unfolded/3: 309, 310, 311, 315, 316, 317
  - spend_fuel/1: 335
  - unfold_certified_head/3: 261, 267
  - whnf_value/3: 54
  - with_fuel/2: 77

## Cure.Core.Quote cold lines

  - split_data_args/3: 93, 94, 95

## Cure.Core.Serialize cold lines

  - build/1: 133, 134, 135, 136, 139
  - build_all/1: 203
  - build_branches/1: 213, 216
  - build_node/2: 148, 149, 166, 191
  - decode/1: 75, 76
  - enc/1: 34, 35
  - parse/1: 122, 123
  - parse_list/2: 126
  - str/1: 63
  - take_atom/2: 106
  - take_string/2: 98, 99, 100, 101
  - tokenize/2: 87, 88, 89
