# Kernel Coverage

| Module | Covered | Total | % |
|---|---:|---:|---:|
| Cure.Core.Certificate | 58 | 84 | 69.0 |
| Cure.Core.Conv | 27 | 66 | 40.9 |
| Cure.Core.Eval | 62 | 73 | 84.9 |
| Cure.Core.Inductive | 39 | 79 | 49.4 |
| Cure.Core.Kernel | 174 | 336 | 51.8 |
| Cure.Core.Normalise | 73 | 103 | 70.9 |
| Cure.Core.Quote | 27 | 32 | 84.4 |
| Cure.Core.Serialize | 65 | 108 | 60.2 |

## Cold lines

## Cure.Core.Certificate cold lines

  - calls?/2: 229, 231, 233, 234, 235, 247, 248, 251
  - decreasing?/3: 197
  - guarded?/5: 128, 129
  - guarded_node?/5: 137, 140, 149, 159, 162, 165, 167, 168, 180, 181, 183, 187, 188
  - reaches?/4: 97
  - subterm_scrutinee?/3: 206

## Cure.Core.Conv cold lines

  - apply_eq?/4: 112, 113
  - conv?/4: 49
  - conv_branch_bodies?/5: 161, 162, 163
  - conv_branches?/4: 153, 155, 156
  - conv_neutral?/4: 135, 136, 139, 146, 147, 150
  - conv_struct?/4: 69, 70, 72, 75, 77, 83, 99, 100, 102
  - eta_eq?/4: 107, 108, 109
  - same_neutral_no_delta?/3: 176, 177, 180, 182
  - same_value_no_delta?/3: 185, 187, 188, 189, 190, 191, 194, 199

## Cure.Core.Eval cold lines

  - as_bool/1: 173
  - eval/2: 26, 36, 37, 56, 57, 61
  - vfst/1: 175, 176
  - vsnd/1: 178, 179

## Cure.Core.Inductive cold lines

  - arg_telescope/2: 225, 226, 227
  - ctor_quantities/2: 234, 235, 236, 237
  - ctor_result_indices/2: 216, 217, 218
  - ctor_result_params/2: 266, 267, 268, 269
  - family?/2: 199
  - gather_data_heads/2: 361, 363, 364
  - index_telescope/2: 244, 245, 246
  - occurs?/2: 373, 374, 375, 376, 377, 378, 379, 380, 381, 384, 388, 389, 391
  - param_telescope/2: 254
  - register_builtin/3: 127, 129, 132
  - strictly_positive?/4: 318, 335

## Cure.Core.Kernel cold lines

  - bind_index/3: 844, 845, 846, 847, 848, 849, 850, 852, 854
  - branch_unify/4: 768, 770, 771, 772
  - check/3: 265, 266, 267, 269, 271, 272, 289, 296, 312
  - check_case_branches/7: 703, 708, 718, 724
  - check_ctor/3: 412, 413, 415, 416, 417, 418, 419, 420
  - check_ctor_args/2: 510, 511, 513, 516
  - check_def/2: 358
  - check_family/2: 395, 397, 398
  - check_field_levels/2: 523
  - check_motive_wf/4: 606
  - check_result_indices/3: 957, 958, 959, 960
  - check_telescope/2: 499, 502, 503, 504
  - check_uniform_params/5: 432, 433, 436, 439, 440, 442
  - ensure_eq/1: 473, 474
  - ensure_pi/1: 466
  - ensure_sigma/1: 469
  - head_key/1: 869, 870, 871, 872
  - infer/2: 44, 58, 60, 67, 95, 104, 110, 111, 117, 118, 120, 121, 123, 124, 125, 147, 148, 150, 166, 181, 237
  - infer_prim/3: 1051
  - infer_sort/2: 459
  - infer_type_value_sort/2: 610, 618, 620, 621, 622, 626, 627, 631, 676, 677, 679, 680, 686
  - normalize/2: 34
  - normalize/3: 38
  - numeric_type?/1: 1055
  - occurs_index?/2: 877, 878, 879, 880
  - reduce_index_pairs/3: 799, 800, 801, 802
  - remap_index_error/2: 557
  - replace_branch_vars/2: 908, 911, 914, 917, 920, 923, 925, 926, 929, 932, 936, 937, 940, 942, 945, 948, 950
  - rigid_index?/1: 858, 859, 860, 861, 862, 863, 864, 865, 866, 867
  - shift_subst/2: 953
  - specialize_branch_context/2: 885, 886, 888, 889, 893, 896
  - specialize_branch_value/3: 905
  - unify_indices/4: 789
  - unify_one/4: 809, 812, 815, 821, 823, 827
  - unify_spine/4: 832, 834, 835, 836, 837, 840

## Cure.Core.Normalise cold lines

  - fuel_key/0: 85
  - id_env/1: 139
  - nf/2: 37
  - nf_neutral/4: 185, 186
  - nf_struct/4: 143, 145, 157, 159, 173, 175
  - normalize_opts/1: 108, 112, 116, 122
  - reduce_unfolded/3: 309, 310, 311, 315, 316, 317
  - spend_fuel/1: 335
  - unfold_certified_head/3: 260, 261, 262, 266, 267, 268
  - whnf_value/3: 54
  - with_fuel/2: 77

## Cure.Core.Quote cold lines

  - reify/1: 21
  - reify/2: 49, 51
  - reify_neutral/2: 68, 69

## Cure.Core.Serialize cold lines

  - build/1: 133, 134, 135, 136, 139
  - build_all/1: 203
  - build_branches/1: 213, 216
  - build_node/2: 141, 144, 145, 148, 149, 154, 156, 157, 158, 161, 166, 191
  - decode/1: 75, 76
  - enc/1: 29, 30, 32, 33, 34, 35, 36, 37
  - parse/1: 122, 123
  - parse_list/2: 126
  - str/1: 63
  - take_atom/2: 106
  - take_string/2: 98, 99, 100, 101
  - tokenize/2: 87, 88, 89
  - unary/2: 193
