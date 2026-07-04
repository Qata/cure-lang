# Kernel Coverage

| Module | Covered | Total | % |
|---|---:|---:|---:|
| Cure.Core.Certificate | 186 | 192 | 96.9 |
| Cure.Core.Conv | 66 | 66 | 100.0 |
| Cure.Core.Eval | 65 | 65 | 100.0 |
| Cure.Core.Inductive | 57 | 79 | 72.2 |
| Cure.Core.Kernel | 320 | 340 | 94.1 |
| Cure.Core.Normalise | 87 | 103 | 84.5 |
| Cure.Core.Quote | 34 | 37 | 91.9 |
| Cure.Core.Serialize | 108 | 108 | 100.0 |

## Cold lines

## Cure.Core.Certificate cold lines

  - arg_relation/2: 295
  - arity_of/1: 443
  - callees_env/2: 409
  - function_edges/3: 450
  - reaches?/4: 536
  - shift_term/2: 575

## Cure.Core.Conv cold lines


## Cure.Core.Eval cold lines


## Cure.Core.Inductive cold lines

  - arg_telescope/2: 225, 226, 227
  - ctor_quantities/2: 234, 235, 236, 237
  - ctor_result_indices/2: 216, 217, 218
  - ctor_result_params/2: 266, 267, 268, 269
  - family?/2: 199
  - index_telescope/2: 244, 245, 246
  - param_telescope/2: 254
  - register_builtin/3: 127, 129, 132

## Cure.Core.Kernel cold lines

  - bind_index/4: 862
  - check/3: 289, 296, 312
  - check_def/2: 358
  - check_motive_wf/4: 607
  - head_key/1: 907
  - infer/2: 67
  - infer_type_value_sort/2: 619, 621, 622, 623, 632, 690
  - normalize/2: 34
  - normalize/3: 38
  - remap_index_error/2: 558
  - replace_branch_vars/2: 980
  - unify_spine/4: 841, 844

## Cure.Core.Normalise cold lines

  - fuel_key/0: 85
  - nf/2: 37
  - normalize_opts/1: 108, 112, 116, 122
  - reduce_unfolded/3: 309, 310, 311, 315, 316, 317
  - spend_fuel/1: 335
  - unfold_certified_head/3: 261, 267
  - with_fuel/2: 77

## Cure.Core.Quote cold lines

  - split_data_args/3: 93, 94, 95

## Cure.Core.Serialize cold lines

