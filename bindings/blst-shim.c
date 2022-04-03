#include <lean/lean.h>

#include <blst.h>

/**
 * Unwrap an Option of an external object as data for some
 * or NULL for none. Unsafe.
 */
static inline void *lean_option_unwrap(b_lean_obj_arg a) {
  if (lean_is_scalar(a)) {
    return NULL;
  } else {
    lean_object *some_val = lean_ctor_get(a, 0);
    return lean_get_external_data(some_val);      
  }
}

/**
 * Option.some a
 */
static inline lean_object * lean_mk_option_some(lean_object * a) {
  lean_object* tuple = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(tuple, 0, a);
  return tuple;
}

/**
 * Option.none.
 * Note that this is the same value for Unit and other constant constructors of inductives.
 */
static inline lean_object * lean_mk_option_none() {
  return lean_box(0);
}

static inline lean_object * lean_mk_tuple2(lean_object * a, lean_object * b) {
  lean_object* tuple = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(tuple, 0, a);
  lean_ctor_set(tuple, 1, b);
  return tuple;
}



static inline lean_obj_res lean_exclusive_or_copy(lean_obj_arg a, lean_obj_res (*copy_fun)(lean_obj_arg)) {
  if (lean_is_exclusive(a))
    return a;
  return copy_fun(a);
}

inline static void noop_foreach(void *mod, b_lean_obj_arg fn) {}

// SDL_Window

static lean_external_class *g_blst_scalar_class = NULL;

static void blst_scalar_finalizer(void *ptr) { 
  free(ptr);
}

static lean_external_class *get_blst_scalar_class() {
  if (g_blst_scalar_class == NULL) {
    g_blst_scalar_class = lean_register_external_class(
        &blst_scalar_finalizer, &noop_foreach);
  }
  return g_blst_scalar_class;
}

static inline const uint32_t* lean_extract_const(lean_obj_arg a, size_t expected_size) {
  size_t size = lean_array_size(a);
  assert(size == expected_size);
  lean_object* ptr = lean_array_cptr(a);
  uint32_t* out = (uint32_t*) malloc(sizeof(uint32_t)*size);
  for (int i = 0; i < size; ++i) {
    out[i] = (uint32_t) lean_unbox_uint32(&ptr[i]);
  }
  return out;
}

/*
constant fromUInt32 (a : { arr : Array UInt32 // arr.size = 8 }) : Scalar
*/
lean_obj_res lean_blst_scalar_from_uint32(lean_obj_arg a) {
  blst_scalar *out = (blst_scalar*) malloc(sizeof(blst_scalar));
  blst_scalar_from_uint32(out, lean_extract_const(a, 8));
  lean_object *lean_w = lean_alloc_external(get_blst_scalar_class(), out);
  return lean_io_result_mk_ok(lean_w);
}


