#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
//#include <limits.h>

typedef uintptr_t mp_limb_t;
typedef mp_limb_t *mp_ptr;
typedef const mp_limb_t *mp_srcptr;
typedef size_t mp_size_t;

#define GMP_NUMB_BITS (sizeof(mp_limb_t) * CHAR_BIT)
#define GMP_NUMB_MASK (~(mp_limb_t)0)

#define ASSERT(expr) if (!(expr)) { fprintf(stderr, "Assertion failed: %s\n", #expr); exit(1); }

#define MPN_SAME_OR_INCR_P(dst, src, size) \
  ((dst) <= (src) || !MPN_OVERLAP_P(dst, size, src, size))

#define MPN_OVERLAP_P(xp, xsize, yp, ysize) \
  ((xp) + (xsize) > (yp) && (yp) + (ysize) > (xp))

// Define __mpz_struct similar to GMP
typedef struct {
  mp_size_t _mp_alloc;  // Allocated size (number of limbs allocated)
  mp_size_t _mp_size;   // Used size (number of limbs currently in use)
  mp_limb_t *_mp_d;     // Pointer to the array of limbs
} __mpz_struct;

// Function to initialize an __mpz_struct
void mpz_init(__mpz_struct *z, mp_size_t alloc_size) {
  z->_mp_alloc = alloc_size;
  z->_mp_size = 0;
  z->_mp_d = (mp_limb_t *)malloc(alloc_size * sizeof(mp_limb_t));
  if (z->_mp_d == NULL) {
    fprintf(stderr, "Memory allocation failed\n");
    exit(1);
  }
}

// Function to free an __mpz_struct
void mpz_clear(__mpz_struct *z) {
  free(z->_mp_d);
  z->_mp_d = NULL;
  z->_mp_alloc = 0;
  z->_mp_size = 0;
}

// mpn_add_n function to add two arrays of limbs
mp_limb_t
mpn_add_n(mp_ptr rp, mp_srcptr up, mp_srcptr vp, mp_size_t n)
{
  mp_limb_t ul, vl, sl, rl, cy, cy1, cy2;

  ASSERT(n >= 1);
  ASSERT(MPN_SAME_OR_INCR_P(rp, up, n));
  ASSERT(MPN_SAME_OR_INCR_P(rp, vp, n));

  cy = 0;
  do
  {
    ul = *up++;
    vl = *vp++;
    sl = ul + vl;          // Sum of the two limbs
    cy1 = sl < ul;         // Carry from the addition of ul and vl
    rl = sl + cy;          // Add the previous carry
    cy2 = rl < sl;         // Carry from the addition of sl and cy
    cy = cy1 | cy2;        // Combine the two carry flags
    *rp++ = rl;            // Store the result limb
  } while (--n != 0);

  return cy;               // Return the final carry
}

// Function in the style of mpz_add
void mpz_add(__mpz_struct *result, const __mpz_struct *a, const __mpz_struct *b) {
  // Determine the size of the result
  mp_size_t max_size = (a->_mp_size > b->_mp_size) ? a->_mp_size : b->_mp_size;

  // Ensure the result has enough allocated space
  if (result->_mp_alloc < max_size + 1) {
    result->_mp_d = (mp_limb_t *)realloc(result->_mp_d, (max_size + 1) * sizeof(mp_limb_t));
    if (result->_mp_d == NULL) {
      fprintf(stderr, "Memory allocation failed\n");
      exit(1);
    }
    result->_mp_alloc = max_size + 1;
  }

  // Perform addition using mpn_add_n
  mp_limb_t carry = mpn_add_n(result->_mp_d, a->_mp_d, b->_mp_d, max_size);

  // Handle carry
  result->_mp_size = max_size;
  if (carry) {
    result->_mp_d[max_size] = carry;
    result->_mp_size++;
  }
}

// Function to print a limb array with a label (decimal and hexadecimal)
void print_limb_array(const char *label, const mp_limb_t *array, mp_size_t size)
{
  printf("%s:\n", label);
  printf("Decimal: ");
  for (mp_size_t i = 0; i < size; i++)
  {
    printf("%lu ", array[i]);
  }
  printf("\nHexadecimal: ");
  for (mp_size_t i = 0; i < size; i++)
  {
    printf("0x%lX ", array[i]);
  }
  printf("\n");
}


int main(void)
{
  // Initialize operands
  __mpz_struct a, b, result;
  mpz_init(&a, 3);
  mpz_init(&b, 3);
  mpz_init(&result, 4); // Allocate space for potential carry

  // Set values for a and b
  a._mp_size = 3;
  a._mp_d[0] = 0xFFFFFFFFFFFFFFFF;
  a._mp_d[1] = 0xFFFFFFFFFFFFFFFF;
  a._mp_d[2] = 0x1;

  b._mp_size = 3;
  b._mp_d[0] = 0x1;
  b._mp_d[1] = 0x0;
  b._mp_d[2] = 0xFFFFFFFFFFFFFFFF;

  // Perform addition
  mpz_add(&result, &a, &b);

  print_limb_array("Operand a", a._mp_d, a._mp_size);
  print_limb_array("Operand b", b._mp_d, b._mp_size);
  // Print the result
  print_limb_array("Result a+b", result._mp_d, result._mp_size);

  // Free allocated memory
  mpz_clear(&a);
  mpz_clear(&b);
  mpz_clear(&result);

  return 0;
}