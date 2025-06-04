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
void mpz_add(mp_limb_t **result, mp_size_t *result_size, const mp_limb_t *a, mp_size_t a_size, const mp_limb_t *b, mp_size_t b_size)
{
  // Determine the size of the result
  mp_size_t max_size = (a_size > b_size) ? a_size : b_size;
  *result_size = max_size;

  // Allocate memory for the result
  *result = (mp_limb_t *)malloc((max_size + 1) * sizeof(mp_limb_t)); // +1 for potential carry
  if (*result == NULL)
  {
    fprintf(stderr, "Memory allocation failed\n");
    exit(1);
  }

  // Perform addition using mpn_add_n
  mp_limb_t carry = mpn_add_n(*result, a, b, max_size);

  // Handle carry
  if (carry)
  {
    (*result)[max_size] = carry;
    (*result_size)++;
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
  // Example operands with values that will cause carry propagation across limbs
  mp_size_t a_size = 3, b_size = 3;
  mp_limb_t a[] = {0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0x1}; // Large values to trigger carry
  mp_limb_t b[] = {0x1, 0x0, 0xFFFFFFFFFFFFFFFF}; // Values to propagate carry

  // Result variables
  mp_limb_t *result = NULL;
  mp_size_t result_size = 0;

  // Print input arrays
  print_limb_array("Operand a", a, a_size);
  print_limb_array("Operand b", b, b_size);

  // Call mpz_add
  mpz_add(&result, &result_size, a, a_size, b, b_size);

  // Print the result
  print_limb_array("Result a+b", result, result_size);

  // Free allocated memory
  free(result);

  return 0;
}