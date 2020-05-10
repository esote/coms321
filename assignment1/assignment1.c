#include <stdint.h>
#include <stdio.h>

void
builder(uint64_t *array, int length)
{
	int i;

	for (i = 0; i < length; i++) {
		array[i] = length - i;
	}
}

// Could use XOR alg
void
swap(uint64_t *array, int i, int j)
{
	uint64_t tmp;
	tmp = array[i];
	array[i] = array[j];
	array[j] = tmp;
}

int
smallest(uint64_t *array, int start, int stop) {
	int smallest;
	int i;

	smallest = start;

	for (i = start; i < stop; i++) {
		if (array[i] < array[smallest]) {
			smallest = i;
		}
	}

	return smallest;
}

void
selection_sort(uint64_t *array, int length)
{
	int i, j;

	for (i = 0; i < length; i++) {
		j = smallest(array, i, length);
		swap(array, i, j);
	}
}

uint64_t
binary_search_iterative(uint64_t *array, uint64_t x, int i, int j)
{
	int k;

	while (i <= j) {
		k = (i + j) / 2;

		if (array[k] == x) {
			return k;
		} else if (array[k] < x) {
			i = k + 1;
		} else {
			j = k - 1;
		}
	}

	return -1;
}

uint64_t
binary_search_recursive(uint64_t *array, uint64_t x, int i, int j)
{
	int k;

	if (j < i) {
		return -1;
	}

	k = (i + j) / 2;

	if (array[k] == x) {
		return k;
	} else if (array[k] < x) {
		return binary_search_recursive(array, x, k + 1, j);
	} else {
		return binary_search_recursive(array, x, i, k - 1);
	}
}

#define LEN 64

int
main(void)
{
	uint64_t array[LEN];
	uint64_t iterative, recursive;

	builder(array, LEN);
	selection_sort(array, LEN);
	iterative = binary_search_iterative(array, 34, 0, LEN - 1);
	recursive = binary_search_recursive(array, 34, 0, LEN - 1);
	// mem offset 0 = iterative - recursive
}
